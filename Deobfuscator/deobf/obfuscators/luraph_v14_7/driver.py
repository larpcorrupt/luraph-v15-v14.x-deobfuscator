"""
Luraph v14.7 pipeline (see LURAPH.md).

The protected script runs in the fake environment with every VM closure
instrumented (patch_entries). Checks that cannot be emulated exactly end in
a trap that corrupts the bytecode; the runtime reports which function made
that call and the script runs again with that function turned into a no-op.
Loadstring'd VM chunks are instrumented the same way and passed back.
Then the captured protos are lifted (devirt.py), with constant rounds for
code that never ran.
"""
import json
import os
import re
import sys
import time
from pathlib import Path

import harness
import traceout as trace

HERE = os.path.dirname(os.path.abspath(__file__))
MAX_RERUNS = 12
SPIN_CHECKS = 24    # watchdog checks (2^20 VM steps each) without environment access = endless loop


def patch_spin(src):
    """Spin watchdog (envlog's --cfg spin): every VM dispatch loop head counts
    steps in __SPIN.n and calls __SPIN.f() every __SPIN.step of them. Table
    operations only, plus that rare call (no locals: see patch_entries)."""
    return re.sub(r"while true do (?:local )?[A-Za-z_]+(?:,[A-Za-z_]+)*=\s*\(?[A-Za-z_]+\[[A-Za-z_]+\]\)?;",
                  lambda m: m.group(0) + "__SPIN.n=__SPIN.n+1;if __SPIN.n>=__SPIN.step then __SPIN.f()end;", src)


def patch_chunk(src, tmpdir):
    """Instrument a loadstring'd VM chunk like the main script."""
    path = os.path.join(tmpdir, "_chunk_%s.luau" % harness.chunk_key(src))
    with open(path, "w", encoding="latin-1", newline="") as f:
        f.write(src)
    try:
        return patch_entries(src, path)
    except Exception as e:  # not parseable by luau-ast: run it as is
        print("[!] could not instrument chunk (%s)" % e, file=sys.stderr)
        return src
    finally:
        os.remove(path)


def patch_entries(source, path):
    """Give every VM closure an entry hook. It only uses table operations (no
    calls, no locals), so the stack looks exactly as it would without it: it numbers
    protos in first-entry order, logs recent entries and returns early for the
    protos listed in __SKIPP."""
    from obfuscators.luraph_v14_7 import vmmap
    root = vmmap.load_ast(path)
    lines = source.split("\n")
    edits = []
    for l1, c1, pv in vmmap.closure_entries(root):
        # no locals: they would enlarge every VM frame, and Luraph mixes the
        # depth its stack-overflow probe reaches into its decryption keys.
        # __PLAST[pid] = entry number of the latest entry of that proto (it
        # tells invocations apart when statements are attributed to protos)
        k = "(%s or __PID)" % pv
        edits.append((l1, c1, ("if not __PID[{k}] then __PID.n=__PID.n+1;__PID[{k}]=__PID.n;end;"
                               "__ENT.n=__ENT.n+1;__ENT[__ENT.n%64]=__PID[{k}];__PLAST[__PID[{k}]]=__ENT.n;"
                               "if __SKIPP[__PID[{k}]] then return end;").format(k=k)))
    # closure -> proto, recorded where the closure is made (not per call), so
    # the runtime can map the functions on the Lua stack back to protos
    tag = harness.chunk_key(source)
    makers = vmmap.maker_info(root)
    if os.environ.get("DEVIRT_DEBUG"):
        print("[*] v14.x mapper: %d dispatcher(s), %d entry hook(s), %d maker(s)" %
              (len(vmmap.find_dispatchers(root)), len(vmmap.closure_entries(root)), len(makers)), file=sys.stderr)
    if not makers:
        print("[!] v14.x mapper found dispatch code but no closure makers; devirtualization capture may be incomplete",
              file=sys.stderr)
    for info in makers:
        (l2, c2), var, pv = info["at"], info["var"], info["proto"]
        code = " __PF[%s]=%s " % (var, info.get("pf_key", pv))
        # devirtualizer capture: once per proto, the maker-level values the VM
        # closure uses (operand arrays, constants, helpers). Table operations
        # only, like the entry hook; runs where the closure is made, not per call.
        cap = "".join("__PA[%s].%s=%s;" % (pv, nm, nm) for nm in info["captures"])
        # v14.x factories may close over locals from the surrounding initializer.
        # Capture those too so devirt can reconstruct the maker's parent Scope.
        cap += "".join("__PA[%s].%s=%s;" % (pv, env["field"], env["name"])
                       for env in info.get("outer_env", ()))
        # __PK: one closure per proto, for calls the devirtualizer asks the
        # runtime to evaluate (LPH_ENCSTR-style string decryptors)
        code += ("if __PA and not __PA[%s] then __PA[%s]={};__PA.n=__PA.n+1;__PA[%s].__seq=__PA.n;"
                 "__PA[%s].__maker=\"%s@%d,%d\";__PK[%s]=%s;%s end "
                 % (pv, pv, pv, pv, tag, l2, c2, info.get("pf_key", pv), var, cap))
        edits.append((l2, c2, code))
    for l, c, code in sorted(edits, reverse=True):
        lines[l] = lines[l][:c] + code + lines[l][c:]
    return "\n".join(lines)


def _trace_root_candidates(body):
    """Rank likely payload-root pids from envlog call-chain markers.

    Large v14 scripts enter many helper/probe closures before and after the
    actual chunk. Using the *last* second pid in the stack therefore picks a
    runtime helper surprisingly often. Rank the immediate child of the
    outermost instrumented frame instead: favour a child that accounts for
    many statements in one/few invocations, and strongly penalize children
    that return to an emitting parent (the fingerprint/probe shape).
    """
    scores = {}
    hits = {}
    invs = {}
    last_seen = {}
    last_child = {}
    pos = 0
    for line in body.splitlines():
        m = re.match(r"^\s*--@\d+\s*(.*)$", line)
        if not m:
            continue
        pos += 1
        chain = []
        for part in m.group(1).split(","):
            q = re.match(r"^(\d+):([^,\s]*)", part.strip())
            if q:
                chain.append((int(q.group(1)), q.group(2)))
        if len(chain) >= 2:
            parent, child = chain[0][0], chain[1][0]
            w = 5 + min(3, len(chain) - 2)
            if len(chain) == 2:
                w += 1
            scores[child] = scores.get(child, 0) + w
            hits[child] = hits.get(child, 0) + 1
            invs.setdefault(child, set()).add(chain[1][1])
            last_seen[child] = pos
            last_child[parent] = child
        elif len(chain) == 1:
            parent = chain[0][0]
            child = last_child.get(parent)
            if child is not None:
                scores[child] = scores.get(child, 0) - 18
                last_child.pop(parent, None)

    for pid, xs in invs.items():
        scores[pid] = scores.get(pid, 0) - max(0, len(xs) - 2) * 5

    ranked = sorted(
        scores,
        key=lambda p: (scores[p], hits.get(p, 0), last_seen.get(p, 0)),
        reverse=True,
    )
    return ranked


def _trace_root_hint(body):
    ranked = _trace_root_candidates(body)
    return ranked[0] if ranked else None


def _json_loads_loose(raw):
    """Parse harness JSON even if an interrupted run left trailing commas."""
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        out = []
        i = 0
        quoted = False
        escaped = False
        while i < len(raw):
            ch = raw[i]
            if quoted:
                out.append(ch)
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    quoted = False
                i += 1
                continue
            if ch == '"':
                quoted = True
                out.append(ch)
                i += 1
                continue
            if ch == ",":
                j = i + 1
                while j < len(raw) and raw[j] in " \t\r\n":
                    j += 1
                if j < len(raw) and raw[j] in "}]":
                    i += 1
                    continue
            out.append(ch)
            i += 1
        return json.loads("".join(out))


def _apply_root_hint(protos_json, body):
    """Apply the strongest runtime payload-root hint to the captured dump.

    v14's in-harness root_callee can be stale on large scripts. The weighted
    marker vote is based on the complete rendered run, so let it override that
    stale value and keep a short ranked list for diagnostics/fallbacks.
    """
    ranked = _trace_root_candidates(body)
    hint = ranked[0] if ranked else None
    if hint is None or not protos_json or protos_json.startswith("error:"):
        return protos_json, hint
    try:
        data = _json_loads_loose(protos_json)
    except Exception:
        return protos_json, hint
    protos = data.get("protos", {})
    ranked = [pid for pid in ranked if str(pid) in protos][:8]
    if not ranked:
        return protos_json, hint
    hint = ranked[0]
    old = data.get("root_callee")
    data["root_candidates"] = ranked
    data["root_callee"] = hint
    protos_json = json.dumps(data, separators=(",", ":"))
    if old != hint:
        if old is None:
            print("[*] inferred payload root proto #%d from weighted runtime call chain" % hint, file=sys.stderr)
        else:
            print("[*] corrected payload root proto #%s -> #%d from weighted runtime call chain" % (old, hint), file=sys.stderr)
    elif os.environ.get("DEVIRT_DEBUG"):
        print("[*] payload root proto #%d confirmed by weighted runtime call chain" % hint, file=sys.stderr)
    return protos_json, hint


def _v14_probe_signature_score(code):
    """Score the narrow Roblox anti-analysis fingerprint used by Luraph v14.x.

    This intentionally requires several independent markers so ordinary user
    code that happens to use Path2D or one Roblox signal is not stripped.
    """
    if not code:
        return 0
    score = 0
    if 'Instance.new("ScreenGui")' in code:
        score += 1
    if 'Instance.new("Frame")' in code:
        score += 1
    if 'Instance.new("Path2D")' in code and 'Path2DControlPoint.new' in code:
        score += 3
    curve_calls = len(re.findall(r':Get(?:Position|Tangent)OnCurve(?:ArcLength)?\(', code))
    if curve_calls >= 5:
        score += 3
    if len(re.findall(r'^\s*task\.(?:spawn|delay)\(', code, re.M)) >= 2:
        score += 2
    event_calls = len(re.findall(r'\.(?:DescendantRemoving|ChildRemoved|AncestryChanged):Connect\(function', code))
    if event_calls >= 2:
        score += 3
    # v14.8 in particular also ships an event-only ancestry fingerprint.
    # Requiring several empty-looking AncestryChanged probes keeps this narrow
    # enough not to classify an ordinary user signal connection as scaffolding.
    ancestry_calls = len(re.findall(r'\.AncestryChanged:Connect\(function', code))
    if ancestry_calls >= 4:
        score += 4
    if 'Instance.new("Folder")' in code and re.search(r':WaitForChild\("\d+"\)', code):
        score += 2
    if 'game:GetService("HttpService")' in code and 'game:GetService("RunService")' in code:
        score += 2
    return score


def _strip_v14_probe_suite(code):
    """Remove the compact anti-analysis probe suite from trace recovery.

    This is intentionally narrow and is only used after the static lifter has
    failed.  v14.8/v14.9 run a recognizable temporary Roblox fingerprint:
    empty task callbacks, a throwaway ScreenGui/Path2D tree, immediate
    DescendantRemoving/ChildRemoved/AncestryChanged connect/disconnect pairs and throwaway Folders.  Those
    statements are Luraph runtime scaffolding, not payload source.
    """
    if _v14_probe_signature_score(code) < 8:
        return code

    lines = code.splitlines()
    out = []
    probe_vars = set()
    connection_vars = set()
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Empty task callbacks used by the timing/scheduler fingerprint.
        if re.match(r'^task\.spawn\(function\([^)]*\)\s*$', stripped):
            if i + 1 < len(lines) and lines[i + 1].strip() == "end)":
                i += 2
                continue
        if re.match(r'^task\.delay\([^,]+,\s*function\([^)]*\)\s*$', stripped):
            if i + 1 < len(lines) and lines[i + 1].strip() == "end)":
                i += 2
                continue

        # Temporary objects in the known v14 fingerprint suite.
        m = re.match(r'^local\s+(\w+)\s*=\s*Instance\.new\("(ScreenGui|Frame|Path2D|Folder)"(?:,.*)?\)\s*$', stripped)
        if m:
            probe_vars.add(m.group(1))
            i += 1
            continue

        # Some code generators/minifiers collapse the whole empty callback and
        # disconnect onto one line.  Remove that form too, but only after the
        # suite-level signature gate above has fired.
        m = re.match(
            r'^local\s+(\w+)\s*=\s*(.+?)\.(?:DescendantRemoving|ChildRemoved|AncestryChanged):Connect\(function\([^)]*\)\s*end\)\s*;?\s*\1:Disconnect\(\)\s*$',
            stripped)
        if m:
            connection_vars.add(m.group(1))
            i += 1
            continue

        # Immediate empty Roblox-signal connection + disconnect.
        # AncestryChanged is used by the v14.8 fingerprint on game/workspace,
        # throwaway folders and a couple of services.
        m = re.match(r'^local\s+(\w+)\s*=\s*(.+)\.(?:DescendantRemoving|ChildRemoved|AncestryChanged):Connect\(function\([^)]*\)\s*$', stripped)
        if m and i + 2 < len(lines) and lines[i + 1].strip() == "end)"                 and lines[i + 2].strip() == m.group(1) + ":Disconnect()":
            connection_vars.add(m.group(1))
            i += 3
            continue

        # Any operation whose receiver is one of the throwaway objects.
        recv = re.match(r'^(\w+)(?:\.|:)', stripped)
        if recv and recv.group(1) in probe_vars:
            i += 1
            continue

        out.append(line)
        i += 1

    # Service locals that were only used by removed connection probes are now
    # dead.  Prune them without touching arbitrary user GetService calls.
    code = "\n".join(out)
    for name in re.findall(r'^\s*local\s+(\w+)\s*=\s*game:GetService\("(?:HttpService|RunService)"\)\s*$',
                           code, re.M):
        decl_re = re.compile(r'^\s*local\s+' + re.escape(name)
                             + r'\s*=\s*game:GetService\("(?:HttpService|RunService)"\)\s*$',
                             re.M)
        without_decl = decl_re.sub('', code)
        if not re.search(r'\b' + re.escape(name) + r'\b', without_decl):
            code = decl_re.sub('', code)

    # Remove excess blank runs left by probe deletion.
    code = re.sub(r'\n{3,}', '\n\n', code).strip()
    return code


def _payload_trace_source(body, root_pid):
    """Source-like statements attributed to the final payload invocation.

    v14.x often executes environment probes in an earlier invocation of the
    same proto that later executes the user chunk.  Group by the marker's
    invocation id and keep the latest invocation, then strip the narrowly
    recognized Luraph probe suite.
    """
    if root_pid is None:
        return None
    try:
        import fold
        lines = body.splitlines()
        items = fold.parse(lines, 0, len(lines))
        groups = {}
        order = []

        def visit(xs):
            for it in xs:
                if isinstance(it, fold.Stmt):
                    chain = it.chain
                    if len(chain) >= 2 and chain[1][0] == str(root_pid):
                        inv = chain[1][1] or ""
                        if inv not in groups:
                            groups[inv] = []
                            order.append(inv)
                        groups[inv].extend(fold.render([it]))
                    else:
                        visit(it.items)

        visit(items)
        if not groups:
            return None

        def inv_key(v):
            try:
                return (1, int(v))
            except Exception:
                return (0, order.index(v))

        chosen = max(groups, key=inv_key)
        code = "\n".join(groups[chosen]).strip()
        if not code:
            return None
        code = "\n".join(x for x in code.splitlines() if not x.startswith("\0"))
        code = _strip_v14_probe_suite(code)
        return code.strip() or None
    except Exception:
        return None



def _observable_trace_source(body):
    """Recover compact, directly-observed payload side effects from a v14 trace.

    This is a last-resort semantic recovery path, not a replacement for the VM
    lifter.  It deliberately accepts only calls whose complete arguments were
    observed by envlog (print/warn are the important regression fixtures).  It
    ignores the Luraph/Roblox fingerprint suite and never guesses values.
    """
    try:
        import fold
        items = fold.parse(body.splitlines(), 0, len(body.splitlines()))
        found = []

        def visit(xs):
            for it in xs:
                if isinstance(it, fold.Stmt):
                    block = "\n".join(fold.render([it])).strip()
                    if block:
                        cleaned = _strip_v14_probe_suite(block).strip()
                        # These wrappers record concrete arguments, so returning
                        # them is semantically stronger than a wrong bootstrap lift.
                        if re.match(r'^(?:print|warn)\s*\(', cleaned):
                            found.append(cleaned)
                    visit(it.items)
                elif hasattr(it, "items"):
                    visit(it.items)

        visit(items)
        # Preserve order but suppress duplicate observations caused by helper
        # folding / repeated marker nesting.
        out = []
        for x in found:
            if not out or out[-1] != x:
                out.append(x)
        if not out or len(out) > 32:
            return None
        code = "\n".join(out).strip()
        return code if len(code.encode("utf-8", "replace")) <= 8192 else None
    except Exception:
        return None


def _v14_scaffold_score(text):
    """How strongly a static result still resembles the Luraph VM/runtime.

    These markers should never dominate real deobfuscated source.  Keep this
    deliberately structural; user scripts may have a variable called state or
    handlers, but they will not also contain our caller-register placeholders
    and dozens of unresolved Luraph helper calls.
    """
    if not text:
        return 10 ** 6
    score = 0
    caller_regs = text.count("the caller's registers")
    runtime = text.count("luraph_runtime")
    handlers = text.count("handlers[")
    state_branches = len(re.findall(r"\\b(?:if|elseif)\\s+state\\s*==", text))
    dense_table = len(re.findall(r"^\\s*\\[\\d+\\]\\s*=", text, re.M))
    score += min(80, caller_regs * 5)
    score += min(18, runtime)
    score += min(40, handlers * 2)
    score += min(30, state_branches // 3)
    if dense_table >= 200:
        score += 30
    if "local ... = ..." in text:
        score += 40
    if ("unresolved Luraph runtime helper" in text and runtime >= 6 and
            (caller_regs or handlers or state_branches >= 6 or dense_table >= 200)):
        score += 20
    return score


def _looks_like_v14_scaffolding(text):
    return _v14_scaffold_score(text) >= 24


def _dump_root_candidates(ppath):
    try:
        data = _json_loads_loose(Path(ppath).read_text(encoding="utf-8", errors="replace"))
    except Exception:
        return [], None
    protos = data.get("protos", {})
    out = []
    for pid in data.get("root_candidates") or []:
        try:
            n = int(pid)
        except Exception:
            continue
        if str(n) in protos and n not in out:
            out.append(n)
    cur = data.get("root_callee")
    try:
        cur = int(cur) if cur is not None else None
    except Exception:
        cur = None
    if cur is not None and str(cur) in protos and cur not in out:
        out.insert(0, cur)
    return out, cur


def _set_dump_root(ppath, pid):
    try:
        data = _json_loads_loose(Path(ppath).read_text(encoding="utf-8", errors="replace"))
        if str(pid) not in data.get("protos", {}):
            return False
        data["root_callee"] = int(pid)
        Path(ppath).write_text(json.dumps(data, separators=(",", ":")), encoding="utf-8", newline="\\n")
        return True
    except Exception:
        return False

def devirtualize(job, ppath, dpath, cfg, rerun, chunk_paths=(), live=None):
    """Lift the captured protos; constants that only Luraph's lazy decoder can
    produce (code that never ran) are requested from further runs. With a
    live harness (`live()` -> fetch function, while the long-lived harness
    made the current dump) the walks ask for them right away (a chain of
    constants, each needed to find the next, then takes one round instead
    of one round per link)."""
    from obfuscators.luraph_v14_7 import devirt
    args = job.args
    requested = set()
    last_bufs = ""
    text = None
    stats = {"functions": 0, "errors": 0, "fallbacks": 0}
    rounds = args.devirt_rounds
    # Intermediate rounds only need the constant requests and decrypted
    # strings, which come from walking each function: they skip the
    # structuring/codegen/naming and reuse the walks of functions that asked
    # for nothing (devirt.collect_requests). The text comes from one full lift
    # at the fixed point; if that lift still asks for something new, the
    # remaining rounds are full lifts (the old way).
    quick = not os.environ.get("DEVIRT_FULL_ROUNDS")
    cache = devirt.WalkCache()
    t0 = time.time()
    for rnd in range(1, rounds + 1):
        t1 = time.time()
        full = not quick
        if quick:
            stats, reqs, bufs = devirt.run_big_stack(devirt.collect_requests, job.source_path, ppath, chunk_paths, cache,
                                                     live and live())
            new = reqs - requested
            print("[*] devirt round %d: %d functions (%d walked), %d unlifted blocks, %d new constant requests%s "
                  "(%.1fs)" % (rnd, stats["functions"], stats["walked"], stats["errors"], len(new),
                               " (%d decoded live)" % stats["fetched"] if stats.get("fetched") else "",
                               time.time() - t1), file=sys.stderr)
            if os.environ.get("DEVIRT_REQS"):
                for rq in sorted(new):
                    print("[*]     request %s" % rq, file=sys.stderr)
            if not new and stats.get("errors", 0):
                if os.environ.get("DEVIRT_STRICT"):
                    print("[!] v14.x quick walk has %d unresolved VM state(s); strict mode refuses partial output"
                          % stats["errors"], file=sys.stderr)
                    return False
                print("[*] v14.x quick walk has %d unresolved VM state(s); continuing with partial full lift"
                      % stats["errors"], file=sys.stderr)
                full = True
            if (not new and devirt.same_patches(last_bufs, bufs)) or rnd == rounds:
                full = True
        if full:
            print("[*] devirtualizing (round %d)..." % rnd, file=sys.stderr)
            t1 = time.time()
            text, stats, reqs, bufs = devirt.run_big_stack(devirt.lift_program, job.source_path, ppath, chunk_paths,
                                                           live and live())

            # Large v14 scripts may create runtime/helper closures before the
            # actual chunk root.  If the selected root clearly decompiles back
            # into Luraph's own VM, try the next runtime-ranked roots from the
            # *same* proto dump.  No script rerun is needed for this scan.
            raw_text = text or ""
            cleaned_text = _strip_v14_probe_suite(raw_text)
            probe_only = bool(raw_text.strip()) and not cleaned_text.strip() and _v14_probe_signature_score(raw_text) >= 8
            if cleaned_text.strip() and cleaned_text != raw_text:
                text = cleaned_text
            base_score = (10 ** 6) if probe_only else _v14_scaffold_score(text or "")
            candidates, current_root = _dump_root_candidates(ppath)
            if (base_score >= 24 or probe_only) and len(candidates) > 1:
                best = (base_score, text, stats, reqs, bufs, current_root)
                reason = "anti-tamper probe-only root" if probe_only else "VM/bootstrap scaffolding"
                print("[!] selected v14 root is %s (score %d); scanning alternate roots"
                      % (reason, base_score), file=sys.stderr)
                tried = 0
                scan_limit = 8 if probe_only else 4
                for pid in candidates:
                    if pid == current_root or tried >= scan_limit:
                        continue
                    tried += 1
                    if not _set_dump_root(ppath, pid):
                        continue
                    at0 = time.time()
                    try:
                        atext, astats, areqs, abufs = devirt.run_big_stack(
                            devirt.lift_program, job.source_path, ppath, chunk_paths, live and live())
                    except Exception as ex:
                        if os.environ.get("DEVIRT_DEBUG"):
                            print("[*]   root #%d rejected: %s" % (pid, ex), file=sys.stderr)
                        continue
                    araw = atext or ""
                    aclean = _strip_v14_probe_suite(araw)
                    aprobe_only = bool(araw.strip()) and not aclean.strip() and _v14_probe_signature_score(araw) >= 8
                    if aclean.strip() and aclean != araw:
                        atext = aclean
                    ascore = (10 ** 6) if aprobe_only else _v14_scaffold_score(atext or "")
                    label = "probe-only" if aprobe_only else "candidate"
                    print("[*]   root #%d: %s score %d, %d unlifted block(s) (%.1fs)"
                          % (pid, label, ascore, astats.get("errors", 0), time.time() - at0), file=sys.stderr)
                    # Scaffolding/probe score is the primary signal.  On a tie
                    # prefer the candidate with fewer unresolved VM states.
                    if (ascore, astats.get("errors", 0)) < (best[0], best[2].get("errors", 0)):
                        best = (ascore, atext, astats, areqs, abufs, pid)
                    if ascore < 24 and astats.get("errors", 0) == 0:
                        break
                _, text, stats, reqs, bufs, chosen_root = best
                if chosen_root is not None:
                    _set_dump_root(ppath, chosen_root)
                if best[0] < base_score:
                    print("[*] selected alternate payload root #%s (score %d -> %d)"
                          % (chosen_root, base_score, best[0]), file=sys.stderr)

            new = reqs - requested
            print("[*]   %d functions, %d unlifted blocks, %d unstructured jumps, %d new constant requests (%.1fs)"
                  % (stats["functions"], stats["errors"], stats["fallbacks"], len(new), time.time() - t1),
                  file=sys.stderr)
            if (not new and devirt.same_patches(last_bufs, bufs)) or rnd == rounds:
                break
            if quick:
                print("[*]   the full lift needs more constants: continuing with full lifts", file=sys.stderr)
                quick = False
        requested |= reqs
        last_bufs = bufs
        c = dict(cfg)
        c["force_req"] = ";".join(sorted(requested))
        # strings decrypted in place by lifted code the runtime never ran
        c["force_buf"] = bufs
        t1 = time.time()
        body, err = rerun(c)
        if os.environ.get("DEVIRT_TIMING"):
            print("[*]   constant run %.1fs (total %.0fs)" % (time.time() - t1, time.time() - t0), file=sys.stderr)
        if body is None:
            print("[!] constant request run failed: " + err[-500:], file=sys.stderr)
            break
        m = re.search(r"\x00PROTOS ([^\n]*)\n", body)
        if not m or m.group(1).startswith("error:"):
            print("[!] constant request run gave no protos", file=sys.stderr)
            break
        with open(ppath, "w", encoding="utf-8", newline="\n") as f:
            f.write(m.group(1))
    if text is None:
        print("[*] constant recovery stopped before a full lift; attempting best-effort partial lift",
              file=sys.stderr)
        try:
            text, stats, _, _ = devirt.run_big_stack(
                devirt.lift_program, job.source_path, ppath, chunk_paths, None)
        except Exception as ex:
            print("[!] best-effort partial lift failed: %s: %s" % (type(ex).__name__, ex),
                  file=sys.stderr)

    finished = devirt.finish_text(text or "").strip()
    # The selected proto may be the v14 Roblox anti-analysis fingerprint.
    # Strip only the strongly-recognized probe suite; if nothing remains, this
    # was not the payload root and must not be accepted as deobfuscated source.
    finished = _strip_v14_probe_suite(finished).strip()
    # Avoid duplicate/stale credit headers when the same output path is reused.
    finished = re.sub(r"^(?:-- Devirtualized with Luraph v14\.[789] engine\s*)+", "", finished).lstrip()
    if not finished:
        print("[!] v14.x lifter captured no liftable VM functions; falling back to the behavior trace",
              file=sys.stderr)
        return False
    if _looks_like_v14_scaffolding(finished):
        print("[!] refusing v14 static output: selected root is still Luraph VM/bootstrap scaffolding",
              file=sys.stderr)
        return False
    unresolved = stats.get("errors", 0) if isinstance(stats, dict) else 0
    if unresolved:
        finished = ("-- PARTIAL RECOVERY: %d unresolved VM state(s) remain\n"
                    "-- Recovered regions below are static devirtualization output; unresolved paths were not guessed.\n\n"
                    % unresolved) + finished
    header = job.credit_header()
    job.write(dpath, header + finished + "\n")
    return True


def run(job):
    """The whole Luraph pipeline; returns the result file's path."""
    args = job.args
    devirt_on = not args.no_devirt
    source = job.source
    try:
        patched = source if args.no_hooks else patch_entries(source, job.source_path)
    except SyntaxError as e:
        sys.exit("[!] the input is %s: the file is damaged (truncated, or mangled by a paste/upload); "
                 "nothing to run" % e)
    cache_path = harness.load_p2d_cache(job.input, args.studio)
    runner = harness.Runner(job)
    bridge = runner.bridge

    skip = []
    # spin watchdog from the first run: a script ending in a pure-VM endless
    # loop (tamper response, wait for remote code) then stops after a few
    # seconds instead of running into the timeout. DEOB_SPIN_LATE=1: only
    # after a timeout (the old way)
    spin = not os.environ.get("DEOB_SPIN_LATE")
    if spin:
        patched = patch_spin(patched)
    chunks = {}
    raw_chunks = {}     # key -> original source of a loadstring'd VM chunk (for devirt)
    body = None
    trapped = None      # (body, raw output) of the run that hit the last trap
    cfg = None
    lenient_alloc = False
    for attempt in range(1, args.max_runs + 1):
        # (same keys as harness.base_cfg, in the order the harness always had)
        cfg = {"time_budget": args.budget, "dump_strings": args.strings, "executor": args.executor,
               "skip_protos": skip}
        if args.input_text is not None:
            cfg["input_text"] = args.input_text
        if args.no_fold:
            cfg["fold"] = False
        if devirt_on:
            cfg["devirt"] = True
        if lenient_alloc:
            cfg["v14_lenient_create"] = True
        harness.user_cfg(args, cfg)
        if spin:
            cfg["spin"] = SPIN_CHECKS
        print("[*] tracing %s (run %d)..." % (job.input, attempt), file=sys.stderr)
        body, err = runner.run(patched, cfg, chunks)
        if body is None and not spin and err.startswith("timed out") and not bridge:
            # stuck in the script's own code (no environment access, so the
            # runtime never regains control): rerun with a spin watchdog
            print("[*] the script never finished; re-running with a spin watchdog", file=sys.stderr)
            spin = True
            patched = patch_spin(patched)
            chunks = {k: patch_spin(v) for k, v in chunks.items()}
            cfg["spin"] = SPIN_CHECKS
            body, err = runner.run(patched, cfg, chunks)
        if body is None:
            harness.save_raw(args.raw)
            runner.finish()
            sys.exit("[!] " + err)
        body = harness.take_p2d(body, cache_path, bridge is not None)
        found, body = harness.take_chunks(body)
        added = 0
        for key, src in found:
            if key not in chunks and args.no_hooks:
                chunks[key] = src
            elif key not in chunks:
                raw_chunks[key] = src
                chunks[key] = patch_chunk(src, job.outdir)
                if spin:
                    chunks[key] = patch_spin(chunks[key])
                added += 1
        if added:
            print("[*] script loadstring'd %d new VM chunk(s); instrumenting and re-running" % added, file=sys.stderr)
            continue
        trig = re.search(r"\x00TRIGGER (\d+)", body)
        if trapped is not None and trace.stmt_count(body) < trace.stmt_count(trapped[0]):
            # disabling that function made the script stop earlier: the trap
            # is the script's own check (e.g. LPH_CRASH() after a failed
            # license check), not an environment divergence. Keep that run.
            print("[*] disabling function #%d made the script stop earlier: it is the script's own "
                  "crash check; keeping run %d" % (skip[-1], attempt - 1), file=sys.stderr)
            body, harness.LAST_RAW[0] = trapped
            skip.pop()
            break
        if not trig:
            # Some v14.8/v14.9 fingerprints derive an invalid allocation size
            # when one Roblox-only probe differs from the standalone runtime.
            # Retry once with recovery-only create wrappers.  Native behavior
            # remains the first run and every normal-size allocation remains
            # native even in the recovery run.
            if (os.environ.get("DEOB_V14_LENIENT_ALLOC")
                    and not lenient_alloc and attempt < args.max_runs
                    and "size out of range" in body
                    and "script error:" in body):
                print("[*] v14.x allocation fingerprint diverged; re-running once with lenient probe allocations",
                      file=sys.stderr)
                lenient_alloc = True
                continue
            if (not lenient_alloc and "size out of range" in body and "script error:" in body):
                print("[*] v14.x allocation fingerprint diverged; keeping the first trace (lenient retry disabled for speed)",
                      file=sys.stderr)
            break
        trapped = (body, harness.LAST_RAW[0])
        pid = int(trig.group(1))
        if pid in skip:
            print("[!] anti-tamper trigger %d fired again; giving up on reruns" % pid, file=sys.stderr)
            break
        print("[*] anti-tamper trap reached through function #%d; disabling it and re-running" % pid,
              file=sys.stderr)
        skip.append(pid)

    run_text = harness.trace_text(body)     # the run the constant rounds must repeat
    body = harness.p2d_miss(body, cache_path)
    if not devirt_on:
        runner.finish()
    harness.save_raw(args.raw)
    body = re.sub(r"\x00TRIGGER \d+\n?", "", body)
    protos_json, body = trace.take_line(body, "PROTOS")
    protos_json, root_hint = _apply_root_hint(protos_json, body)
    force, body = trace.take_line(body, "FORCE")
    if force is not None and devirt_on:
        print("[*] constants decoded on request: " + force, file=sys.stderr)
    unscrambled, body = trace.take_line(body, "UNSCRAMBLED")
    if unscrambled is not None and devirt_on:
        print("[*] %s function(s) scrambled by the script's LPH_CRASH(): dumped as they were "
              "when first created" % unscrambled, file=sys.stderr)
    body, strings = trace.take_strings(body)

    notes = ["anti-tamper trap functions disabled: %s" % ", ".join("#%d" % p for p in skip)] if skip else []
    text = trace.header(job.input, notes) + body

    def write_trace():
        job.write(job.trace_path, trace.render(text, args))

    def semantic_trace_candidate():
        """Return compact payload source when the static v14 lift cannot finish.

        Prefer statements whose runtime proto chain identifies the payload root.
        This avoids turning dozens/hundreds of environment-probe statements into
        the recovery result for a one-line script.  Only when no attribution is
        available do we fall back to the old tiny-trace heuristic.
        """
        attributed = _payload_trace_source(body, root_hint)
        observable = _observable_trace_source(body)
        if attributed is not None:
            rendered = attributed
            # Root attribution in v14 can still point at the bootstrap invocation.
            # If that produces a large block while envlog directly observed only
            # a tiny set of concrete print/warn calls, prefer the observed calls.
            if observable is not None:
                ac = len([ln for ln in rendered.splitlines() if ln.strip() and not ln.lstrip().startswith("--")])
                oc = len([ln for ln in observable.splitlines() if ln.strip() and not ln.lstrip().startswith("--")])
                if ac > max(12, oc * 6):
                    rendered = observable
        elif observable is not None:
            rendered = observable
        else:
            try:
                if trace.stmt_count(body) > 24:
                    return None
                rendered = trace.render(text, args)
            except Exception:
                return None
        bad = (
            "[envlog]", "loadstring() of", "repeat forever",
            "stopped in an endless loop", "script error:",
            "removed at so its gonna be shit",
        )
        low = rendered.lower()
        if any(x.lower() in low for x in bad):
            return None
        lines = rendered.splitlines()
        # trace.header() is a leading comment block.  Strip only that prefix;
        # keep comments that belong to the recovered payload itself.
        while lines and (not lines[0].strip() or lines[0].lstrip().startswith("--")):
            lines.pop(0)
        candidate = "\n".join(lines).strip()
        if not candidate or len(candidate.encode("utf-8", "replace")) > 12000:
            return None
        code_lines = [ln for ln in lines if ln.strip() and not ln.lstrip().startswith("--")]
        if not code_lines or len(code_lines) > 80:
            return None
        return candidate + "\n"

    def write_semantic_candidate(candidate):
        spath = job.path(".semantic.luau")
        job.write(spath, job.credit_header() + candidate)
        print("[*] static v14 lift resolved to bootstrap/runtime scaffolding; "
              "using compact trace-assisted payload reconstruction", file=sys.stderr)
        return spath

    def write_recovered_loadstring():
        """Return the deepest runtime-intercepted loadstring body as source.

        The runtime trace is diagnostic output, not deobfuscated source.  When
        Luraph hands execution to a loadstring payload and the VM lifter later
        fails, that intercepted payload is a strictly better recovery result
        than a statement-by-statement envlog trace (which may just follow a
        decoy/endless-loop path).
        """
        if not raw_chunks:
            return None

        # Dicts preserve insertion order.  The newest chunk is normally the
        # deepest stage reached by nested loadstring calls.  Walk backwards so
        # empty/whitespace-only chunks do not win.
        for key, src in reversed(list(raw_chunks.items())):
            if not isinstance(src, str) or not src.strip():
                continue
            rpath = job.path(".loadstring_recovered.lua")
            banner = (
                "-- Recovered from runtime-intercepted loadstring()\n"
                "-- source: %s | chunk: %s | bytes: %d\n\n"
                % (job.input, key, len(src.encode("latin-1", errors="replace")))
            )
            job.write(rpath, banner + src, encoding="latin-1")
            print(
                "[*] using intercepted loadstring payload as recovery output "
                "(%d bytes, chunk %s)" % (len(src.encode("latin-1", errors="replace")), key),
                file=sys.stderr,
            )
            return rpath
        return None

    # the trace is the result only without devirtualization or when lifting
    # fails: otherwise skip its readability pass (minutes on a 250k-statement trace)
    if not (devirt_on and not job.debug):
        write_trace()
    if strings is not None:
        job.write(job.path(".strings.txt"), strings)
    dpath = job.path(".devirt.luau")
    # Never let a rejected/partial result from an earlier invocation win this run.
    try:
        os.remove(dpath)
    except FileNotFoundError:
        pass
    if protos_json is not None:
        ppath = job.path(".protos.json")
        if protos_json.startswith("error:"):
            print("[!] proto capture failed: " + protos_json, file=sys.stderr)
        else:
            job.write(ppath, protos_json)
            if devirt_on:
                # the lifter needs the original source of every VM chunk
                chunk_paths = [job.write(job.path(".chunk_%s.luau" % key), src, encoding="latin-1")
                               for key, src in raw_chunks.items()]
                lift(job, runner, patched, cfg, chunks, run_text, ppath, dpath, chunk_paths)
    runner.finish()
    trace.status_line(body)
    semantic = semantic_trace_candidate() if devirt_on else None
    if devirt_on and os.path.exists(dpath):
        # A lift full of calls to nil means the VM was misread.  Prefer a
        # directly intercepted loadstring body over the behavior trace.
        with open(dpath, encoding="utf-8", errors="replace") as f:
            lifted = f.read()

        if _looks_like_v14_scaffolding(lifted):
            print("[!] rejected devirtualized output because it still contains Luraph VM/bootstrap scaffolding",
                  file=sys.stderr)
            if not job.debug:
                os.remove(dpath)
            if semantic is not None:
                return write_semantic_candidate(semantic)
            recovered = write_recovered_loadstring()
            if recovered is not None:
                return recovered
            raise RuntimeError("v14 payload root could not be isolated from Luraph runtime scaffolding")

        # A one/few-statement payload must not turn into thousands of lines of
        # Luraph bootstrap code.  Known unresolved runtime helpers are another
        # strong sign that the static root followed the loader instead of the
        # payload.  In that narrow case, the fully observed compact trace is a
        # better semantic reconstruction.
        if semantic is not None:
            llines = max(1, lifted.count("\n"))
            slines = max(1, semantic.count("\n"))
            partial_static = "PARTIAL RECOVERY:" in lifted
            unresolved = "devirt:" in lifted
            direct_observable = all(
                (not ln.strip()) or ln.lstrip().startswith("--") or
                re.match(r"^(?:print|warn)\s*\(", ln.strip())
                for ln in semantic.splitlines()
            )
            static_missed_observable = (
                direct_observable and
                (("print(" in semantic and "print(" not in lifted) or
                 ("warn(" in semantic and "warn(" not in lifted))
            )
            if (not partial_static and
                    (unresolved or static_missed_observable or (llines > 200 and llines > slines * 10))):
                return write_semantic_candidate(semantic)

        nil_calls = lifted.count("(nil)(")
        if nil_calls < 50 or nil_calls * 100 < lifted.count("\n"):
            return dpath
        print("[!] the devirtualized output is broken (%d calls of nil)" % nil_calls, file=sys.stderr)
        if not job.debug:
            os.remove(dpath)
        recovered = write_recovered_loadstring()
        if recovered is not None:
            return recovered
        if getattr(args, "trace_fallback", False):
            if not os.path.exists(job.trace_path):
                write_trace()
            return job.trace_path
        raise RuntimeError("devirtualized output was invalid and no intercepted loadstring payload was available")

    if devirt_on:
        if semantic is not None:
            return write_semantic_candidate(semantic)
        recovered = write_recovered_loadstring()
        if recovered is not None:
            return recovered
        if getattr(args, "trace_fallback", False):
            print("[!] devirtualization produced no source; returning behaviour trace because --trace-fallback was requested",
                  file=sys.stderr)
            if not os.path.exists(job.trace_path):
                write_trace()
            return job.trace_path
        raise RuntimeError(
            "devirtualization produced no source and no intercepted loadstring payload; "
            "rerun with --debug for diagnostics or --trace-fallback if you explicitly want the behavior trace"
        )

    # --no-devirt intentionally asks for the behavior trace.
    if not os.path.exists(job.trace_path):
        write_trace()
    return job.trace_path


def lift(job, runner, patched, cfg, chunks, run_text, ppath, dpath, chunk_paths):
    """devirtualize() with its constant rounds answered by one long-lived
    harness (started now, so the script runs while round 1 walks); a fresh
    run per round if it fails or behaves differently."""
    args = job.args
    bridge = runner.bridge
    server = [None]
    synced = [False]    # the long-lived harness made the current dump
    if not bridge and not os.environ.get("DEOB_NO_SERVE"):
        server[0] = harness.HarnessServer(runner.luau, patched, cfg, chunks)
        server.append(False)    # its first run not checked yet

    def live():
        hs = server[0]
        if hs is None or not synced[0] or os.environ.get("DEOB_NO_FETCH"):
            return None
        return lambda paths, bufs: hs.fetch(paths, bufs, args.timeout)

    def rerun(c):
        synced[0] = False
        if bridge:
            return runner.run(patched, c, chunks)
        hs = server[0]
        if hs is not None and not server[1]:
            server[1] = True
            first, err = hs.reply(args.timeout)
            if os.environ.get("DEOB_SERVE_DIFF") and first is not None:
                for nm, tx in (("run", run_text), ("served", harness.trace_text(first))):
                    with open(job.path(".serve_%s.txt" % nm), "w", encoding="utf-8") as f:
                        f.write(tx)
            if first is None or not harness.same_trace(harness.trace_text(first), run_text):
                print("[!] the long-lived harness %s; running the script once per round instead"
                      % ("failed: " + err[-300:] if first is None else "traced differently"),
                      file=sys.stderr)
                hs.close()
                hs = server[0] = None
        if hs is not None:
            res = hs.request(c, args.timeout)
            if res[0] is not None:
                synced[0] = True
                return res
            print("[!] the long-lived harness failed: %s; running the script once per round "
                  "instead" % res[1][-300:], file=sys.stderr)
            hs.close()
            server[0] = None
        return runner.run(patched, c, chunks)
    try:
        devirtualize(job, ppath, dpath, cfg, rerun, chunk_paths, live)
    except Exception as e:
        # never lose the run over a lifter bug: the trace is still a result
        print("[!] devirtualization failed: %s: %s" % (type(e).__name__, e), file=sys.stderr)
        if os.environ.get("DEVIRT_TB"):
            import traceback
            traceback.print_exc()
    finally:
        if server[0] is not None:
            server[0].close()
