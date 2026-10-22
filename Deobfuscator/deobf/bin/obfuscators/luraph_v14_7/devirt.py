"""
Luraph v14.7 devirtualizer (front end + driver): lifts the VM protos
captured by the harness (*.protos.json) back into Luau with real control
flow. The IR and the back end are shared (ir.py, backend.py).

    python obfuscators/luraph_v14_7/devirt.py <src> <protos.json> [--all OUT | --raw KEY | --lift KEY | --op ...]

How it works (no hardcoded opcode table; handlers are randomized per build):
  * vmmap.maker_info finds each closure maker and its VM closure. The static
    VM model (VMModel) knows the closure prologue, the dispatch loops by mode
    value (`if k==93 then while true do ...`) and the return code after the
    handler function.
  * For every instruction, luasym.Interp runs one iteration of the real
    dispatch loop: operand arrays and helpers are concrete (from the dump),
    registers are symbolic. Instruction decoders (self-modifying handlers)
    simply run and the instruction is dispatched again. Branches on symbolic
    conditions fork the run; the paths become an IR tree per instruction.
  * The instruction graph is then structured into Luau (structure.py).
"""
import json
import os
import re
import struct
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))     # deobf/: the shared modules
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from obfuscators.luraph_v14_7 import vmmap  # noqa: E402
import backend  # noqa: E402
import luasym as S  # noqa: E402
from luasym import (LTable, Builtin, LuaFunc, Buf, Unsupported, Expr, Const, Reg, Pseudo, Global,  # noqa: E402
                    Upval, Index, Bin, Un, IfExp, TempVal, Vararg, ClosureExpr, Multi, TempTail,
                    VarargTail, SymList, TailCount, RegFile, EnvTable, UpContainer, Scope,
                    BreakSig, ReturnSig, YieldSig, is_sym)
from luasym import ContinueSig  # noqa: E402
from ir import (IRStmt, Assign, CallStmt, SetList, GenIter, Outcome, Next, Ret, Crash, Node,  # noqa: E402,F401
                ForPrep, Close, Opaque, Vec, Missing, fmt_expr, fmt_any, fmt_tail, fmt_multi, fmt_const,
                fmt_stmt, fmt_node)


class NilIndex(Missing):
    """Symbolic read through a table base that the v14 tracer could not
    materialize.  Unlike an undecoded constant, this is safe to fork on: the
    concrete VM path will eliminate impossible branches as the walk proceeds.
    """


# The shared v15-era symbolic interpreter rejects `nil[key]` before handing the
# access to the obfuscator-specific Lifter.index hook.  v14.7-14.9 handlers
# legitimately hit this shape while flattened helper state is still symbolic.
# Intercept only that exact failure and route it through Lifter.index, which
# returns NilIndex.  Keep every other Unsupported error unchanged.
if not getattr(S.Interp, "_luraph_v14_nil_index_patch", False):
    _v14_orig_eval = S.Interp.eval

    def _v14_eval(self, node, scope):
        try:
            return _v14_orig_eval(self, node, scope)
        except Unsupported as ex:
            msg = str(ex)
            if (isinstance(node, dict) and node.get("type") == "AstExprIndexExpr"
                    and msg.startswith("index nil @")):
                obj = self.eval(node["expr"], scope)
                key = self.eval(node["index"], scope)
                if isinstance(key, Multi):
                    key = key.first()
                return self.L.index(obj, key, self)
            if (isinstance(node, dict) and node.get("type") == "AstExprLocal"
                    and msg.startswith("unbound local ")):
                # A statically-known v14 runtime/native helper may close over a
                # lexical local outside the VM maker.  If that exact binding
                # was not serializable at capture time, keep it symbolic rather
                # than aborting the entire VM walk.  Real payload values still
                # win whenever the binding is available.
                local = node.get("local") or {}
                return Missing("outer:%s@%s" % (local.get("name", "?"),
                                                local.get("location", "?")))
            raise

    S.Interp.eval = _v14_eval
    S.Interp._luraph_v14_nil_index_patch = True

# v14 handlers sometimes perform arithmetic on values that are temporarily
# absent from the captured helper state.  Treat only that exact handler-state
# hole as symbolic; concrete Lua arithmetic errors are otherwise unchanged.
if not getattr(S.Interp, "_luraph_v14_nil_arith_patch", False):
    _v14_orig_binop = S.Interp.binop

    def _v14_binop(self, op, a, b):
        if op in ("Add", "Sub", "Mul", "Div", "FloorDiv", "Mod", "Pow") and (a is None or b is None):
            aa = a if a is not None else Missing("arith-left")
            bb = b if b is not None else Missing("arith-right")
            return self.L.sym_binop(op, aa, bb)
        return _v14_orig_binop(self, op, a, b)

    S.Interp.binop = _v14_binop
    S.Interp._luraph_v14_nil_arith_patch = True


# --------------------------------------------------------------------------
# captured data

class PatchLog(dict):
    """A patch dict that remembers the keys written since the last `take()`
    (live requests send only what changed)."""

    def __init__(self, *a):
        super().__init__(*a)
        self.dirty = set(self)

    def __setitem__(self, k, v):
        super().__setitem__(k, v)
        self.dirty.add(k)

    def update(self, other=(), **kw):
        for k, v in dict(other, **kw).items():
            self[k] = v

    def take(self):
        d, self.dirty = self.dirty, set()
        return d



def _load_json_loose(path):
    """Load a harness dump and repair trailing commas emitted when a run is cut off.

    The repair is string-aware: commas inside JSON strings are never touched.
    It only removes a comma whose next non-whitespace token is `}` or `]`.
    """
    with open(path, encoding="utf-8") as f:
        raw = f.read()
    try:
        return json.loads(raw)
    except json.JSONDecodeError:
        out = []
        i = 0
        in_str = False
        esc = False
        n = len(raw)
        while i < n:
            ch = raw[i]
            if in_str:
                out.append(ch)
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                i += 1
                continue
            if ch == '"':
                in_str = True
                out.append(ch)
                i += 1
                continue
            if ch == ',':
                j = i + 1
                while j < n and raw[j] in " \t\r\n":
                    j += 1
                if j < n and raw[j] in "}]":
                    i += 1
                    continue
            out.append(ch)
            i += 1
        return json.loads("".join(out))

class Dump:
    def __init__(self, path):
        d = _load_json_loose(path)
        self.raw = d
        self.tables = {}
        self.lfs = {}
        self.shared = {}        # lfid -> number: Luraph runtime closures the lifted code uses (SharedFn)
        self.buf_loc = {}       # id(Buf) -> (Buf, table id, key): where the buffer is stored
        self._load_tables(d["tables"])
        # bytes the lifted string decryptors wrote into VM buffers (id(Buf), offset) -> byte;
        # the runtime needs them to decode constants of code that never ran
        self.buf_patch = PatchLog()
        self.misses = {}
        self.vm_names = {"e"}     # capture names of the VM object (set by Program)
        # the same for shared tables (e.g. the string pool's offset table): (tid, key) -> value
        self.tab_patch = PatchLog()
        self.tid_of = {id(t): tid for tid, t in self.tables.items()}
        self.lazy = {int(tid) for tid, t in d["tables"].items() if t.get("mt")}
        # lazy table -> its decoder (the shared __index metamethod): see same_operand
        self.decoder = {int(tid): json.dumps(t["mtf"]) for tid, t in d["tables"].items() if t.get("mtf")}
        # constants decoded for a decrypted operand value: "seq,name,slot@value" -> value
        self.overrides = {path: self.val(v) for path, v in d.get("overrides", [])}
        self.pid_of_table = {int(k): v for k, v in d["pid_of_table"].items()}
        self.protos = {}
        for key, cap in d["protos"].items():
            self.protos[key] = {k: self.val(v) for k, v in cap.items()}
        self._paths = None
        self.late = self._lazy_late(d)
        # built now: the lifter writes into dump tables later
        self._by_operand = self._operand_facts()
        # live requests (deob.py HarnessServer.fetch): fetcher(paths, patches)
        # -> JSON, answered in the harness session that produced this dump
        self.fetcher = None
        self.fetched = set()
        self._fetched_any = False
        self.fetch_time = [0.0, 0.0, 0.0, 0]    # patches, round trip, in the harness, patch bytes sent
        self.extra_patches = (PatchLog(), PatchLog())   # stable patches of protos walked earlier this round
        self._sent = {}         # stable patch key -> value the harness session has applied

    def _lazy_late(self, d):
        """Lazy constants decoded at run time from an instruction's decoded
        operand, in a proto the runtime restored to its pre-run state (envlog
        CHAIN.unscramble, "late": [slot, ...]). The dump's operand is the
        undecoded one again, so they are not plain slots: they hold for the
        operand the lifter decodes for that instruction (each decodes once).
        -> {(tid, slot): value}"""
        late = {}
        for tid, t in d["tables"].items():
            for k in t.get("late") or ():
                key = S.norm_key(self.val(k))
                v = self.tables[int(tid)].h.pop(key, None)
                if v is not None:
                    late[(int(tid), key)] = v
        return late

    def _load_tables(self, tables):
        for tid in tables:
            self.tables[int(tid)] = LTable(tid=int(tid))
        for tid, t in tables.items():
            tb = self.tables[int(tid)]
            for i, v in enumerate(t["arr"], 1):
                if v is not None:
                    tb.h[i] = self.val(v)
                    if isinstance(tb.h[i], Buf):
                        self.buf_loc[id(tb.h[i])] = (tb.h[i], int(tid), i)
            for k, v in t["kv"]:
                kk = self.val(k)
                vv = self.val(v)
                if vv is not None:
                    tb.h[("opaque", id(kk)) if isinstance(kk, Expr) else S.norm_key(kk)] = vv
                    if isinstance(vv, Buf) and isinstance(kk, int):
                        self.buf_loc[id(vv)] = (vv, int(tid), kk)

    def fetch(self, rq):
        """A missing lazy constant (request path `rq`) decoded right away by
        the live harness, instead of in the next constant round. Its new
        tables join the dump. -> the value, or None (no harness, failed,
        or asked before)."""
        if self.fetcher is None or rq in self.fetched:
            return None
        self.fetched.add(rq)
        t0 = time.time()
        # the harness keeps what it got applied: only new or changed entries
        bw, tw = self._patch_delta()
        send = "+" + format_patches(bw, tw) if bw or tw else "="
        t1 = time.time()
        try:
            # a new reader's first request: the answer repeats every table
            # made since the dump (an earlier reader may have got them)
            first = not self._fetched_any
            self._fetched_any = True
            d = json.loads(self.fetcher([("*" if first else "") + rq], send))
            ft = self.fetch_time
            ft[0] += t1 - t0
            ft[1] += time.time() - t1
            ft[2] += d.get("t", 0)
            ft[3] += len(send)
        except Exception as ex:  # noqa: BLE001
            print("[!] live constant request failed (%s): back to constant rounds" % str(ex)[:200],
                  file=sys.stderr)
            self.fetcher = None
            return None
        # (answers repeat every table made since the dump: load the new ones)
        new = {tid: t for tid, t in (d.get("tables") or {}).items() if int(tid) not in self.tables}
        self._load_tables(new)
        for tid, t in new.items():
            if t.get("mt"):
                self.lazy.add(int(tid))
            if t.get("mtf"):
                self.decoder[int(tid)] = json.dumps(t["mtf"])
            self.tid_of[id(self.tables[int(tid)])] = int(tid)
        val = None
        for path, v in d.get("values") or []:
            val = self.val(v)
            if val is None:
                continue
            self.overrides[path] = val
            if path.startswith("!"):
                continue
            pre, _, last = path.rpartition(",")
            op = last.partition("@")[2]
            t = PathResolver(self).get(pre)
            if t is not None and op:
                self._add_operand(self._by_operand, t.tid, op, val)
            elif t is not None:
                # a plain slot: in the table, as a dump would have it
                k = int(last) if re.fullmatch(r"-?\d+", last) else last.encode("latin-1")
                t.h[S.norm_key(k)] = val
            if isinstance(val, LTable) and self._paths is not None and val.tid not in self._paths \
                    and not path.startswith("!"):
                self._extend_paths(val, path.split(","))
        return val

    def _patch_delta(self):
        """Stable patches written since the last live request that the
        harness session does not have yet: (bytes, table entries)."""
        paths = self.paths()
        bw, tw = {}, {}
        for d in (self.extra_patches[0], self.extra_patches[1]):
            for k in d.take():
                if k in d:
                    (bw if len(k) == 3 else tw)[k] = d[k]
        for bid, off in self.buf_patch.take():
            v = self.buf_patch.get((bid, off))
            buf, tid, key = self.buf_loc[bid]
            if isinstance(v, int) and buf.data[off] != v and tid in paths:
                bw[(",".join(str(x) for x in paths[tid]), key, off)] = v
        for tid, key in self.tab_patch.take():
            v = self.tab_patch.get((tid, key))
            base = self.tables[tid].h.get(key)
            if tid in paths and not (isinstance(base, (int, float)) and base == v):
                tw[(",".join(str(x) for x in paths[tid]), key)] = v
        for d in (bw, tw):
            for k in [k for k, v in d.items() if self._sent.get(k, d) == v]:
                del d[k]
            self._sent.update(d)
        return bw, tw

    def _extend_paths(self, root, path):
        paths = self._paths
        paths[root.tid] = path
        queue = [root]
        i = 0
        while i < len(queue):
            t = queue[i]
            i += 1
            for k, v in t.h.items():
                if isinstance(v, LTable) and v.tid not in paths and isinstance(k, int):
                    paths[v.tid] = paths[t.tid] + [k]
                    queue.append(v)

    def miss(self, why):
        self.misses[why] = self.misses.get(why, 0) + 1

    def same_operand(self, rq, tid):
        """A lazy constant depends only on the operand it is decoded from
        (`path,slot@v`): the operand indexes the constant pool of the table's
        decoder (its shared `__index` metamethod, "mtf" in the dump; one per
        VM implementation), so any table with the same decoder decoded for
        the same v (a plain slot t[k] with t[0][k] == v, or another `@v`
        result) gives the value without a request. Only scalars and flat
        tables of scalars (upvalue descriptors, rebuilt per decode): child
        protos are distinct objects. Without this a branch on such a constant
        stopped the walk once per round (StealAnEgg: one step per round)."""
        op = rq.rpartition(",")[2].partition("@")[2]
        hit = self._by_operand.get((self.decoder.get(tid, tid), op))
        return hit[1] if hit and hit[0] is not None else None

    def _operand_facts(self):
        """(decoder, operand) -> (signature, value) for same_operand."""
        by = {}

        def add(tid, op, v):
            self._add_operand(by, tid, op, v)
        res = PathResolver(self)
        for path, v in self.overrides.items():
            pre, _, last = path.rpartition(",")
            slot, at, op = last.partition("@")
            if at:
                t = res.get(pre)
                add(t.tid if t is not None else None, op, v)
        for lt in self.lazy:
            t = self.tables[lt]
            k0 = t.h.get(0)
            if not isinstance(k0, LTable):
                continue
            for k, v in t.h.items():
                op = k0.h.get(k) if type(k) is int and k >= 1 else None
                if type(op) in (int, float):
                    add(lt, S.fmt_num(op), v)
        return by

    def _add_operand(self, by, tid, op, v):
        if v is None or tid is None:
            return
        if isinstance(v, LTable):
            if any(isinstance(x, (LTable, OpaqueFn, Buf)) for x in v.h.values()):
                return
            sig = ("t", tuple(sorted((repr(k), repr(x)) for k, x in v.h.items())))
        elif isinstance(v, (bytes, int, float, bool)):
            sig = ("v", type(v).__name__, repr(v))
        else:
            return
        key = (self.decoder.get(tid, tid), op)
        old = by.get(key)
        if old is None:
            by[key] = (sig, v)
        elif old[0] != sig:
            by[key] = (None, None)      # disagree: never reuse

    def paths(self):
        """Shortest path to every table from a captured proto: [seq, name, key, key, ...]."""
        if self._paths is None:
            paths = {}
            queue = []
            for cap in self.protos.values():
                seq = cap.get("__seq")
                if seq is None:
                    continue
                for nm, v in cap.items():
                    if isinstance(v, LTable) and v.tid not in paths:
                        paths[v.tid] = [seq, nm]
                        if nm not in self.vm_names:   # the VM object: requests only, don't walk into it
                            queue.append(v)
            # tables that only exist as a decoded-on-request value (child protos
            # of code that never ran): reached through that request's path
            for rq, v in self.overrides.items():
                if isinstance(v, LTable) and v.tid not in paths and not rq.startswith("!"):
                    paths[v.tid] = rq.split(",")
                    queue.append(v)
            i = 0
            while i < len(queue):
                t = queue[i]
                i += 1
                for k, v in t.h.items():
                    if isinstance(v, LTable) and v.tid not in paths and isinstance(k, int):
                        paths[v.tid] = paths[t.tid] + [k]
                        queue.append(v)
            self._paths = paths
        return self._paths

    def val(self, v):
        if v is None or isinstance(v, bool):
            return v
        if isinstance(v, (int, float)):
            return S.fix_int(v)
        if "s" in v:
            return bytes.fromhex(v["s"])
        if "t" in v:
            return self.tables[v["t"]]
        if "f" in v:
            return Builtin(v["f"])
        if "lf" in v:
            f = self.lfs.get(v["lf"])
            if f is None:
                f = self.lfs[v["lf"]] = OpaqueFn(v["lf"])
                pf = v.get("pf")
                if pf is not None and "t" in pf:
                    f.pf_tid = pf["t"]
            return f
        if "num" in v:
            return {"inf": float("inf"), "-inf": float("-inf"), "nan": float("nan"), "-0": -0.0}[v["num"]]
        if "b" in v:
            return Buf(bytes.fromhex(v["b"]))
        if "g" in v:
            return EnvTable() if v["g"] == "ENV" else Builtin(v["g"])
        if "vec" in v:
            return Vec([S.fix_int(self.val(x)) for x in v["vec"]])
        src = v.get("src") or ""
        return Opaque(v.get("u"), bytes.fromhex(src).decode("utf-8", "replace") if src else "")


class OpaqueFn:
    """A Lua function value from the dump; bound to its AST later if known."""

    def __init__(self, lfid):
        self.lfid = lfid
        self.node = None
        self.pf_tid = None      # a VM closure: table id of its proto


class FrameArg(Global):
    """The caller's register frame passed as a call argument (a register
    holding the frame, `s[k] = s`, in the argument range). LPH_ENCSTR-style
    decryptors store their result into it (Program._walk evaluates such calls
    in the runtime, see frame_call); if one stays unevaluated it renders as nil."""

    def __init__(self, reg):
        Global.__init__(self, "nil --[[ the caller's registers ]]")
        self.reg = reg


class RuntimeMaker:
    """The closure maker looked up for a proto that exists only at runtime
    (ProtoLifter.index): calling it gives that value itself."""


class SharedFn(Global):
    """A VM closure the payload gets from the VM object (`R[a] = vmobj[k]`).
    Script code cannot reach the VM object, so this is Luraph's runtime
    (fetched.lua: LPH_ENCFUNC's decryptor, which deserializes the decrypted
    function with the VM's Lua-level loader): not lifted, a stub function
    named after the order of first use (lift_program)."""

    def __init__(self, fn, n):
        Global.__init__(self, "luraph_runtime%d" % n)
        self.fn = fn


# --------------------------------------------------------------------------
# static model of one VM (one closure maker)

def iter_nodes(n):
    """Every dict node under n, pre-order (iterative: the AST is deep)."""
    stack = [n]
    pop, push = stack.pop, stack.extend
    while stack:
        n = pop()
        if type(n) is dict:
            yield n
            push(reversed([v for v in n.values() if type(v) is dict or type(v) is list]))
        elif type(n) is list:
            push(reversed(n))


class VMModel:
    def __init__(self, info, dispatch_nodes, ctor_funcs):
        self.info = info
        self.maker = info["maker"]
        self.vm = info["vm"]
        self.dispatch = {id(n) for n in dispatch_nodes}
        self.ctor_funcs = ctor_funcs
        self.maker_decls = {}
        for k, nm in vmmap._decls_in(self.maker).items():
            self.maker_decls.setdefault(nm, []).append(k)
        body = self.vm["body"]["body"]
        # prologue ... local V,c,I,j,J = T(function(...) <loops> end, ...) ; post
        self.tcall_idx = None
        for i, st in enumerate(body):
            if st["type"] == "AstStatLocal" and len(st["values"]) == 1 \
                    and st["values"][0]["type"] == "AstExprCall":
                args = st["values"][0]["args"]
                if args and args[0]["type"] == "AstExprFunction" and \
                        any(id(n) in self.dispatch for n in iter_nodes(args[0])):
                    self.tcall_idx = i
                    break
        if self.tcall_idx is not None:
            # handlers run inside a protected call; the code after it returns
            self.prologue = body[:self.tcall_idx]
            self.tstat = body[self.tcall_idx]
            self.post = body[self.tcall_idx + 1:]
            self.inner = self.tstat["values"][0]["args"][0]
        else:
            # the loops sit directly in the VM closure; handlers return directly
            self.prologue = []
            self.tstat = None
            self.post = None
            self.inner = self.vm
        self.inner_body = self.inner["body"]["body"]
        self._find_state_vars()

    def _find_state_vars(self):
        """Loop-state stack K (K={...,[x]=K}), the values saved in it
        (pseudo for-loop variables) and the open-upvalue list (sink)."""
        vm_decls = vmmap._decls_in(self.vm)
        self.special = {}
        self.kstack_key = None
        self.kstack_link = None
        # the link may go through a copy: `ad=K; K={[7]=ad,...}`
        alias = {}
        for n in iter_nodes(self.inner):
            if n.get("type") in ("AstStatAssign", "AstStatLocal"):
                for var, val in zip(n["vars"], n["values"]):
                    loc = var["location"] if n["type"] == "AstStatLocal" else \
                        var["local"]["location"] if var["type"] == "AstExprLocal" else None
                    if loc and val["type"] == "AstExprLocal":
                        alias.setdefault(loc, set()).add(val["local"]["location"])
        for n in iter_nodes(self.inner):
            if n.get("type") != "AstStatAssign":
                continue
            for var, val in zip(n["vars"], n["values"]):
                if var["type"] != "AstExprLocal" or val["type"] != "AstExprTable":
                    continue
                me = var["local"]["location"]
                if me not in vm_decls:
                    continue
                link = None
                saved = []
                for it in val["items"]:
                    v = it["value"]
                    if v["type"] == "AstExprLocal" and it["kind"] == "general" and \
                            (v["local"]["location"] == me or alias.get(v["local"]["location"]) == {me}):
                        link = it["key"]["value"]
                    elif v["type"] == "AstExprLocal":
                        saved.append(v["local"])
                if link is not None:
                    self.kstack_key = me
                    self.kstack_link = S.fix_int(link)
                    for loc in saved:
                        self.special[loc["location"]] = ("pseudo", loc["name"])
        # open upvalues: `local q = N; if q then for f in next, q, nil do`
        iterated = set()        # locals iterated with a generic for somewhere
        for n in iter_nodes(self.inner):
            if n.get("type") == "AstStatForIn" and len(n["values"]) >= 2 and \
                    n["values"][1]["type"] == "AstExprLocal":
                iterated.add(n["values"][1]["local"]["location"])
        for n in iter_nodes(self.inner):
            if n.get("type") != "AstStatLocal":
                continue
            for var, val in zip(n["vars"], n["values"]):
                if val["type"] == "AstExprLocal" and val["local"]["location"] in vm_decls \
                        and val["local"]["location"] not in self.special \
                        and var["location"] in iterated:
                    self.special[val["local"]["location"]] = "sink"
        # ... or iterated directly (`for q in next, S, nil do ... S[q] = nil`,
        # fetched.lua's first VM): without this its boxes look like live
        # frame slots, and a closed-over local merges with later uses of its
        # register
        cleared = set()
        for n in iter_nodes(self.inner):
            if n.get("type") == "AstStatAssign":
                for var, val in zip(n["vars"], n["values"]):
                    if var["type"] == "AstExprIndexExpr" and var["expr"]["type"] == "AstExprLocal" \
                            and val["type"] == "AstExprConstantNil":
                        cleared.add(var["expr"]["local"]["location"])
        for loc in iterated & cleared:
            if loc in vm_decls and loc not in self.special:
                self.special[loc] = "sink"

    def is_dispatch(self, node):
        return id(node) in self.dispatch

    # The maker is called as maker(vm, proto, upvals) in one layout; another
    # repeats parameter names, function(g, d, d, d, d, j): only the last `d`
    # is visible (the proto) and the upvalue list follows it.
    def proto_index(self):
        return self.info.get("proto_index", 1)

    def upvals_index(self):
        return self.info.get("upvals_index", 2)

    def maker_args(self, vmobj, proto, upvals):
        n = len(self.maker["args"])
        vals = [None] * max(n, 3)
        vals[0], vals[self.proto_index()], vals[self.upvals_index()] = vmobj, proto, upvals
        return vals

    def proto_of(self, cap):
        p = cap.get("self")
        return p if p is not None else cap.get(self.maker["args"][self.proto_index()]["name"])

    def vmobj_of(self, cap):
        return cap.get(self.maker["args"][0]["name"])


def find_ctor_funcs(root):
    """Functions in the top-level `setmetatable({...})` table constructor: key -> AstExprFunction."""
    best = None
    for n in iter_nodes(root):
        if n.get("type") == "AstExprTable":
            fns = sum(1 for it in n["items"] if it["value"]["type"] == "AstExprFunction")
            if best is None or fns > best[0]:
                best = (fns, n)
    out = {}
    if best:
        pos = 0
        for it in best[1]["items"]:
            if it["kind"] == "item":
                pos += 1        # positional items: t[1], t[2], ...
            if it["value"]["type"] != "AstExprFunction":
                continue
            if it["kind"] == "item":
                out[pos] = it["value"]
            elif it["kind"] == "record":
                out[it["key"]["value"].encode("latin-1")] = it["value"]
            elif it["kind"] == "general" and it["key"]["type"] == "AstExprConstantNumber":
                out[S.fix_int(it["key"]["value"])] = it["value"]
            elif it["kind"] == "general" and it["key"]["type"] == "AstExprConstantString":
                out[it["key"]["value"].encode("latin-1")] = it["value"]
    return out


# --------------------------------------------------------------------------
# IR (the shared classes are in ir.py)

class VMCrash(Unsupported):
    pass


class Overlay:
    """Path-sensitive writes to the proto's instruction arrays and buffers.
    Luraph decrypts code in place, in XOR layers (several decryptors can cover
    one slot); decryptors on different paths must not see each other's
    effects. Persistent chain of dicts; `h` hashes the content (vs the base)
    so equal overlays from different paths merge."""
    __slots__ = ("parent", "d", "h", "depth")
    MASK = (1 << 64) - 1

    def __init__(self, parent=None):
        self.parent = parent
        self.d = {}
        self.h = parent.h if parent else 0
        self.depth = parent.depth + 1 if parent else 0

    def get(self, key, base):
        o = self
        while o is not None:
            if key in o.d:
                return o.d[key]
            o = o.parent
        return base

    def set(self, key, value, base_value):
        old = self.get(key, base_value)
        if _differs(old, base_value):
            self.h = (self.h - hash((key, _hv(old)))) & self.MASK
        if _differs(value, base_value):
            self.h = (self.h + hash((key, _hv(value)))) & self.MASK
        self.d[key] = value

    def flattened(self):
        if self.depth < 24:
            return self
        o = Overlay()
        chain = []
        x = self
        while x is not None:
            chain.append(x)
            x = x.parent
        for x in reversed(chain):
            o.d.update(x.d)
        o.h = self.h
        return o


def _differs(a, b):
    return type(a) is not type(b) or not S.lua_eq(a, b)


def _hv(v):
    if isinstance(v, (int, float, bytes, bool)) or v is None:
        return v
    return id(v)


class State:
    """(mode, pc, loop-stack, known jump-register values, array overlay) at an
    instruction boundary."""
    __slots__ = ("mode", "pc", "kstack", "jregs", "ov", "packs", "locs")

    def __init__(self, mode, pc, kstack, jregs=(), ov=None, packs=(), locs=()):
        self.mode, self.pc, self.kstack, self.jregs, self.ov = mode, pc, kstack, jregs, ov
        self.packs = packs    # ((reg, SymList), ...): registers holding table.pack(...) results
        self.locs = locs      # ((decl, value), ...): carried loop-function locals (Stepper.carry)

    def key(self, link):
        d = 0
        k = self.kstack
        if isinstance(k, JitFrame):
            d, k = k.depth, None
        while isinstance(k, LTable):
            d += 1
            k = k.get(link)
        return (self.mode, self.pc, d, self.jregs, self.ov.h if self.ov is not None else 0,
                tuple((r, fmt_expr(l)) for r, l in self.packs), self.locs)


# --------------------------------------------------------------------------

WALK_MAX_ERRORS = int(os.environ.get("DEVIRT_WALK_MAX_ERRORS", "500"))
WALK_RESTARTS = int(os.environ.get("DEVIRT_WALK_RESTARTS", "256"))
MAX_STACK_DEPTHS = int(os.environ.get("DEVIRT_MAX_STACK_DEPTHS", "32"))
STACK_WALK_MAX = int(os.environ.get("DEVIRT_STACK_WALK_MAX", "150000"))


class WalkIncomplete(Unsupported):
    """A VM walk could not be proven complete.

    A missing edge can remove part of the original program while still producing
    valid-looking Luau. v14 now preserves the resolved graph by default and marks
    unresolved states in generated output; set DEVIRT_STRICT=1 to reject partial
    graphs instead.
    """


def _walk_signature(lf, st, order):
    """A cheap convergence signature used to detect restart loops."""
    carry = tuple(sorted(getattr(st, "carry", ()), key=repr))
    jregs = tuple(sorted(lf.jump_regs, key=repr))
    unstable = tuple(sorted(lf.pack_unstable, key=repr))
    reqs = tuple(sorted(lf.requests))
    return (jregs, carry, unstable, reqs, len(order), lf.stack_base)


def unresolved_nodes(order):
    """Return [(state-key, reason), ...] for graph nodes that lost semantics."""
    return [(k, n.error) for k, n in order if getattr(n, "error", None)]


class ProtoLifter:
    """Steps the instructions of one proto."""
    walk_only = False   # set for request-collecting walks (no text is produced)

    def __init__(self, vm, dump, vmobj, proto, upvals, globals_tab):
        self.vm = vm
        self.vmobj = vmobj
        self.dump = dump
        self.special = vm.special
        self.globals_tab = globals_tab
        self.out = []
        self.temp_prefix = ""
        self.tcount = 0
        self.proto_arrays = set()
        self.reg_arrays = set()      # bases of register-resident arrays (see reg_array)
        self.children = []
        self.requests = set()
        self.jump_regs = set()
        self.jvals = {}
        self.jread = set()
        self.stack_base = None       # stack VM: registers above this are its operand stack (Stepper.carry)
        self.captured_regs = set()   # registers captured by closures (calls may change them)
        self.frame_uses = set()      # (upvalue, register) read/written through captured frames
        self.packs = {}         # reg -> SymList (from the state; copied on first read per run)
        self.pack_copies = {}
        self.pack_read = set()
        self.pack_unstable = set()   # (reg, text) packs left out of walk states (see Program._walk)
        self.pack_killed = set()     # (reg, text) unread packs overwritten somewhere
        self.ov = None          # overlay of the current run (child of the state's)
        self.ov_base = None
        # v14.x flattened handlers sometimes access a helper table through a
        # base that is temporarily unresolved by the symbolic interpreter.
        # Keep writes/reads to that base coherent within this prototype rather
        # than turning the base into literal Lua nil.
        self.nil_shadow = {}
        self.in_prologue = False
        self.cur_scope = None
        self.jstack = None           # LPH_JIT functions: the loop stack (JitFrame)
        self.proto = proto
        for v in proto.h.values():
            if isinstance(v, LTable):
                self.proto_arrays.add(id(v))
        self.making = False
        if isinstance(proto, JitProto):
            # a function an LPH_JIT function defines: its environment is
            # where it was made
            self.maker_scope = proto.env
            return
        # Run the closure maker itself.  v15 usually has a self-contained
        # maker, but v14.x factories can close over locals from an outer
        # initializer.  patch_entries serializes those free locals as __venvN;
        # rebuild the maker's lexical parent scope before interpreting it.
        maker_parent = Scope()
        cap = None
        for _cap in dump.protos.values():
            try:
                _p = vm.proto_of(_cap)
            except Exception:
                continue
            if _p is proto:
                cap = _cap
                break
        if cap is None:
            # Identity normally matches; equality is a fallback for deserialized
            # primitive/table wrappers used by some harness revisions.
            for _cap in dump.protos.values():
                try:
                    if vm.proto_of(_cap) == proto:
                        cap = _cap
                        break
                except Exception:
                    pass
        if cap is not None:
            for env in vm.info.get("outer_env", ()):
                field = env.get("field")
                decl = env.get("decl")
                if field in cap:
                    maker_parent.vars[decl] = cap[field]
        it = S.Interp(self)
        self.making = True
        r = it.call_lua(LuaFunc(vm.maker, maker_parent), Multi(vm.maker_args(vmobj, proto, upvals)))
        self.making = False
        f = r.first() if isinstance(r, Multi) else r
        if not isinstance(f, LuaFunc) or f.node is not vm.vm:
            raise Unsupported("closure maker did not return the VM closure")
        self.maker_scope = f.env

    # ---- setup: run the closure prologue
    def initial_state(self):
        self.in_prologue = True
        cs = Scope(self.maker_scope)
        cs.vars["..."] = Multi([], VarargTail(1))
        self.cur_scope = cs
        it = S.Interp(self)
        it.exec_block(self.vm.prologue, cs)
        self.in_prologue = False
        self.closure_scope = cs
        return cs

    def state_packs(self):
        """The unread packs carried into the next state."""
        return tuple(sorted(((r, l) for r, l in self.packs.items() if r not in self.pack_read
                             and (r, fmt_expr(l)) not in self.pack_unstable), key=lambda kv: kv[0]))

    # ---- hooks used by luasym.Interp
    def is_dispatch(self, node):
        return self.vm.is_dispatch(node)

    def emit(self, st):
        if isinstance(st, Assign) and isinstance(st.target, Reg):
            if isinstance(st.value, SymList):
                self.packs[st.target.n] = st.value
                self.pack_copies.pop(st.target.n, None)
            else:
                old = self.packs.pop(st.target.n, None)
                if old is not None and st.target.n not in self.pack_read:
                    self.pack_killed.add((st.target.n, fmt_expr(old)))
                self.pack_copies.pop(st.target.n, None)
        if isinstance(st, Assign) and isinstance(st.target, Reg) and self.jvals.get(st.target.n) is FRAME:
            del self.jvals[st.target.n]
        if isinstance(st, Assign) and isinstance(st.target, Reg) and st.target.n in self.jump_regs \
                and self.stack_base is not None and isinstance(st.target.n, int) and st.target.n > self.stack_base:
            # a stack VM's operand stack slot (above the frame's locals) that
            # held a return address or mode: it holds data too, so the
            # statements all stay (dead stores are dropped later)
            v = st.value
            if isinstance(v, Const) and isinstance(v.v, int) and not isinstance(v.v, bool):
                self.jvals[st.target.n] = v.v
            else:
                self.jvals.pop(st.target.n, None)
        elif isinstance(st, Assign) and isinstance(st.target, Reg) and st.target.n in self.jump_regs:
            v = st.value
            if isinstance(v, Const) and isinstance(v.v, int):
                self.jvals[st.target.n] = v.v
            else:
                self.jvals.pop(st.target.n, None)
            st.jump = True
        self.out.append(st)

    def new_temp(self):
        self.tcount += 1
        return "%s%d" % (self.temp_prefix, self.tcount)

    def special_get(self, sp, it):
        if sp == "sink":
            return OPENUPS
        if sp[0] == "reg":
            # a local of an LPH_JIT function (JitModel)
            return self.index(REGFILE, sp[1], it)
        if sp[0] == "jstack":
            return self.jstack
        if sp[0] == "upval":
            return Upval(sp[1])
        if sp[0] == "pseudo":
            return Pseudo(sp[1], self.depth(it))
        raise Unsupported(sp)

    def special_set(self, sp, v, it):
        if sp == "sink":
            return
        if sp[0] in ("reg", "jstack", "upval") and self.in_prologue:
            return      # (an LPH_JIT prologue run again: its writes belong to the entry)
        if sp[0] == "upval":
            self.emit(Assign(Upval(sp[1]), self.value_of(v)))
            return
        if sp[0] == "jstack":
            if isinstance(v, Multi):
                v = v.first()
            if v is None:
                self.jstack = JIT_BOTTOM
                return
            if isinstance(v, JitFrame):
                self.jstack = v         # pop
                return
            link = [k for k, x in v.h.items() if isinstance(x, JitFrame)] if isinstance(v, LTable) else []
            if isinstance(v, LTable) and v.tid is None and len(link) <= 1:
                # push: the other slots become loop variables of the new
                # depth. It links to the current frame, or (a loop right
                # after another one) replaces the top frame, or starts over
                # at the bottom (a literal nil link)
                parent = v.h[link[0]] if link else JIT_BOTTOM
                fr = JitFrame(link[0] if link else None, parent.depth + 1)
                if link:
                    fr.h[link[0]] = parent
                for k, x in v.h.items():
                    if not link or k != link[0]:
                        pv = Pseudo("JIT%s" % k, fr.depth)
                        self.emit(Assign(pv, self.value_of(x)))
                        fr.h[k] = pv
                self.jstack = fr
                return
            raise Unsupported("LPH_JIT loop stack set to %r (%s; stack %s)" % (
                v, {k: fmt_any(x) for k, x in v.h.items()} if isinstance(v, LTable) else "", fmt_any(self.jstack)))
        if sp[0] == "reg":
            if isinstance(v, Multi):
                v = v.first()
            if isinstance(v, JitFrame):
                # a loop-stack frame passing through a register (`v = N[k]; N = v`)
                self.jvals[sp[1]] = v
                return
            if isinstance(self.jvals.get(sp[1]), JitFrame):
                del self.jvals[sp[1]]
            if isinstance(v, LTable) and v.tid is None and v.h:
                # a table constructor, as one expression: its items may read
                # the register it is assigned to (`t = {t[2], t[3], t[4], t[1]}`)
                keys = sorted(v.h, key=lambda k: (not isinstance(k, int), repr(k)))
                seq = keys == list(range(1, len(keys) + 1))
                items = [(None if seq else self.as_expr(k), self.value_of(v.h[k])) for k in keys]
                self.newindex(REGFILE, sp[1], S.NewTable(items), it)
                return
            self.newindex(REGFILE, sp[1], v, it)
            return
        if sp[0] == "pseudo":
            self.emit(Assign(Pseudo(sp[1], self.depth(it)), self.value_of(v)))
            return
        raise Unsupported(sp)

    def depth(self, it):
        if isinstance(getattr(self, "jstack", None), JitFrame):
            return self.jstack.depth
        if not self.vm.kstack_key:
            return 0
        k = self.cur_scope.lookup(self.vm.kstack_key)
        kv = k.vars[self.vm.kstack_key] if k else None
        d = 0
        while isinstance(kv, LTable):
            d += 1
            kv = kv.get(self.vm.kstack_link)
        return d

    def jit_closure(self, fn):
        """A Lua function made inside an LPH_JIT function -> ClosureExpr
        lifted with its own JitModel. The outer locals it uses are upvalues:
        registers by reference, instruction temps with a symbolic value
        copied into a register first."""
        jm = _jit_nested_model(fn.node)
        if jm is None:
            raise Unsupported("a Lua function in an LPH_JIT function that is not a state machine")
        declared = _declared_in(fn.node)
        ups, upmap = [], {}
        for n in iter_nodes(fn.node):
            if n.get("type") != "AstExprLocal":
                continue
            loc = n["local"]["location"]
            if loc in declared or loc in upmap:
                continue
            sp = self.special.get(loc)
            if sp is not None and sp[0] == "reg":
                ups.append(Reg(sp[1]))
            elif sp is not None and sp[0] == "upval":
                ups.append(Upval(sp[1]))
            else:
                sc = fn.env.lookup(loc)
                v = sc.vars[loc] if sc is not None else None
                if not is_sym(v):
                    continue        # a fixed value: read through the environment
                self.tmp_regs = getattr(self, "tmp_regs", 0) + 1
                r = Reg(JIT_TMP + self.tmp_regs)
                self.emit(Assign(r, self.value_of(v)))
                ups.append(r)
            upmap[loc] = len(ups)
        c = ClosureExpr(JitProto(fn.env, upmap), ups)
        c.vm = jm
        for u in ups:
            if isinstance(u, Reg):
                self.captured_regs.add(u.n)
        self.children.append(c)
        return c

    def parallel_values(self, targets, vals, it):
        """`a, b = b, a` / `t[1], t[2] = t[2], t[1]`: Lua evaluates every value
        before assigning, but IR assignments are statements in order and
        register reads are references. A value that reads what an earlier
        target of the same statement writes (a register, or any table slot
        when a table store came first) is copied into a fresh register
        first."""
        regs = set()
        stored = False          # an earlier target stores into a table
        out = list(vals)
        for i, tg in enumerate(targets):
            x = out[i]
            if i > 0 and (regs or stored) and is_sym(x):
                hit = False
                for e in walk_expr(x):
                    if (isinstance(e, Reg) and e.n in regs) or (stored and isinstance(e, (Index, Pseudo))):
                        hit = True
                        break
                if hit:
                    self.tmp_regs = getattr(self, "tmp_regs", 0) + 1
                    t = Reg(JIT_TMP + self.tmp_regs)
                    self.emit(Assign(t, self.value_of(x)))
                    out[i] = t
            if tg[0] == "local":
                sp = self.special.get(tg[1]["location"])
                if sp is not None and sp[0] == "reg":
                    regs.add(sp[1])
            elif tg[0] == "index":
                if isinstance(tg[1], RegFile) and isinstance(tg[2], int):
                    regs.add(S.norm_key(tg[2]))
                elif is_sym(tg[1]) or isinstance(tg[1], JitFrame):
                    stored = True
        return out

    def global_value(self, name):
        v = self.globals_tab.get(name.encode("latin-1"))
        if v is None:
            # "Hardcode Globals" bakes script globals into handlers
            # (`R[a] = assert`): the value is the script's global.
            return Global(name)
        return v

    def reg_array(self, key):
        """`R[base + e]`: Luraph keeps a local array in registers base..
        (fetched.lua: two 256-entry tables at 6 and 262). Lifted as a table
        `Reg(REG_ARRAY + base)` indexed by e, declared `{}` at entry."""
        if not (isinstance(key, S.Bin) and key.op == "Add"):
            return None
        a, b = key.a, key.b
        if isinstance(b, Const) and isinstance(b.v, int) and not isinstance(b.v, bool):
            a, b = b, a
        if not (isinstance(a, Const) and isinstance(a.v, int) and not isinstance(a.v, bool)):
            return None
        self.reg_arrays.add(a.v)
        return Reg(REG_ARRAY + a.v), b

    def library_name(self, t):
        for k, v in self.globals_tab.h.items():
            if v is t and isinstance(k, bytes):
                return k.decode("latin-1")
        return None

    def set_global(self, name, v):
        # "Hardcode Globals" handler store (`deepcopy = R[a]`)
        self.emit(Assign(Global(name), self.value_of(v)))

    def varargs(self, scope):
        s = scope
        while s is not None:
            if "..." in s.vars:
                return s.vars["..."]
            s = s.parent
        raise Unsupported("varargs outside vararg function")

    def as_expr(self, v):
        if isinstance(v, BoxPart):
            return Index(Upval(v.idx), self.as_expr(v.k))
        if isinstance(v, BoxProxy):
            return Upval(v.idx)
        if isinstance(v, Expr):
            return v
        if isinstance(v, Vec):
            return v
        if v is None or isinstance(v, (bool, int, float, bytes)):
            return Const(v)
        if isinstance(v, Multi):
            return self.as_expr(v.first())
        if isinstance(v, RegFile):
            # v14.x helper calls can pass the entire VM register frame as an
            # ordinary argument.  The devirtualizer already knows how to
            # evaluate frame-writing calls through FrameArg/frame_call; the
            # missing conversion here was what caused `RegFile ... in an
            # expression` on 14.8/14.9.
            return FrameArg(-1)
        if isinstance(v, EnvTable):
            return Global("_ENV")
        if isinstance(v, LuaFunc) and isinstance(self.vm, JitModel):
            return self.jit_closure(v)
        if isinstance(v, OpaqueFn):
            # A pf tag means the runtime observed which proto created this Lua
            # closure.  It does *not* mean that every occurrence is a script
            # child we should recursively lift: Luraph keeps VM/runtime helper
            # closures in its VM object too.  Real script closure opcodes are
            # represented as ClosureExpr by make_closure().  Treat dump-only
            # OpaqueFn values like v15 does unless we can preserve known native
            # source.  This prevents the v14 lifter from recursively decompiling
            # Luraph's own bootstrap/helper protos.
            if v.node is not None:
                native = self.native_opaque_fn(v)
                if native is not None:
                    return native
            n = self.dump.shared.setdefault(v.lfid, len(self.dump.shared) + 1)
            return SharedFn(v, n)
        if isinstance(v, Buf):
            # a buffer constant (LPH_ENCFUNC: the encrypted function)
            t = self.new_temp()
            self.emit(CallStmt(t, Global("buffer.fromstring"), Multi([Const(bytes(v.data))])))
            return TempVal(t, 1)
        if isinstance(v, Builtin) and v.fn is None:
            # a library function as a value (`R[a] = tonumber` with Hardcode
            # Globals, `local char = string.char`)
            return Global(v.name)
        if isinstance(v, LuaFunc):
            text = self.plain_function_text(v)
            if text is not None:
                return Opaque("function", text)
        raise Unsupported("value %r in an expression" % (v,))

    def _function_source(self, node):
        """Exact source slice for a native Lua function AST node."""
        lines = getattr(self.vm, "src_lines", None)
        if not isinstance(node, dict) or node.get("type") != "AstExprFunction" or not lines:
            return None
        m = re.fullmatch(r"(\d+),(\d+) - (\d+),(\d+)", node.get("location", ""))
        if not m:
            return None
        l1, c1, l2, c2 = (int(x) for x in m.groups())
        if not (0 <= l1 < len(lines) and 0 <= l2 < len(lines)):
            return None
        if l1 == l2:
            return lines[l1][c1:c2]
        return "\n".join([lines[l1][c1:]] + lines[l1 + 1:l2] + [lines[l2][:c2]])

    def _free_locals(self, node):
        """Free local declarations referenced by a native function.

        LPH_NO_VIRTUALIZE is allowed to capture upvalues.  Keep declaration
        identity (the AST location), because minified names can be reused in
        nested scopes.
        """
        declared = _declared_in(node)
        out = []
        seen = set()
        for n in iter_nodes(node):
            if n.get("type") != "AstExprLocal":
                continue
            loc = n["local"].get("location")
            if loc in declared or loc in seen:
                continue
            seen.add(loc)
            out.append(n["local"])
        return out

    def _decl_name(self, decl):
        name = decl.get("name") if isinstance(decl, dict) else None
        if isinstance(name, str) and name:
            return name
        # Luau AST builds used by the v15 deobfuscator normally expose the
        # name, but keep a deterministic fallback for older ast dumps.
        return "__lph_up_%d" % (abs(hash(str(decl.get("location", "")))) % 1000000)

    def plain_function_text(self, fn):
        """Preserve a native Lua closure (including LPH_NO_VIRTUALIZE).

        For a closure with upvalues, rebuild the lexical binding as an IIFE:

            (function(a,b) return function(...) ... end end)(VALUE_A, VALUE_B)

        This lets native/non-virtualized code coexist with devirtualized VM
        code instead of being discarded or misclassified as another VM.
        """
        node = fn.node
        text = self._function_source(node)
        if text is None:
            return None

        free = self._free_locals(node)
        if not free:
            return text

        env = getattr(fn, "env", None)
        if env is None:
            return None

        names = []
        values = []
        for decl in free:
            loc = decl.get("location")
            sc = env.lookup(loc) if hasattr(env, "lookup") else None
            if sc is None or loc not in sc.vars:
                return None
            value = sc.vars[loc]
            try:
                expr = self.as_expr(value)
                rendered = fmt_expr(expr)
            except (Unsupported, Exception):
                return None
            # Raw newlines/comments inside an argument are valid in Luau, but
            # parenthesizing the rendered expression avoids precedence leaks.
            names.append(self._decl_name(decl))
            values.append("(" + rendered + ")")

        return "(function(%s) return %s end)(%s)" % (
            ",".join(names), text, ",".join(values)
        )

    def native_opaque_fn(self, fn):
        """Preserve a statically-known native v14 function as Luau source.

        VM-object helpers and LPH_NO_VIRTUALIZE closures can capture locals from
        the initializer around the VM maker.  Rebuild those bindings from the
        maker scope instead of rejecting the function or executing it with an
        empty lexical environment.
        """
        node = getattr(fn, "node", None)
        text = self._function_source(node)
        if text is None:
            return None
        free = self._free_locals(node)
        if not free:
            return Opaque("function", text)
        env = getattr(self, "maker_scope", None)
        if env is None:
            return None
        names, values = [], []
        for decl in free:
            loc = decl.get("location")
            sc = env.lookup(loc) if hasattr(env, "lookup") else None
            if sc is None or loc not in sc.vars:
                return None
            try:
                rendered = fmt_expr(self.as_expr(sc.vars[loc]))
            except Exception:
                return None
            names.append(self._decl_name(decl))
            values.append("(" + rendered + ")")
        return Opaque("function", "(function(%s) return %s end)(%s)" %
                      (",".join(names), text, ",".join(values)))

    def sym_binop(self, op, a, b):
        if isinstance(a, SymList) or isinstance(b, SymList):
            raise Unsupported("arith on packed list")
        return Bin(op, self.as_expr(a), self.as_expr(b))

    def sym_unop(self, op, a):
        if isinstance(a, SymList):
            if op == "Len":
                return a.count_expr()
            raise Unsupported("unop on packed list")
        return Un(op, self.as_expr(a))

    def sym_and_or(self, kind, a, rhs):
        b = rhs()
        return Bin("And" if kind == "and" else "Or", self.as_expr(a), self.as_expr(b))

    # indexing
    def _nil_shadow_key(self, key):
        if isinstance(key, Multi):
            key = key.first()
        if is_sym(key):
            try:
                return ("sym", fmt_expr(self.as_expr(key)))
            except Exception:
                return ("sym", repr(key))
        try:
            return ("const", S.norm_key(key))
        except Exception:
            return ("repr", repr(key))

    def index(self, obj, key, it):
        if isinstance(obj, Multi):
            obj = obj.first()
        if isinstance(key, Multi):
            key = key.first()
        if isinstance(obj, RegFile):
            if is_sym(key):
                arr = self.reg_array(key)
                if arr is None:
                    raise Unsupported("symbolic register index")
                return Index(*arr)
            k = S.norm_key(key)
            if isinstance(k, (int, float)) and k < 1 and self.stack_base is not None:
                raise Unsupported("read below the stack VM's frame (register %s)" % k)
            if self.jvals.get(k) is FRAME:
                return obj
            if k in self.jvals:
                self.jread.add(k)
                return self.jvals[k]
            if k in self.packs:
                self.pack_read.add(k)
                c = self.pack_copies.get(k)
                if c is None:
                    src = self.packs[k]
                    c = SymList(src.items, src.tail, src.nkey)
                    c.extra = dict(src.extra)
                    self.pack_copies[k] = c
                return c
            return Reg(k)
        if isinstance(obj, EnvTable):
            if isinstance(key, bytes):
                return Global(key.decode("latin-1"))
            return Index(Global("_ENV"), self.as_expr(key))
        if isinstance(obj, UpContainer):
            return Upval(obj.idx)
        if isinstance(obj, UpList):
            if not isinstance(key, int):
                raise Unsupported("upvalue index %r" % (key,))
            return obj.get(key)
        if isinstance(obj, FrameProxy):
            if not isinstance(key, int):
                raise Unsupported("symbolic index into a captured frame")
            self.frame_uses.add((obj.idx, key))
            return Upval((obj.idx, key))
        if isinstance(obj, OpenUps):
            if not isinstance(key, int):
                raise Unsupported("open upvalue index %r" % (key,))
            return MaybeBox(key)
        if isinstance(obj, MaybeBox):
            return None
        if isinstance(obj, BoxProxy):
            if is_sym(key):
                return Index(Upval(obj.idx), self.as_expr(key))
            return BoxPart(obj.idx, key)
        if isinstance(obj, BoxPart):
            if isinstance(key, BoxPart) and key.idx == obj.idx:
                return Upval(obj.idx)
            return Index(self.as_expr(obj), self.as_expr(key))
        if isinstance(obj, LTable):
            if is_sym(key) and obj is self.vmobj and isinstance(key, Index) and isinstance(key.key, Index) \
                    and key.key.obj == key.obj and isinstance(key.key.key, Const):
                # the maker of a proto computed at runtime (`vmobj[P[P[k]]]`,
                # LPH_ENCFUNC's decrypted function): the closure is that value
                return RuntimeMaker()
            if is_sym(key):
                if self.walk_only and any(isinstance(x, Missing) for x in walk_expr(key)):
                    # a closure op reading its not yet decoded proto
                    # (`P[P[1]]`): requested already, walk on
                    return Missing(None)
                if os.environ.get("DEVIRT_TB"):
                    print("   table tid=%s path=%s items=%s" % (obj.tid, self.dump.paths().get(obj.tid), str(list(obj.h.items())[:12])), file=sys.stderr)
                raise Unsupported("symbolic index into a concrete VM table (key %s)" % fmt_expr(key))
            v = obj.get(key)
            if self.ov_base is not None and obj.tid is not None:
                v = self.cur_ov().get((id(obj), S.norm_key(key)), v)
            if v is None and (obj.tid, S.norm_key(key)) in self.dump.late:
                # decoded at run time for this instruction's decoded operand
                return self.dump.late[(obj.tid, S.norm_key(key))]
            if obj.tid in self.dump.lazy and isinstance(key, int) and self.ov_base is not None:
                # lazy constants are decoded from the instruction's operand
                # (obj[0] is that operand array): if this path decrypted the
                # operand, the constant must be decoded for the new value
                k0 = obj.get(0)
                if isinstance(k0, LTable):
                    base = k0.get(key)
                    cur = self.cur_ov().get((id(k0), key), base)
                    if _differs(cur, base):
                        path = self.dump.paths().get(obj.tid)
                        if path is None:
                            self.dump.miss("override without path")
                            return Missing(key)
                        rq = ",".join(str(x) for x in path) + ",%d@%s" % (key, S.fmt_num(cur))
                        if self.dump.overrides.get(rq) is not None:
                            return self.dump.overrides[rq]
                        same = self.dump.same_operand(rq, obj.tid)
                        if same is not None:
                            return same
                        self.requests.add(rq)
                        got = self.dump.fetch(rq)
                        if got is not None:
                            return got
                        # (a failed decode stays unknown; asked again next round)
                        self.dump.miss("override failed" if rq in self.dump.overrides else "override requested")
                        return Missing(key)
            if v is None and obj.tid in self.dump.lazy and isinstance(key, (int, bytes)):
                path = self.dump.paths().get(obj.tid)
                k = key.decode("latin-1") if isinstance(key, bytes) else key
                if path is not None and not (isinstance(k, str) and (k.isdigit() or "," in k or ";" in k)):
                    rq = ",".join(str(x) for x in path + [k])
                    if self.dump.overrides.get(rq) is not None:
                        # decoded inside a table that exists only as a request result
                        return self.dump.overrides[rq]
                    k0 = obj.get(0)
                    op = k0.get(key) if isinstance(k0, LTable) and isinstance(key, int) else None
                    if type(op) in (int, float):
                        same = self.dump.same_operand("%d@%s" % (key, S.fmt_num(op)), obj.tid)
                        if same is not None:
                            return same
                    self.requests.add(rq)
                    got = self.dump.fetch(rq)
                    if got is not None:
                        return got
                if not self.making:
                    self.dump.miss("plain, path" if path is not None else "plain, no path")
                    v = Missing(key)
            return v
        if isinstance(obj, SymList):
            return self.symlist_get(obj, key)
        if isinstance(obj, Expr):
            return Index(obj, self.as_expr(key))
        if obj is None:
            # v14.x flattened handlers can temporarily lose the concrete table
            # base. Preserve coherent mutations on that unresolved table.  A
            # later read of the same key sees the value written by the handler;
            # otherwise the read remains symbolic.
            sk = self._nil_shadow_key(key)
            if sk in self.nil_shadow:
                return self.nil_shadow[sk]
            return NilIndex(key)
        raise Unsupported("index %r" % (obj,))

    def symlist_get(self, lst, key):
        if key == lst.nkey or (lst.nkey is None and key == b"n"):
            return lst.count_expr()
        if isinstance(key, int) and key >= 1:
            if key <= len(lst.items):
                return lst.items[key - 1]
            if lst.tail is not None:
                return lst.tail.at(key - len(lst.items))
            return None
        if key in lst.extra:
            return lst.extra[key]
        raise Unsupported("packed list index %r" % (key,))

    def newindex(self, obj, key, v, it):
        if isinstance(key, Multi):
            key = key.first()
        if isinstance(obj, RegFile):
            if is_sym(key):
                arr = self.reg_array(key)
                if arr is None:
                    raise Unsupported("symbolic register store")
                self.emit(Assign(Index(*arr), self.value_of(v)))
                return
            if isinstance(v, RegFile):
                self.jvals[S.norm_key(key)] = FRAME
                return
            if isinstance(key, (int, float)) and key < 1 and self.stack_base is not None:
                raise Unsupported("store below the stack VM's frame (register %s)" % key)
            self.emit(Assign(Reg(S.norm_key(key)), self.value_of(v)))
            return
        if isinstance(obj, FrameProxy):
            if not isinstance(key, int):
                raise Unsupported("symbolic store into a captured frame")
            self.frame_uses.add((obj.idx, key))
            self.emit(Assign(Upval((obj.idx, key)), self.value_of(v)))
            return
        if isinstance(obj, EnvTable):
            tgt = Global(key.decode("latin-1")) if isinstance(key, bytes) else Index(Global("_ENV"), self.as_expr(key))
            self.emit(Assign(tgt, self.value_of(v)))
            return
        if isinstance(obj, UpContainer):
            self.emit(Assign(Upval(obj.idx), self.value_of(v)))
            return
        if isinstance(obj, OpenUps):
            if v is None and isinstance(key, int):
                self.emit(Close(key))
            return
        if isinstance(obj, MaybeBox):
            return
        if isinstance(obj, BoxPart):
            if isinstance(key, BoxPart) and key.idx == obj.idx:
                self.emit(Assign(Upval(obj.idx), self.value_of(v)))
            else:
                self.emit(Assign(Index(self.as_expr(obj), self.as_expr(key)), self.value_of(v)))
            return
        if isinstance(obj, BoxProxy):
            self.emit(Assign(Index(Upval(obj.idx), self.as_expr(key)), self.value_of(v)))
            return
        if isinstance(obj, JitFrame) and obj.depth > 0:
            k = S.norm_key(key)
            if k == obj.link:
                raise Unsupported("store into an LPH_JIT loop stack link")
            pv = Pseudo("JIT%s" % k, obj.depth)
            self.emit(Assign(pv, self.value_of(v)))
            obj.h[k] = pv
            return
        if isinstance(obj, LTable):
            if is_sym(key):
                raise Unsupported("symbolic key store into a concrete VM table")
            if id(obj) in self.proto_arrays:
                self.mutated = True
            if self.ov_base is not None and obj.tid is not None:
                # tables from the dump are shared by all paths: path-local writes
                self.write_ov((id(obj), S.norm_key(key)), v, obj.get(key))
                return
            obj.set(key, v)
            return
        if isinstance(obj, SymList):
            if key == lst_nkey(obj):
                return  # count updates are implied by the list shape
            if isinstance(key, int) and key >= 1:
                while len(obj.items) < key and obj.tail is None:
                    obj.items.append(None)
                if key <= len(obj.items):
                    obj.items[key - 1] = v
                    return
            obj.extra[key] = v
            return
        if isinstance(obj, Expr):
            self.emit(Assign(Index(obj, self.as_expr(key)), self.value_of(v)))
            return
        if obj is None:
            # Match index(None, key): keep the mutation in an unresolved-table
            # shadow so flattened decoder/helper state can survive across the
            # remainder of this prototype walk.
            self.nil_shadow[self._nil_shadow_key(key)] = v
            return
        raise Unsupported("newindex %r" % (obj,))

    def cur_ov(self):
        return self.ov if self.ov is not None else self.ov_base

    def write_ov(self, key, v, base):
        if self.ov is None:
            self.ov = Overlay(self.ov_base)
        self.ov.set(key, v, base)

    def check_decision(self, cond):
        # (forking both ways here in request walks was tried: same functions
        # per round on StealAnEgg, but walks into junk code; not worth it)
        if any(isinstance(x, Missing) and not isinstance(x, NilIndex) for x in walk_expr(cond)):
            raise Unsupported("needs a constant that is not decoded yet")

    def value_of(self, v):
        """Value for an IR assignment: expressions, constants, closures, lists."""
        if isinstance(v, Multi):
            v = v.first()
        if isinstance(v, GenIterMaker):
            return GenIter(v.args)
        if isinstance(v, (ClosureExpr, GenIter)):
            return v
        if isinstance(v, LuaFunc) and isinstance(self.vm, JitModel):
            return self.jit_closure(v)
        if isinstance(v, SymList):
            return v
        if isinstance(v, LTable):
            if v is self.proto:
                # only Luraph's LPH_CRASH() expansion touches the VM's own
                # proto (it scrambles it, then spins forever)
                raise VMCrash()
            if v.h:
                lib = self.library_name(v)
                if lib is not None:
                    # a whole library as a value (`R[a] = string`, Hardcode Globals)
                    return Global(lib)
                # v14.x (especially 14.9) uses real table constructors as
                # register values in ordinary opcode handlers.  v15 mostly
                # avoided this shape, so the old lifter rejected every
                # non-empty LTable.  Lower acyclic concrete tables to Luau
                # table literals instead.
                stack = getattr(self, "_table_value_stack", None)
                if stack is None:
                    stack = self._table_value_stack = set()
                ident = id(v)
                if ident in stack:
                    raise Unsupported("cyclic VM table stored into a register")
                stack.add(ident)
                try:
                    keys = sorted(v.h, key=lambda k: (not isinstance(k, int), repr(k)))
                    seq = keys == list(range(1, len(keys) + 1))
                    items = []
                    for k in keys:
                        val = v.h[k]
                        keyexpr = None if seq else self.as_expr(k)
                        items.append((keyexpr, self.value_of(val)))
                    return S.NewTable(items)
                finally:
                    stack.discard(ident)
            return S.NewTable()
        return self.as_expr(v)

    # calls
    def call_builtin(self, fn, args, it, stat):
        name = fn.name
        a = args
        if name in ("table.create",):
            if self.in_prologue:
                return RegFile()
            return LTable()
        if name == "getfenv":
            return EnvTable()
        if name == "setfenv":
            return Multi(a.items[:1])
        if name == "table.pack":
            return SymList(a.items, a.tail, nkey=b"n")
        if name in ("unpack", "table.unpack"):
            return self.unpack(a)
        if name == "table.move":
            return self.tmove(a)
        if name == "select":
            n = a.items[0] if a.items else None
            rest = Multi(a.items[1:], a.tail)
            if n == b"#":
                if rest.tail is None:
                    return len(rest.items)
                return TailCount(rest.tail) if not rest.items else Bin("Add", TailCount(rest.tail), Const(len(rest.items)))
            if isinstance(n, int):
                k = n - 1
                if k <= len(rest.items):
                    return Multi(rest.items[k:], rest.tail)
                return Multi([], rest.tail.drop(k - len(rest.items)) if rest.tail else None)
            raise Unsupported("select with %r" % (n,))
        if name == "coroutine.wrap":
            return GenIterMaker()
        if name == "next" and a.items and isinstance(a.items[0], OpenUps):
            return None
        if name.startswith("buffer.") and a.items and isinstance(a.items[0], Buf) and self.ov_base is not None:
            r = self.buffer_op(name, a.items)
            if r is not NotImplemented:
                return r
        if name in S.CONCRETE:
            vals = a.items
            if a.tail is not None or any(is_sym(x) or isinstance(x, (SymList, Multi)) for x in vals):
                if name.startswith("bit32.") and a.tail is None and all(is_sym(x) or isinstance(x, int) for x in vals):
                    # a handler for the script's own bit32 call (`x = bit32.bxor(y, K)`
                    # compiled into a dedicated opcode): the real call
                    t = self.new_temp()
                    self.emit(CallStmt(t, Global(name), Multi([self.value_of(x) for x in vals])))
                    return Multi([], TempTail(t))
                raise Unsupported("builtin %s on symbolic values" % name)
            try:
                r = S.CONCRETE[name](*vals)
            except (struct.error, IndexError, ValueError, TypeError, OverflowError) as ex:
                raise Unsupported("%s failed: %s" % (name, ex))
            return r
        raise Unsupported("builtin " + name)

    def buffer_op(self, name, args):
        """Byte reads/writes of VM buffers go through the path overlay."""
        b = args[0]
        if name in ("buffer.readu8", "buffer.readi8") and len(args) >= 2 and isinstance(args[1], int):
            v = self.cur_ov().get((id(b), args[1]), None)
            if v is None:
                return NotImplemented
            return v - 256 if name == "buffer.readi8" and v >= 128 else v
        if name in ("buffer.writeu8", "buffer.writei8") and len(args) >= 3 and isinstance(args[1], int) \
                and isinstance(args[2], (int, float)):
            off = args[1]
            self.write_ov((id(b), off), int(args[2]) & 255, b.data[off])
            return Multi([])
        if name.startswith("buffer.write") or name.startswith("buffer.read"):
            # wider accesses: only safe when the overlay has no bytes of this buffer
            if any(k[0] == id(b) for k in self._ov_keys()):
                raise Unsupported("wide buffer access after in-place decryption")
        return NotImplemented

    def _ov_keys(self):
        o = self.cur_ov()
        keys = set()
        while o is not None:
            keys |= set(o.d)
            o = o.parent
        return keys

    def unpack(self, a):
        t = a.items[0] if a.items else None
        i = a.items[1] if len(a.items) > 1 else 1
        j = a.items[2] if len(a.items) > 2 else None
        if isinstance(t, RegFile):
            if not isinstance(i, int) or not isinstance(j, int):
                raise Unsupported("unpack registers with symbolic range")
            return Multi([FrameArg(n) if self.jvals.get(n) is FRAME else Reg(n) for n in range(i, j + 1)])
        if isinstance(t, SymList):
            if i != 1:
                raise Unsupported("unpack packed list from %r" % (i,))
            if j is None or is_sym(j) or (isinstance(j, int) and t.tail is not None and j >= len(t.items)):
                if isinstance(j, int) and t.tail is None:
                    return Multi(pad(t.items, j))
                return Multi(t.items, t.tail)
            return Multi(pad(t.items, j))
        if isinstance(t, LTable):
            if j is None:
                j = t.length()
            return Multi([t.get(n) for n in range(i, j + 1)])
        if isinstance(t, Expr):
            # a table in a register (e.g. a table.pack result read a second
            # time): a real unpack call
            tt = self.new_temp()
            self.emit(CallStmt(tt, Global("table.unpack"),
                               Multi([self.value_of(x) if x is not None else Const(None) for x in a.items], a.tail)))
            return Multi([], TempTail(tt))
        raise Unsupported("unpack %r" % (t,))

    def tmove(self, a):
        src, f, e, t, dst = (a.items + [None] * 5)[:5]
        if dst is None:
            dst = src
        if isinstance(src, SymList) and src is dst:
            # shift right in place: move(d, 1, count, T, d)
            if f == 1 and isinstance(t, int):
                src.items = [None] * (t - 1) + src.items
                return dst
            raise Unsupported("in-place move of packed list")
        if is_sym(f) or is_sym(t):
            raise Unsupported("table.move with symbolic positions")
        if is_sym(e) and isinstance(src, SymList) and f == 1 and isinstance(dst, Expr) and isinstance(t, int):
            # SETLIST with a multret tail: tbl[t...] = unpack(list)
            self.emit(SetList(dst, t, Multi([self.value_of(x) if x is not None else Const(None) for x in src.items],
                                            src.tail)))
            return dst
        if is_sym(e) and isinstance(src, Expr) and isinstance(dst, Expr):
            # a pack held in a register that is no longer tracked: the real call
            tt = self.new_temp()
            self.emit(CallStmt(tt, Global("table.move"),
                               Multi([self.value_of(x) if x is not None else Const(None) for x in a.items])))
            return dst
        if is_sym(e):
            raise Unsupported("table.move with symbolic end")
        n = e - f + 1
        for k in range(n):
            v = self.elem(src, f + k)
            self.put(dst, t + k, v)
        return dst

    def elem(self, src, i):
        if isinstance(src, RegFile):
            return Reg(i)
        if isinstance(src, SymList):
            return self.symlist_get(src, i)
        if isinstance(src, LTable):
            return src.get(i)
        raise Unsupported("move from %r" % (src,))

    def put(self, dst, i, v):
        if isinstance(dst, RegFile):
            self.emit(Assign(Reg(i), self.value_of(v) if v is not None else Const(None)))
        elif isinstance(dst, Expr):
            self.emit(Assign(Index(dst, Const(i)), self.value_of(v) if v is not None else Const(None)))
        elif isinstance(dst, SymList):
            while len(dst.items) < i and dst.tail is None:
                dst.items.append(None)
            if i <= len(dst.items):
                dst.items[i - 1] = v
            else:
                raise Unsupported("store past a packed list's tail")
        elif isinstance(dst, LTable):
            dst.set(i, v)
        else:
            raise Unsupported("move into %r" % (dst,))

    def call_symbolic(self, fn, args, it, stat):
        if isinstance(fn, GenIterMaker):
            fn.args = args
            return Multi([])
        if isinstance(fn, OpaqueFn) and fn.node is None and fn.pf_tid is None:
            # v14.7-14.9 have an untagged runtime factory used as
            # helper(protoTable, upvalueTable).  The first argument is a real
            # captured proto (pid_of_table knows it), and the second is the
            # closure's upvalue vector.  Reconstruct that closure instead of
            # emitting a stub call that expands the Luraph bootstrap.
            vals = list(args.items)
            for i, proto in enumerate(vals):
                if not isinstance(proto, LTable) or proto.tid not in self.dump.pid_of_table:
                    continue
                ups = vals[i + 1] if i + 1 < len(vals) else None
                if not isinstance(ups, LTable):
                    continue
                entries = [ups.get(k) for k in range(1, ups.length() + 1)]
                c = ClosureExpr(proto, entries)
                c.vm = self.vm
                return Multi([c])
        if isinstance(fn, RuntimeMaker):
            vals = args.items
            pi = self.vm.proto_index()
            return Multi([vals[pi] if len(vals) > pi else None])
        if isinstance(fn, OpaqueFn):
            node = self.vm_fn_node(fn)
            if node is not None and node is self.vm.maker:
                return self.make_closure(args)
            target = getattr(self.vm, "siblings", {}).get(id(node)) if node is not None else None
            if target is not None:
                return self.make_closure(args, target)
            if node is not None:
                # v14 LPH_NO_VIRTUALIZE / legacy LPH_JIT_ULTRA functions are
                # native Lua closures, not VM bytecode.  First try the normal
                # symbolic interpreter; if the native body uses syntax or
                # environment state that the VM interpreter does not model,
                # preserve the function as native source and emit the call
                # instead of treating it as a broken VM function.
                try:
                    return it.call_lua(LuaFunc(node, self.maker_scope), args)
                except Unsupported:
                    native = self.native_opaque_fn(fn)
                    if native is not None:
                        t = self.new_temp()
                        self.emit(CallStmt(
                            t, native,
                            Multi([self.value_of(x) if not isinstance(x, SymList) else x
                                   for x in args.items], args.tail),
                        ))
                        return Multi([], TempTail(t))
                    raise
            if fn.pf_tid is None:
                # v14.x has helper closures which are real runtime Lua
                # functions but are not always tagged with a prototype.
                # Preserve the call through a generated runtime stub rather
                # than making one opaque helper abort the entire payload lift.
                pass
            # a VM/runtime closure kept by the VM: emit an ordinary call.
            # as_expr() turns unresolved OpaqueFn values into SharedFn stubs.
        if isinstance(fn, Multi):
            fn = fn.first()
        if isinstance(fn, (GenIterMaker,)):
            return Multi([])
        if self.walk_only and any(isinstance(x, Missing) for x in walk_expr(fn)):
            # e.g. a closure handler using its not yet decoded proto: the
            # proto is requested already, the rest of the function still counts
            return Multi([Missing(None)])
        fe = self.as_expr(fn) if not isinstance(fn, (ClosureExpr,)) else fn
        t = self.new_temp()
        self.emit(CallStmt(t, fe, Multi([self.value_of(x) if not isinstance(x, SymList) else x
                                         for x in args.items], args.tail)))
        return Multi([], TempTail(t))

    def vm_fn_node(self, fn):
        return fn.node

    def make_closure(self, args, vm=None):
        """A VM closure of the proto in args; vm: the interpreter (VMModel)
        whose maker was called, when it is not this proto's."""
        vals = args.items
        vm = vm or self.vm
        pi, ui = vm.proto_index(), vm.upvals_index()
        proto = vals[pi] if len(vals) > pi else None
        ups = vals[ui] if len(vals) > ui else None
        if self.walk_only and not isinstance(proto, LTable) and \
                any(isinstance(x, Missing) for x in walk_expr(proto)):
            # the child proto is requested already; walking on finds the
            # constants the rest of this function needs in the same round
            # (stopping here asked for one closure per round: a long chain)
            return Missing(None)
        if not isinstance(proto, LTable):
            raise Unsupported("closure of non-proto")
        entries = []
        if isinstance(ups, LTable):
            for i in range(1, ups.length() + 1):
                entries.append(ups.get(i))
        c = ClosureExpr(proto, entries)
        c.vm = vm
        for e in entries:
            if isinstance(e, MaybeBox):
                self.captured_regs.add(e.reg)
            if isinstance(e, LTable):
                for v in e.h.values():
                    if isinstance(v, int) and any(isinstance(x, RegFile) for x in e.h.values()):
                        self.captured_regs.add(v)
        self.children.append(c)
        return c


def lst_nkey(lst):
    return lst.nkey if lst.nkey is not None else b"n"


def pad(items, n):
    items = list(items[:n])
    while len(items) < n:
        items.append(None)
    return items


class OpenUps:
    """Luraph's table of open upvalue boxes (register -> box). Reads give a
    MaybeBox (a by-reference capture of that register); storing nil into it
    is the close op: the captured local's scope ends there."""


OPENUPS = OpenUps()


class MaybeBox:
    def __init__(self, reg):
        self.reg = reg

    def __repr__(self):     # (stable: structure.merge_equivalent compares text)
        return "box(r%s)" % self.reg


class UpList:
    """The upvalue list of the proto being lifted. y[i] is a BoxProxy, or a
    FrameProxy for the upvalues that hold the parent's whole register frame."""

    def __init__(self, frames=()):
        self.boxes = {}
        self.frames = set(frames)

    def get(self, i):
        b = self.boxes.get(i)
        if b is None:
            b = self.boxes[i] = FrameProxy(i) if i in self.frames else BoxProxy(i)
        return b


REGFILE = RegFile()

# `s[k] = s`: a register holding the VM frame itself (jvals marker). Closures
# capture it by value and read the parent's locals as upv[i][reg].
FRAME = "<frame>"


class FrameProxy:
    """Upvalue i holding the parent's register frame: upv[i][r] is the
    parent's register r (Upval((i, r)))."""

    def __init__(self, idx):
        self.idx = idx

    def __repr__(self):
        return "frameproxy(%s)" % (self.idx,)


class BoxProxy:
    """Upvalue i. Luraph keeps shared upvalues in boxes read as box[a][box[b]];
    by-value upvalues are used directly (y[i], y[i][k])."""

    def __init__(self, idx):
        self.idx = idx

    def __repr__(self):
        return "boxproxy(%s)" % (self.idx,)


class BoxPart(Expr):
    """box[k] of upvalue `idx`: either half of a box access, or (if used any
    other way) the by-value upvalue indexed with constant k."""

    def __init__(self, idx, k):
        self.idx, self.k = idx, k


def walk_expr(e):
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, Expr):
            yield x
            stack += [v for v in x.__dict__.values() if isinstance(v, Expr)]
            if isinstance(x, S.NewTable):
                stack += [y for kv in x.items for y in kv if isinstance(y, Expr)]


# ---- register facts for the constant propagation in Program._walk

def meet(a, b):
    """Facts true on both paths: equal facts stay; a constant and a
    truthiness (or two constants) that agree on truthiness give that truthiness."""
    out = {}
    for r, f in a.items():
        g = b.get(r)
        if g is None:
            continue
        if g == f:
            out[r] = f
            continue
        ta, tb = truth_of(f), truth_of(g)
        if ta is not None and ta == tb:
            out[r] = ("t",) if ta else ("f",)
    return out


def fact_of(value):
    """Fact for a register assigned `value` (an IR expression)."""
    if isinstance(value, Const):
        v = value.v
        if isinstance(v, (int, float, bytes, bool)) or v is None:
            return ("c", v)
    if isinstance(value, ClosureExpr):
        return ("t", value)     # (frame_call evaluates calls of it)
    if isinstance(value, (S.NewTable, Vec, Opaque)):
        return ("t",)
    return None


def eval_fact(e, facts):
    """Concrete value of an IR expression under the facts, or a truthiness
    ("t"/"f"), or None when unknown."""
    if isinstance(e, Const):
        return ("c", e.v)
    if isinstance(e, Reg):
        return facts.get(e.n)
    if isinstance(e, Un) and e.op == "Not":
        a = eval_fact(e.a, facts)
        t = truth_of(a)
        return None if t is None else ("c", not t)
    if isinstance(e, Bin) and e.op.startswith("Compare"):
        a, b = eval_fact(e.a, facts), eval_fact(e.b, facts)
        if a and b and a[0] == "c" and b[0] == "c":
            try:
                x, y = a[1], b[1]
                if e.op == "CompareEq":
                    return ("c", S.lua_eq(x, y))
                if e.op == "CompareNe":
                    return ("c", not S.lua_eq(x, y))
                if isinstance(x, bool) or isinstance(y, bool) or x is None or y is None:
                    return None
                if isinstance(x, bytes) != isinstance(y, bytes):
                    return None
                return ("c", {"CompareLt": x < y, "CompareLe": x <= y, "CompareGt": x > y,
                              "CompareGe": x >= y}[e.op])
            except TypeError:
                return None
    return None


def truth_of(f):
    if f is None:
        return None
    if f[0] == "c":
        return S.truthy(f[1])
    return f[0] == "t"


def edge_facts(cond, taken, facts):
    """Facts implied by taking one side of a branch on `cond`."""
    f = dict(facts)
    c = cond
    neg = False
    while isinstance(c, Un) and c.op == "Not":
        c, neg = c.a, not neg
    t = taken != neg
    if isinstance(c, Reg):
        if c.n not in f or f[c.n][0] != "c":
            f[c.n] = ("t",) if t else ("f",)
    elif isinstance(c, Bin) and c.op in ("CompareEq", "CompareNe"):
        eq = t if c.op == "CompareEq" else not t
        if eq:
            if isinstance(c.a, Reg) and isinstance(c.b, Const):
                f[c.a.n] = ("c", c.b.v)
            elif isinstance(c.b, Reg) and isinstance(c.a, Const):
                f[c.b.n] = ("c", c.a.v)
    return f


def apply_stmt_facts(st, facts, lf):
    if isinstance(st, Assign) and isinstance(st.target, Reg):
        fv = fact_of(st.value)
        if fv is None and isinstance(st.value, Reg):
            fv = facts.get(st.value.n)
        if fv is None:
            facts.pop(st.target.n, None)
        else:
            facts[st.target.n] = fv
    elif isinstance(st, CallStmt):
        if any(isinstance(x, FrameArg) for x in st.args.items):
            writes = frame_call(st, facts, lf)
            prev = getattr(st, "frame_eval", None)
            if writes is None or (prev is not None and prev != writes):
                st.frame_eval = False
            elif prev is None:
                st.frame_eval = writes
            if not st.frame_eval:
                facts.clear()       # it may write any register
                return
            for r, v in st.frame_eval.items():
                facts[r] = ("c", v)
        # a call can change registers captured by closures (upvalue boxes)
        for r in list(facts):
            if r in lf.captured_regs:
                del facts[r]


def frame_call(st, facts, lf):
    """A call that gets the caller's register frame (FrameArg), of a closure
    without upvalues, all other arguments constant: run it in the runtime on
    a fresh table ("!proto!args" request, envlog callPath). -> {register:
    value} it wrote (LPH_ENCSTR-style decryptors: the plaintext), or None."""
    if isinstance(st.fn, ClosureExpr):
        c = st.fn
    else:
        f = eval_fact(st.fn, facts) if isinstance(st.fn, Reg) else None
        c = f[1] if f and f[0] == "t" and len(f) > 1 else None
    if not isinstance(c, ClosureExpr) or c.upvals or not isinstance(c.proto, LTable) or st.args.tail is not None:
        return None
    path = lf.dump.paths().get(c.proto.tid)
    if path is None:
        return None
    specs = []
    for x in st.args.items:
        v = eval_fact(x, facts) if not isinstance(x, FrameArg) else ("F",)
        if v is None or v[0] not in ("c", "F"):
            return None
        if v[0] == "F":
            specs.append("F")
        elif v[1] is None:
            specs.append("z")
        elif isinstance(v[1], bool):
            specs.append("t" if v[1] else "f")
        elif isinstance(v[1], bytes):
            specs.append("s" + v[1].hex())
        elif isinstance(v[1], (int, float)) and v[1] == v[1] and abs(v[1]) != float("inf"):
            specs.append("n" + S.fmt_num(v[1]))
        else:
            return None
    rq = "!%s!%s" % ("~".join(str(x) for x in path), "/".join(specs))
    got = lf.dump.overrides.get(rq)
    if got is None:
        lf.requests.add(rq)
        got = lf.dump.fetch(rq)
    if not isinstance(got, LTable):
        return None
    out = {}
    for k, v in got.h.items():
        if not isinstance(k, int) or not isinstance(v, (bytes, int, float, bool)):
            return None
        out[k] = v
    c.frame_evaluated = True    # (codegen.drop_dead_packs drops it once unused)
    return out


def drop_idle_closes(order, captured):
    """Close ops of registers no closure of this function captures: no-ops
    (Luraph closes whole ranges), but they would keep otherwise identical
    copies of an instruction apart (structure.merge_equivalent)."""
    stack = [n for _, n in order]
    while stack:
        n = stack.pop()
        if n is None:
            continue
        if any(isinstance(x, Close) and x.reg not in captured for x in n.stmts):
            n.stmts = [x for x in n.stmts if not (isinstance(x, Close) and x.reg not in captured)]
        stack += [n.then, n.els]


def apply_frame_calls(order):
    """Evaluated frame-writing calls (frame_call) -> the register writes."""
    stack = [n for _, n in order]
    while stack:
        n = stack.pop()
        if n is None:
            continue
        if any(getattr(x, "frame_eval", None) for x in n.stmts):
            new = []
            for x in n.stmts:
                w = getattr(x, "frame_eval", None)
                if w:
                    new += [Assign(Reg(r), Const(v)) for r, v in sorted(w.items())]
                else:
                    new.append(x)
            n.stmts = new
        stack += [n.then, n.els]


def propagate(node, facts, succ, lf):
    """Walk one instruction's IR tree under the facts, collecting feasible
    successors with their facts."""
    stack = [(node, facts)]
    while stack:
        n, f = stack.pop()
        if n is None:
            continue
        for st in n.stmts:
            apply_stmt_facts(st, f, lf)
        if n.cond is not None:
            v = truth_of(eval_fact(n.cond, f))
            n.decided = getattr(n, "decided", "unset")
            if v is None:
                n.decided = None
                stack.append((n.then, edge_facts(n.cond, True, f)))
                stack.append((n.els, edge_facts(n.cond, False, f)))
            else:
                if n.decided == "unset":
                    n.decided = v
                elif n.decided is not None and n.decided != v:
                    n.decided = None
                stack.append((n.then if v else n.els, f))
        elif isinstance(n.outcome, Next):
            succ.append((n.outcome.state, f))
    return None


def expr_regs(e):
    """Registers read by an expression."""
    out = []
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, Reg):
            out.append(x)
        elif isinstance(x, Expr):
            stack += [v for v in x.__dict__.values() if isinstance(v, Expr)]
            if isinstance(x, S.NewTable):
                stack += [y for kv in x.items for y in kv if isinstance(y, Expr)]
    return out


class GenIterMaker:
    """coroutine.wrap(helper) of Luraph's generic-for: called once with
    (vm, f, s, ctl); then stored as the loop state and called per iteration."""

    def __init__(self):
        self.args = None


# --------------------------------------------------------------------------
# stepping

class _AccessLog(dict):
    """A scope's variables that remember which ones were read before being
    written, and which were written (Stepper.carry)."""
    __slots__ = ("read_first", "written")

    def __init__(self, *a):
        super().__init__(*a)
        self.read_first = set()
        self.written = set()

    def __getitem__(self, k):
        if k not in self.written:
            self.read_first.add(k)
        return dict.__getitem__(self, k)

    def __setitem__(self, k, v):
        self.written.add(k)
        dict.__setitem__(self, k, v)


class Stepper:
    def __init__(self, vm, lifter):
        self.vm = vm
        self.lf = lifter
        cs = lifter.initial_state()
        self.cs = cs
        # locate mode / pc variables from the dispatch loops
        self.loops = []   # (index in inner body, if-node, while-node)
        for i, st in enumerate(vm.inner_body):
            if st["type"] == "AstStatIf":
                tb = st["thenbody"]["body"]
                if tb and tb[0]["type"] in ("AstStatWhile", "AstStatRepeat") and vm.is_dispatch(tb[0]):
                    self.loops.append((i, st, tb[0]))
        self.mode_decl = None
        if not self.loops:
            # small scripts: Luraph emits only the opcodes used, sometimes all
            # in one mode, and then the loop sits in the function without a
            # mode `if` (mode is always 0 then)
            for i, st in enumerate(vm.inner_body):
                if st["type"] in ("AstStatWhile", "AstStatRepeat") and vm.is_dispatch(st):
                    self.loops.append((i, None, st))
                    break
        if not self.loops:
            raise Unsupported("no dispatch loops in the VM function")
        w = self.loops[0][2]
        # v14.x frequently parenthesizes the opcode fetch:
        #     local op = (OPS[PC])
        # luau-ast represents that as AstExprGroup, unlike many v15 samples.
        # Do not index the raw node directly; normalize parser-only wrappers
        # first and validate the shape so malformed matches fail clearly.
        first = w["body"]["body"][0]
        vals = first.get("values") or []
        if not vals:
            raise Unsupported("dispatch loop has no opcode fetch value")
        fetch = vmmap.unwrap(vals[0])
        if not isinstance(fetch, dict) or fetch.get("type") != "AstExprIndexExpr":
            raise Unsupported("unrecognized v14.x opcode fetch shape")
        pc_expr = vmmap.unwrap(fetch.get("index"))
        if not isinstance(pc_expr, dict) or pc_expr.get("type") != "AstExprLocal":
            raise Unsupported("v14.x opcode PC is not a local")
        pcname = pc_expr["local"]
        self.pc_decl = pcname["location"]
        # mode test of each loop: `if MODE==K then`, or `if a then` with
        # `local a = MODE==K` earlier in the loop function (evaluated here
        # directly, since the state's mode is set after the prologue ran)
        self.conds = {}
        for i, st, _ in self.loops:
            if st is None:
                continue
            cond = st["condition"]
            if cond["type"] == "AstExprLocal":
                cond = self._local_value(cond["local"]["location"], i) or cond
            self.conds[i] = cond
            if self.mode_decl is None and cond["type"] == "AstExprBinary":
                mv = cond["left"] if cond["left"]["type"] == "AstExprLocal" else cond["right"]
                self.mode_decl = mv["local"]["location"]
        self.first_inner = self.loops[0][0]
        self.gov = Overlay()
        # Loop-function locals that carry a value from one instruction to the
        # next (a stack VM's stack pointer: `local M=G` in the prologue,
        # handlers `M+=1;R[M]=...`). Found while walking: a prologue local a
        # handler reads before writing it and some handler writes, holding
        # an integer. Their values are part of the state (State.locs); a new
        # one restarts the walk (`new_carry`, like a new jump register).
        self.carry = set()
        self.read_first = set()
        self.written = set()
        self.not_carried = set()
        self.new_carry = False
        self.fixed_decls = {d for d in (self.pc_decl, self.mode_decl, vm.kstack_key) if d}
        self.sp_cands = self._stack_pointer_candidates()

    def _stack_pointer_candidates(self):
        """Prologue locals the handlers use directly as a register index
        (`R[M]`): only these can be a stack pointer. (A register VM's
        multret top is carried too, but the lifter models it otherwise.)"""
        # (per VM: every function of the VM runs the same loop function)
        cache = self.vm.__dict__.setdefault("_sp_cands", {})
        if None not in cache:
            # every local indexing a local: `x[y]` (which x is the register file is per call)
            pairs = set()
            for _, _, w in self.loops:
                for n in iter_nodes(w):
                    if n.get("type") == "AstExprIndexExpr" and n["expr"].get("type") == "AstExprLocal" \
                            and n["index"].get("type") == "AstExprLocal":
                        pairs.add((n["expr"]["local"]["location"], n["index"]["local"]["location"]))
            cache[None] = pairs
        _, inner = self._fresh_scopes(None, S.Interp(self.lf))
        self.lf.out = []
        regfiles = {k for k, v in inner.vars.items() if isinstance(v, RegFile)}
        return {i for r, i in cache[None] if r in regfiles} & set(inner.vars)

    def _local_value(self, loc, before):
        """The expression a local of the loop function is declared with."""
        for st in self.vm.inner_body[:before]:
            if st["type"] != "AstStatLocal":
                continue
            for k, v in enumerate(st["vars"]):
                if v["location"] == loc and k < len(st["values"]):
                    return st["values"][k]
        return None

    def initial(self):
        it = S.Interp(self.lf)
        cs, inner = self._fresh_scopes(None, it)
        pc = inner.lookup(self.pc_decl).vars[self.pc_decl]
        mode = inner.lookup(self.mode_decl).vars[self.mode_decl] if self.mode_decl else 0
        ks = inner.lookup(self.vm.kstack_key) if self.vm.kstack_key else None
        locs = self._carried(inner)
        if locs:
            # a carried local indexes the registers: a stack pointer, whose
            # initial value is the frame size (the slots above: operand stack)
            self.lf.stack_base = min(v for _, v in locs)
        return State(mode, pc, ks.vars[self.vm.kstack_key] if ks else None, locs=locs)

    def _carried(self, inner):
        """State.locs: the carried locals' current values."""
        out = []
        for k in sorted(self.carry):
            v = inner.vars.get(k)
            if not (isinstance(v, int) and not isinstance(v, bool)):
                raise Unsupported("symbolic value of a VM local carried between instructions (%r)" % (v,))
            out.append((k, v))
        return tuple(out)

    def _fresh_scopes(self, state, it):
        """Scopes at the top of the loop function, before the first loop;
        pc / mode / loop stack set from `state` (None: initial values)."""
        cs = Scope(self.cs.parent)
        cs.vars = dict(self.cs.vars)
        inner = Scope(cs)
        inner.vars["..."] = cs.vars["..."]
        self.lf.cur_scope = inner
        self.lf.in_prologue = True
        it.exec_block(self.vm.inner_body[:self.first_inner], inner)
        self.lf.in_prologue = False
        if state is not None:
            inner.lookup(self.pc_decl).vars[self.pc_decl] = state.pc
            if self.mode_decl:
                inner.lookup(self.mode_decl).vars[self.mode_decl] = state.mode
            if self.vm.kstack_key:
                inner.lookup(self.vm.kstack_key).vars[self.vm.kstack_key] = state.kstack
            for k, v in state.locs:
                inner.vars[k] = v
        return cs, inner

    def run_once(self, state, decisions, tprefix):
        lf = self.lf
        lf.out = []
        lf.tcount = 0
        lf.temp_prefix = tprefix
        lf.mutated = False
        lf.jvals = dict(state.jregs) if state is not None else {}
        lf.jread = set()
        # one overlay per proto: Luraph's in-place decryptors dominate the code
        # they decrypt, so applying them in visiting order is what the VM does
        lf.ov_base = self.gov
        lf.ov = None
        lf.packs = dict(state.packs) if state is not None else {}
        lf.pack_copies = {}
        lf.pack_read = set()
        it = S.Interp(lf)
        it.decisions = list(decisions)
        cs, inner = self._fresh_scopes(state, it)
        inner.vars = acc = _AccessLog(inner.vars)
        loop_i = None
        for i, st, w in self.loops:
            if st is None or S.truthy(it.eval(self.conds[i], inner)):
                loop_i = (i, st, w)
                break
        if loop_i is None:
            raise Unsupported("mode %r selects no dispatch loop" % (state.mode,))
        i, st, w = loop_i
        try:
            lf.last_op = (state.mode, it.eval(w["body"]["body"][0]["values"][0], inner))
        except Unsupported:
            lf.last_op = (state.mode, None)
        outcome = None
        try:
            try:
                it.exec_block(w["body"]["body"], Scope(inner))
                outcome = ("next",)
            except BreakSig:
                # rest of the loop's if-body, then the following statements
                try:
                    if st is not None:
                        it.exec_block(st["thenbody"]["body"][1:], Scope(inner))
                    it.exec_block(self.vm.inner_body[i + 1:], inner)
                    outcome = ("ret", Multi([]))
                except YieldSig:
                    outcome = ("next",)
        except VMCrash:
            return it, Crash()
        except ReturnSig as r:
            if self.vm.post is None:
                outcome = ("ret", r.values)
            else:
                outcome = ("ret", self.post_return(it, cs, r.values))
        if outcome[0] == "ret" and outcome is not None and len(outcome) == 2 and outcome[1] is None:
            outcome = ("ret", Multi([]))
        if outcome[0] == "ret":
            m = outcome[1] if isinstance(outcome[1], Multi) else Multi([outcome[1]])
            outcome = ("ret", Multi([lf.value_of(x) if not isinstance(x, SymList) else x for x in m.items], m.tail))
        self._note_access(acc)
        if outcome[0] == "next":
            def get(k):
                return inner.lookup(k).vars[k]
            locs = self._carried(inner)
            sb = lf.stack_base
            if sb is not None and locs:
                # operand stack slots: a value stays known while it is on the
                # stack (reads peek, they don't consume it); above the top it is dead
                top = max(v for _, v in locs)
                jr = tuple(sorted((k, v) for k, v in lf.jvals.items() if k not in lf.jread
                                  and not (isinstance(k, int) and k > top)))
            else:
                jr = tuple(sorted((k, v) for k, v in lf.jvals.items() if k not in lf.jread))
            nxt = State(get(self.mode_decl) if self.mode_decl else 0, get(self.pc_decl), get(self.vm.kstack_key) if self.vm.kstack_key else None,
                        jr, None, lf.state_packs(), locs)
            return it, Next(nxt)
        return it, Ret(outcome[1])

    def _note_access(self, acc):
        """Collect which prologue locals handlers read first / write; a new
        carried local (see __init__) sets `new_carry`."""
        if getattr(self, "no_carry", False):
            return
        self.read_first |= acc.read_first
        self.written |= acc.written
        for k in (self.read_first & self.written & self.sp_cands) - self.carry - self.not_carried - self.fixed_decls:
            v = dict.get(acc, k)
            if k in self.lf.special or not (isinstance(v, int) and not isinstance(v, bool)):
                self.not_carried.add(k)
                continue
            self.carry.add(k)
            self.new_carry = True

    def post_return(self, it, cs, values):
        """The handler returned from the protected function: run the code after it."""
        vals = it.adjust(values, 4)
        ps = Scope(cs)
        names = self.vm.tstat["vars"]
        ps.vars[names[0]["location"]] = True
        for v, x in zip(names[1:], vals):
            ps.vars[v["location"]] = x
        try:
            it.exec_block(self.vm.post, ps)
        except ReturnSig as r:
            return r.values
        return Multi([])

    def step(self, state, tprefix):
        """All paths of one instruction -> Node tree. Decoders re-dispatch."""
        for _ in range(8):
            paths = []
            writes = None
            todo = [[]]
            while todo:
                dec = todo.pop()
                it, oc = self.run_once(state, dec, tprefix)
                if len(paths) > 64:
                    raise Unsupported("too many paths in one instruction")
                taken = [d[3] for d in it.dlog]
                for j in range(len(dec), len(taken)):
                    todo.append(taken[:j] + [not taken[j]])
                paths.append((taken, it.dlog, list(self.lf.out), oc))
                if len(paths) == 1:
                    writes = self.lf.ov
            if writes is not None:
                # commit this instruction's in-place writes (decryption) once
                self.gov.d.update(writes.d)
                dump = self.lf.dump
                for k, v in writes.d.items():
                    if k[0] in dump.buf_loc and isinstance(k[1], int):
                        dump.buf_patch[k] = v
                    elif k[0] in dump.tid_of and k[0] not in self.lf.proto_arrays and                             isinstance(k[1], int) and isinstance(v, (int, float)) and not isinstance(v, bool):
                        dump.tab_patch[(dump.tid_of[k[0]], k[1])] = v
            if len(paths) == 1 and not paths[0][2] and isinstance(paths[0][3], Next) \
                    and self.lf.mutated and paths[0][3].state.pc == state.pc:
                # a decoder rewrote this instruction: dispatch it again
                state = paths[0][3].state
                continue
            node = build_tree(paths, 0, 0)
            node.op = self.lf.last_op
            return node
        raise Unsupported("instruction keeps re-decoding itself")


JIT_ENTRY = -(1 << 40)     # pc of a JIT function's entry: its prologue (JitStepper)
JIT_TMP = 900000           # registers for parallel assignments (ProtoLifter.parallel_values)


def jit_maker_parts(node):
    """LPH_JIT functions are VM-object methods `function(g, upvals, P) local
    W = P[P[k]]; return function(params) <prologue> while c do <if tree on
    a state variable> end end`: plain Lua (a control-flow-flattened state
    machine over the constant array W), not bytecode. -> (index of the proto
    parameter, the inner function) for such a maker, else None."""
    if not isinstance(node, dict) or node.get("type") != "AstExprFunction":
        return None
    body = node["body"]["body"]
    if len(body) != 2 or body[0]["type"] != "AstStatLocal" or body[1]["type"] != "AstStatReturn":
        return None
    vals, ret = body[0]["values"], body[1]["list"]
    if len(vals) != 1 or len(ret) != 1 or ret[0]["type"] != "AstExprFunction":
        return None
    v = vmmap.unwrap(vals[0])
    if not isinstance(v, dict) or v.get("type") != "AstExprIndexExpr":
        return None
    base = vmmap.unwrap(v.get("expr"))
    idx = vmmap.unwrap(v.get("index"))
    if not isinstance(base, dict) or base.get("type") != "AstExprLocal":
        return None
    if not isinstance(idx, dict) or idx.get("type") != "AstExprIndexExpr":
        return None
    ibase = vmmap.unwrap(idx.get("expr"))
    if not isinstance(ibase, dict) or ibase.get("type") != "AstExprLocal":
        return None
    p = base["local"]["location"]
    if ibase["local"]["location"] != p:
        return None
    pis = [i for i, a in enumerate(node["args"]) if a["location"] == p]
    inner = ret[0]
    if not pis or not any(st["type"] == "AstStatWhile" for st in inner["body"]["body"]):
        return None
    return pis[-1], inner


class JitModel(VMModel):
    """An LPH_JIT function (jit_maker_parts), lifted like a one-mode VM: one
    pass of its dispatch loop is an instruction, the state variable is the
    pc, and its parameters and the locals of its prologue are registers
    (except those holding a fixed value, see JitStepper). Registered as a
    sibling maker: the closure op that calls this maker makes a ClosureExpr
    with this model."""

    def __init__(self, maker, ctor, pi, inner):
        self.info = {"maker": maker, "vm": inner, "proto_index": pi, "upvals_index": 1}
        self.maker, self.vm, self.ctor_funcs = maker, inner, ctor
        self.maker_decls = {}
        self.inner = inner
        self.inner_body = inner["body"]["body"]
        self.prologue, self.tstat, self.post = [], None, None
        self.kstack_key = self.kstack_link = None
        self.wi = next(i for i, st in enumerate(self.inner_body) if st["type"] == "AstStatWhile")
        w = self.inner_body[self.wi]
        self.dispatch = {id(w)}
        c = w["condition"]
        self.cond_decl = c["local"]["location"] if c["type"] == "AstExprLocal" else None
        self.pc_decl = None
        for st in w["body"]["body"]:
            if st["type"] == "AstStatIf":
                c = st["condition"]
                if c["type"] == "AstExprBinary" and c["left"]["type"] == "AstExprLocal":
                    self.pc_decl = c["left"]["local"]["location"]
                break
            if st["type"] != "AstStatLocal" or st["values"]:
                break
        if self.pc_decl is None:
            raise Unsupported("LPH_JIT function without a state dispatch")
        self.assigned = set()       # locals the loop assigns
        for n in iter_nodes(w):
            if n.get("type") == "AstStatAssign":
                self.assigned |= {v["local"]["location"] for v in n["vars"] if v["type"] == "AstExprLocal"}
            elif n.get("type") == "AstStatCompoundAssign" and n["var"]["type"] == "AstExprLocal":
                self.assigned.add(n["var"]["local"]["location"])
        self.params = [a["location"] for a in inner["args"]]
        self.locals = [v["location"] for st in self.inner_body[:self.wi] if st["type"] == "AstStatLocal"
                       for v in st["vars"]]
        # the loop stack: a prologue local that table constructors link to
        # (`R = {nil, N, limit, start - step, step}; N = R`)
        self.jstack = None
        for n in iter_nodes(w):
            if n.get("type") == "AstExprTable":
                for it in n["items"]:
                    v = it["value"]
                    if v["type"] == "AstExprLocal" and v["local"]["location"] in self.locals:
                        self.jstack = v["local"]["location"]
        # locals every step writes before reading them (Luraph reuses
        # parameters and dead locals as scratch space) are values within one
        # step, not registers
        live = _jit_live_in(w, self.pc_decl, set(self.params + self.locals))
        self.special = {}
        if self.jstack is not None:
            self.special[self.jstack] = ("jstack",)
        for loc in self.params + self.locals:
            if loc not in (self.pc_decl, self.cond_decl) and loc not in self.special and loc in live:
                self.special[loc] = ("reg", len(self.special) + 1)


class JitFrame(LTable):
    """One entry of an LPH_JIT function's loop stack (`N = {..., N, ...}`,
    the link slot varies per loop): its other slots are Pseudo variables of
    that depth, like the VM's loop stack K. JIT_BOTTOM is the empty stack."""
    __slots__ = ("link", "depth")

    def __init__(self, link, depth):
        LTable.__init__(self)
        self.link, self.depth = link, depth


JIT_BOTTOM = JitFrame(None, 0)


class JitProto(LTable):
    """The "proto" of a function an LPH_JIT function defines (a Lua closure,
    itself a state machine): where it was made (env) and which outer locals
    it uses as upvalues (upmap: declaration -> upvalue index)."""
    __slots__ = ("env", "upmap")

    def __init__(self, env, upmap):
        LTable.__init__(self)
        self.env, self.upmap = env, upmap


_JIT_NESTED = {}
_JIT_TAGGED = {}       # tag -> JitModel of a nested function (collect_requests)


def _jit_nested_model(node):
    if id(node) not in _JIT_NESTED:
        try:
            jm = JitModel(None, {}, None, node)
            jm.tag = "jit-nested@%s" % (node.get("location"),)
            _JIT_TAGGED[jm.tag] = jm
            _JIT_NESTED[id(node)] = (node, jm)
        except (Unsupported, StopIteration, KeyError):
            _JIT_NESTED[id(node)] = (node, None)
    return _JIT_NESTED[id(node)][1]


def _declared_in(node):
    out = {a["location"] for a in node.get("args", [])}
    for n in iter_nodes(node):
        t = n.get("type")
        if t in ("AstStatLocal", "AstStatForIn"):
            out |= {v["location"] for v in n["vars"]}
        elif t == "AstStatFor":
            out.add(n["var"]["location"])
        elif t == "AstStatLocalFunction":
            out.add(n["name"]["location"])
        elif t == "AstExprFunction":
            out |= {a["location"] for a in n["args"]}
    return out


def _jit_live_in(w, pc_decl, cands):
    """Candidates (declarations) some step of the dispatch loop `w` reads
    before it assigns them, or that a function made inside reads. A step is
    the loop body's statements before the dispatch `if` plus one leaf of the
    `if pc <= K` tree."""
    live = set()

    def is_dispatch(st):
        c = st.get("condition") if st.get("type") == "AstStatIf" else None
        return c is not None and c["type"] == "AstExprBinary" and c["left"]["type"] == "AstExprLocal" \
            and c["left"]["local"]["location"] == pc_decl

    def expr(e, done):
        for n in iter_nodes(e):
            t = n.get("type")
            if t == "AstExprLocal" and n["local"]["location"] in cands and n["local"]["location"] not in done:
                live.add(n["local"]["location"])
            elif t == "AstExprFunction":
                live.update(x["local"]["location"] for x in iter_nodes(n)
                            if x.get("type") == "AstExprLocal" and x["local"]["location"] in cands)

    def block(stmts, done):
        done = set(done)
        for st in stmts:
            t = st["type"]
            if t == "AstStatLocal":
                for v in st["values"]:
                    expr(v, done)
            elif t == "AstStatAssign":
                for v in st["values"]:
                    expr(v, done)
                for v in st["vars"]:
                    if v["type"] != "AstExprLocal":
                        expr(v, done)
                for v in st["vars"]:
                    if v["type"] == "AstExprLocal":
                        done.add(v["local"]["location"])
            elif t == "AstStatCompoundAssign":
                expr(st["var"], done)
                expr(st["value"], done)
            elif t == "AstStatIf":
                expr(st["condition"], done)
                a = block(st["thenbody"]["body"], done)
                e = st.get("elsebody")
                if e is None:
                    b = done
                elif e["type"] == "AstStatIf":
                    b = block([e], done)
                else:
                    b = block(e["body"], done)
                done = a & b
            elif t in ("AstStatWhile", "AstStatRepeat"):
                expr(st["condition"], done)
                block(st["body"]["body"], done)
            elif t == "AstStatFor":
                for k in ("from", "to", "step"):
                    if st.get(k):
                        expr(st[k], done)
                block(st["body"]["body"], done)
            elif t == "AstStatForIn":
                for v in st["values"]:
                    expr(v, done)
                block(st["body"]["body"], done)
            elif t == "AstStatBlock":
                done = block(st["body"], done)
            else:
                expr(st, done)
        return done

    def leaves(stmts, done):
        # the dispatch tree: its branches are further dispatch or leaves
        if len(stmts) == 1 and is_dispatch(stmts[0]):
            st = stmts[0]
            leaves(st["thenbody"]["body"], done)
            e = st.get("elsebody")
            if e is not None:
                leaves([e] if e["type"] == "AstStatIf" else e["body"], done)
        else:
            block(stmts, done)

    body = w["body"]["body"]
    i = next((k for k, st in enumerate(body) if is_dispatch(st)), len(body))
    done = block(body[:i], set())
    leaves(body[i:i + 1], done)
    if i + 1 < len(body):
        block(body[i + 1:], set())
    expr(w["condition"], set())
    return live


def _fixed_value(v):
    """A prologue local's value that is the same on every entry (the
    environment, library functions, constants, dump tables): kept as a value."""
    if v is None or isinstance(v, (bool, int, float, bytes, EnvTable, Builtin, OpaqueFn, LuaFunc,
                                   UpList, BoxProxy, FrameProxy)):
        return True
    if isinstance(v, LTable):
        return v.tid is not None
    if isinstance(v, SymList):
        return not v.items and v.tail is None
    return False


class JitStepper(Stepper):
    """Stepper for a JitModel. The entry (pc JIT_ENTRY) runs the prologue
    and assigns the registers; every other step runs the prologue again
    only to rebuild the fixed values, then one pass of the loop body."""

    def __init__(self, vm, lifter):
        self.vm = vm
        self.lf = lifter
        self.cs = lifter.initial_state()
        self.loops = [(vm.wi, None, vm.inner_body[vm.wi])]
        self.mode_decl = None
        self.pc_decl = vm.pc_decl
        self.conds = {}
        self.first_inner = vm.wi
        self.gov = Overlay()
        lifter.special = dict(vm.special)
        if isinstance(lifter.proto, JitProto):
            for loc, k in lifter.proto.upmap.items():
                lifter.special[loc] = ("upval", k)
        lifter.out = []
        _, inner = self._fresh_scopes(None, S.Interp(lifter))
        for loc in vm.locals:
            if loc in lifter.special and loc not in vm.assigned and _fixed_value(inner.vars.get(loc)):
                del lifter.special[loc]
        lifter.out = []

    def _fresh_scopes(self, state, it, entry=False):
        vm, lf = self.vm, self.lf
        cs = Scope(self.cs.parent)
        cs.vars = dict(self.cs.vars)
        inner = Scope(cs)
        lf.in_prologue = not entry
        lf.jstack = JIT_BOTTOM
        for i, loc in enumerate(vm.params, 1):
            inner.vars[loc] = Vararg(i)
            if lf.special.get(loc):
                lf.special_set(lf.special[loc], Vararg(i), it)
        if vm.inner.get("vararg"):
            inner.vars["..."] = Multi([], VarargTail(len(vm.params) + 1))
        lf.cur_scope = inner
        it.exec_block(vm.inner_body[:vm.wi], inner)
        lf.in_prologue = False
        if state is not None and isinstance(state.kstack, JitFrame):
            lf.jstack = state.kstack
        if not entry and state is not None:
            inner.lookup(self.pc_decl).vars[self.pc_decl] = state.pc
        return cs, inner

    def initial(self):
        return State(0, JIT_ENTRY, JIT_BOTTOM)

    def step(self, state, tprefix):
        node = Stepper.step(self, state, tprefix)
        _jit_forloop(node, self.lf)
        return node

    def run_once(self, state, decisions, tprefix):
        lf = self.lf
        vm = self.vm
        lf.out = []
        lf.tcount = 0
        lf.temp_prefix = tprefix
        lf.mutated = False
        lf.jvals = dict(state.jregs)
        lf.jread = set()
        lf.ov_base = self.gov
        lf.ov = None
        lf.packs = dict(state.packs)
        lf.pack_copies = {}
        lf.pack_read = set()
        it = S.Interp(lf)
        it.decisions = list(decisions)
        lf.last_op = (0, state.pc)
        entry = state.pc == JIT_ENTRY
        try:
            cs, inner = self._fresh_scopes(state, it, entry)
            if not entry:
                lf.out = []         # (the prologue's statements belong to the entry)
                ended = False
                try:
                    it.exec_block(vm.inner_body[vm.wi]["body"]["body"], Scope(inner))
                except ContinueSig:
                    pass
                except BreakSig:
                    ended = True
                if not ended and vm.cond_decl is not None:
                    cv = inner.lookup(vm.cond_decl).vars[vm.cond_decl]
                    if is_sym(cv):
                        raise Unsupported("symbolic LPH_JIT loop condition")
                    ended = not S.truthy(cv)
                if ended:
                    it.exec_block(vm.inner_body[vm.wi + 1:], inner)
                    raise ReturnSig(Multi([]))
        except VMCrash:
            return it, Crash()
        except ReturnSig as r:
            m = r.values if isinstance(r.values, Multi) else Multi([r.values])
            return it, Ret(Multi([lf.value_of(x) if not isinstance(x, SymList) else x for x in m.items], m.tail))
        pc = inner.lookup(self.pc_decl).vars[self.pc_decl]
        jr = tuple(sorted((k, v) for k, v in lf.jvals.items() if k not in lf.jread))
        return it, Next(State(0, pc, lf.jstack, jr, None,
                              lf.state_packs()))


def _jit_forloop(node, lf):
    """An LPH_JIT numeric-for header (`c, s, l = N[..]; u = c + s; N[c] = u;
    if (s <= 0 and u >= l) or (s > 0 and u <= l) then var = u; body else
    exit`) in the shape of the VM's FORLOOP handler (loops.try_numeric):
    `c = c + s; if s <= 0 then (if c >= l ...) else (if c <= l ...)`."""
    c0 = node.cond
    if node.stmts or not (isinstance(c0, Bin) and c0.op == "CompareLe" and isinstance(c0.a, Pseudo)
                          and isinstance(c0.b, Const) and c0.b.v == 0):
        return
    step = c0.a
    found = None
    for side, op in ((node.then, "CompareGe"), (node.els, "CompareLe")):
        cc = getattr(side, "cond", None)
        if side is None or len(side.stmts) > 1 or not (isinstance(cc, Bin) and cc.op == op
                                                       and isinstance(cc.b, Pseudo)):
            return
        sm = cc.a
        if not (isinstance(sm, Bin) and sm.op == "Add" and isinstance(sm.a, Pseudo) and sm.b == step
                and sm.a.depth == step.depth and cc.b.depth == step.depth):
            return
        t, e = side.then, side.els
        if t is None or e is None or t.cond is not None or e.cond is not None:
            return
        f = fmt_expr(sm)
        # the counter store comes before the compare's fork, or in both
        # branches; the loop variable's store is missing when it is unused
        if side.stmts and len(t.stmts) <= 1 and not e.stmts:
            a1, a3 = side.stmts[0], side.stmts[0]
            a2 = t.stmts[0] if t.stmts else None
        elif not side.stmts and len(t.stmts) in (1, 2) and len(e.stmts) == 1:
            a1, a3 = t.stmts[0], e.stmts[0]
            a2 = t.stmts[1] if len(t.stmts) == 2 else None
        else:
            return
        if not all(isinstance(x, Assign) for x in (a1, a2 or a1, a3)):
            return
        if not (a1.target == sm.a and a3.target == sm.a and fmt_expr(a1.value) == f and fmt_expr(a3.value) == f
                and (a2 is None or (isinstance(a2.target, Reg) and fmt_expr(a2.value) == f))):
            return
        key = (sm.a, cc.b, a2.target.n if a2 is not None else None)
        if found is not None and found != key:
            return
        found = key
    cnt, lim, var = found
    if var is None:
        lf.tmp_regs = getattr(lf, "tmp_regs", 0) + 1
        var = JIT_TMP + lf.tmp_regs
    node.stmts = [Assign(cnt, Bin("Add", cnt, step))]
    for side in (node.then, node.els):
        side.stmts = []
        side.cond = Bin(side.cond.op, cnt, lim)
        side.then.stmts = [Assign(Reg(var), cnt)]
        side.els.stmts = []


def make_stepper(vm, lifter):
    return JitStepper(vm, lifter) if isinstance(vm, JitModel) else Stepper(vm, lifter)


def build_tree(paths, d, start):
    """paths share decisions[:d]; statements before `start` were emitted already."""
    if len(paths) == 1 and len(paths[0][0]) <= d:
        taken, dlog, out, oc = paths[0]
        return Node(out[start:], outcome=oc)
    # all paths make decision d at the same point
    p0 = paths[0]
    if len(p0[0]) <= d:
        # some path ends here while others continue: shouldn't happen (deterministic)
        taken, dlog, out, oc = p0
        return Node(out[start:], outcome=oc)
    _, cond, _ = p0[1][d][1], p0[1][d][2], None
    at = p0[1][d][1]
    stmts = p0[2][start:at]
    tp = [p for p in paths if p[0][d]]
    fp = [p for p in paths if not p[0][d]]
    then = build_tree(tp, d + 1, at) if tp else None
    els = build_tree(fp, d + 1, at) if fp else None
    return Node(stmts, cond=cond, then=then, els=els)


# --------------------------------------------------------------------------
# --------------------------------------------------------------------------
# driver

def chunk_key(src):
    """Same key as deob.chunk_key / srcKey() in envlog.luau (the __maker tag prefix)."""
    h = 0
    for b in src.encode("latin-1"):
        h = (h * 31 + b) % 2147483648
    return "%d_%d" % (len(src), h)


_SOURCE_CACHE = {}      # source text -> static analysis (the same in every constant round)


def analyze_source(path):
    """AST, VM models and constructor functions of one VM source file. Depends
    only on the text, so constant rounds reuse it."""
    with open(path, encoding="latin-1", newline="") as f:
        text = f.read()
    hit = _SOURCE_CACHE.get(text)
    if hit is not None:
        return hit
    root = vmmap.load_ast(path)
    key = chunk_key(text)
    disp = vmmap.find_dispatchers(root)
    ctor = find_ctor_funcs(root)
    vms = {}
    for info in vmmap.maker_info(root):
        # dispatch loops inside this VM closure
        ids = {id(n) for n in iter_nodes(info["vm"])}
        inside = [d["node"] for d in disp if id(d["node"]) in ids]
        tag = "%s@%d,%d" % ((key,) + tuple(info["at"]))
        vms[tag] = VMModel(info, inside, ctor)
        vms[tag].tag = tag
    # LPH_JIT functions: makers in the VM object returning plain Lua
    for k, node in ctor.items():
        parts = jit_maker_parts(node)
        if parts is not None:
            try:
                jm = JitModel(node, ctor, parts[0], parts[1])
            except Unsupported:
                continue
            jm.tag = "%s@jit:%s" % (key, k.decode("latin-1") if isinstance(k, bytes) else k)
            vms[jm.tag] = jm
    # a closure op picks the child's interpreter through the VM object
    # (`g[C[C[4]]](g, upvals, C)`): it can be the maker of another VM
    siblings = {id(vm.maker): vm for vm in vms.values()}
    for vm in vms.values():
        vm.siblings = siblings
    hit = _SOURCE_CACHE[text] = (root, text.split("\n"), vms, ctor)
    return hit


class Program:
    def __init__(self, source_path, dump_path, chunk_paths=()):
        """source_path: the obfuscated script; chunk_paths: original sources of
        VM chunks it loadstring'd (their protos are tagged with their key)."""
        self.dump = Dump(dump_path)
        self.vms = {}
        self.ctors = {}
        for i, path in enumerate([source_path] + list(chunk_paths)):
            root, lines, vms, ctor = analyze_source(path)
            if i == 0:
                self.root = root
                self.lines = lines
            for tag, vm in vms.items():
                self.vms[tag] = vm
                self.ctors[id(vm)] = ctor
                vm.src_lines = lines
        self.dump.vm_names = {vm.maker["args"][0]["name"] for vm in self.vms.values()}
        # bind Lua function values of the VM object to their AST
        for cap in self.dump.protos.values():
            try:
                e = cap.get(self.vm_of(cap).maker["args"][0]["name"])
            except (KeyError, AttributeError, IndexError):
                continue
            ctor = self.ctors[id(self.vm_of(cap))]
            if isinstance(e, LTable):
                for k, v in e.h.items():
                    if isinstance(v, OpaqueFn) and v.node is None and k in ctor:
                        v.node = ctor[k]
        g = LTable()
        for lib in ("bit32", "string", "table", "math", "buffer"):
            t = LTable()
            for nm in list(S.CONCRETE) + ["table.pack", "table.unpack", "table.move", "table.create"]:
                if nm.startswith(lib + "."):
                    t.set(nm.split(".", 1)[1].encode(), Builtin(nm))
            g.set(lib.encode(), t)
        for nm in ("select", "unpack", "getfenv", "setfenv", "tonumber"):
            g.set(nm.encode(), Builtin(nm))
        self.globals = g

    def vm_of(self, cap):
        tag = cap.get("__maker").decode("latin-1")
        if tag not in self.vms:
            raise Unsupported("no source for VM %s (a loadstring'd chunk that was not saved?)" % tag)
        return self.vms[tag]

    def walk_stable(self, vm, lf, st, limit, *, purpose="lift"):
        """Walk until state discovery converges.

        A restart means the previous graph is obsolete: a new jump register,
        carried VM local, or unstable packed value was discovered.  Never use
        the last partial graph merely because WALK_RESTARTS was exhausted.
        """
        last_sig = None
        stagnant = 0
        for attempt in range(1, WALK_RESTARTS + 1):
            s0, order, restart = self._walk(vm, lf, st, limit)
            if not restart:
                return s0, order

            sig = _walk_signature(lf, st, order)
            if sig == last_sig:
                stagnant += 1
            else:
                stagnant = 0
                last_sig = sig

            # A restart should normally add a fact.  Repeating exactly the same
            # state three times indicates a recovery loop, not useful progress.
            if stagnant >= 3:
                raise WalkIncomplete(
                    "%s walk stopped making progress after %d restarts "
                    "(jump_regs=%d, carry=%d, requests=%d)" %
                    (purpose, attempt, len(lf.jump_regs),
                     len(getattr(st, "carry", ())), len(lf.requests))
                )

        raise WalkIncomplete(
            "%s walk did not converge after %d restarts "
            "(jump_regs=%d, carry=%d, requests=%d)" %
            (purpose, WALK_RESTARTS, len(lf.jump_regs),
             len(getattr(st, "carry", ())), len(lf.requests))
        )

    def lift_raw(self, key, upvals=None, limit=200000):
        cap = self.dump.protos[key]
        vm = self.vm_of(cap)
        if upvals is None:
            upvals = UpList()
        proto = vm.proto_of(cap)
        lf = ProtoLifter(vm, self.dump, vm.vmobj_of(cap), proto, upvals, self.globals)
        st = make_stepper(vm, lf)
        s0, order = self.walk_stable(vm, lf, st, limit, purpose="raw")
        return s0, order, lf

    def _walk(self, vm, lf, st, limit):
        """Sparse conditional constant propagation over the instruction graph.
        Each state (mode, pc, loop depth, jump registers, packs) is stepped
        once; register facts (constant / truthy / falsy) flow along edges and
        meet at merges. A branch whose condition the facts decide only enables
        one edge, so Luraph's opaque predicates never lead into junk code
        (which would also run bogus in-place decryptors).
        Returns (entry, [(key, node)], restart)."""
        s0 = st.initial()
        link = vm.kstack_link
        nodes = {}          # key -> Node
        states = {}         # key -> State
        facts = {}          # key -> dict of incoming facts
        order = []
        self.pred = {}
        self.edges = {}     # key -> set of successor keys (feasible)
        work = [s0.key(link)]
        states[work[0]] = s0
        facts[work[0]] = {}
        inwork = {work[0]}
        pack_sets = {}      # key without packs -> packs of its first state
        pending = set()     # new jump registers of a stack VM (one restart for all)
        depth_at = {}       # stack VM: (mode, pc) -> carried locals (the stack depth)
        hubs = set()        # stack VM: (mode, pc) of pop-and-jump instructions
        steps = 0
        nerr = 0
        while work and len(order) < limit:
            k = work.pop()
            inwork.discard(k)
            s = states[k]
            node = nodes.get(k)
            if node is None:
                try:
                    node = st.step(s, "%d_%d_" % (s.pc, len(order)))
                except Unsupported as e:
                    if os.environ.get("DEVIRT_TB"):
                        import traceback
                        print("-- at %s:%s op %s" % (s.mode, s.pc, lf.last_op), file=sys.stderr)
                        for arr in [v_ for v_ in lf.proto.h.values() if isinstance(v_, LTable)]:
                            for pc_ in range(s.pc - 2, s.pc + 2):
                                base = arr.get(pc_)
                                print("   arr#%s[%d] = %s -> %s" % (arr.tid, pc_, base, st.gov.d.get((id(arr), pc_), base)), file=sys.stderr)
                        traceback.print_exc()
                    node = Node([], outcome=None)
                    node.error = str(e)
                    nerr += 1
                if getattr(st, "new_carry", False):
                    # a VM local turned out to carry state between
                    # instructions: walk again with it in the states
                    st.new_carry = False
                    return s0, order, True
                nodes[k] = node
                order.append((k, node))
                if lf.walk_only and nerr > WALK_MAX_ERRORS:
                    # a request walk that forked on a not yet decoded
                    # constant into junk code: keep what it asked for so far
                    break
            steps += 1
            if steps > limit * 20:
                break
            if lf.stack_base is not None and len(order) > STACK_WALK_MAX and getattr(st, "carry", None):
                # Do not fall back to stale stack slots.  That old fallback could
                # make the walk terminate, but it also changed VM semantics and
                # was a major source of convincing-looking partial output.
                raise WalkIncomplete(
                    "stack VM state explosion after %d states "
                    "(stack_base=%r, carried=%r)" %
                    (len(order), lf.stack_base, sorted(st.carry, key=repr))
                )
            succ = []
            restart = propagate(node, dict(facts[k]), succ, lf)
            if restart:
                node.error = restart
            for ns, nf in succ:
                if not isinstance(ns.pc, int) or not isinstance(ns.mode, int):
                    regs = {r.n for x in (ns.pc, ns.mode) if not isinstance(x, int)
                            for r in expr_regs(x)} - lf.jump_regs
                    if regs and lf.stack_base is not None:
                        # stack VM: finish the walk first, collecting every
                        # new return-address slot (one restart for all)
                        pending |= regs
                        continue
                    if regs:
                        # computed jump through a register: track its constant values
                        lf.jump_regs |= regs
                        return s0, order, True
                    node.error = "symbolic next pc/mode: %s / %s" % (fmt_any(ns.pc), fmt_any(ns.mode))
                    continue
                if ns.locs:
                    # compiled stack code has few stack depths per pc (one,
                    # except at a shared pop-and-jump, a "hub"); ever new ones
                    # are a path where the stack grows each round: cut it off
                    if ns.pc != s.pc + 1 and s.locs and ns.locs < s.locs:
                        hubs.add((s.mode, s.pc))
                    seen_locs = depth_at.setdefault((ns.mode, ns.pc), set())
                    if ns.locs not in seen_locs and len(seen_locs) >= MAX_STACK_DEPTHS \
                            and (ns.mode, ns.pc) not in hubs:
                        node.error = "stack depth %s at %s:%s (seen %s)" % (
                            ns.locs[0][1], ns.mode, ns.pc, sorted(x[0][1] for x in seen_locs))
                        # Keep request walks permissive so they can still discover
                        # constants.  A real lift will reject this node before
                        # lowering instead of silently deleting the edge.
                        continue
                    seen_locs.add(ns.locs)
                nk = ns.key(link)
                # a long-lived unread pack (the entry's `...`) killed inside a
                # loop gives the loop a second copy: leave such packs out of the
                # states (the register still holds the table.pack) and restart
                core = nk[:5]
                seen = pack_sets.setdefault(core, nk[5])
                if seen != nk[5]:
                    bad = (set(seen) ^ set(nk[5])) & lf.pack_killed
                    if bad - lf.pack_unstable:
                        lf.pack_unstable |= bad
                        return s0, order, True
                self.edges.setdefault(k, set()).add(nk)
                if nk not in facts:
                    facts[nk] = nf
                    states[nk] = ns
                    self.pred[nk] = k
                    changed = True
                else:
                    old = facts[nk]
                    m = meet(old, nf)
                    changed = m != old
                    facts[nk] = m
                if changed and nk not in inwork:
                    work.append(nk)
                    inwork.add(nk)
        self.facts = facts
        if pending:
            lf.jump_regs |= pending
            return s0, order, True
        return s0, order, False

def show_op(prog, key, mode, pc, force_op=None):
    cap = prog.dump.protos[key]
    vm = prog.vm_of(cap)
    lf = ProtoLifter(vm, prog.dump, vm.vmobj_of(cap), vm.proto_of(cap),
                     LTable(), prog.globals)
    st = make_stepper(vm, lf)
    lines = prog.lines
    for i, ifn, w in st.loops:
        c = st.conds[i]
        k = c["right"] if c["right"]["type"] == "AstExprConstantNumber" else c["left"]
        if S.fix_int(k["value"]) != mode:
            continue
        d = [x for x in vmmap.find_dispatchers(prog.root) if x["node"] is w][0]
        arrs = {}
        for nm, keys in vm.maker_decls.items():
            if len(keys) == 1 and keys[0] in lf.maker_scope.vars:
                v = lf.maker_scope.vars[keys[0]]
                if isinstance(v, LTable) and id(v) in lf.proto_arrays:
                    arrs[nm] = v
        # the loop's opcode array is named in the dispatch statement; resolve via VM scope aliases
        opname = d["arr"]
        cs = st.cs
        it = S.Interp(lf)
        _, inner = st._fresh_scopes(None, it)
        stmt = w["body"]["body"][0]
        opv = it.eval(stmt["values"][0]["expr"], inner)
        op = opv.get(pc) if force_op is None else force_op
        print("mode %d pc %d: op %s (array %s)" % (mode, pc, op, opname))
        for nm, v in sorted(arrs.items()):
            print("   %s[%d] = %s" % (nm, pc, fmt_any(v.get(pc))))
        blk = vmmap.resolve(d["tree"], d["op"], op)
        print(vmmap.text_of(lines, blk) if blk else "<no handler>")
        return
    print("no loop for mode", mode)


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("protos")
    ap.add_argument("--raw", help="print the raw listing of one proto key")
    ap.add_argument("--lift", help="lift one proto key (with its closures) to Luau")
    ap.add_argument("--op", nargs=2, metavar=("PROTO", "MODE:PC[:OP]"), help="show the handler of one instruction (OP: as decrypted)")
    ap.add_argument("--all", metavar="OUT", help="lift every VM root (what deob.py --devirt writes) into OUT")
    ap.add_argument("--chunk", action="append", default=[], metavar="FILE",
                    help="original source of a loadstring'd VM chunk (*.chunk_<key>.luau written by deob.py)")
    ap.add_argument("--allow-partial", action="store_true",
                    help="debug only: lower a graph even when some VM states are unresolved")
    a = ap.parse_args()
    if a.allow_partial:
        os.environ["DEVIRT_ALLOW_PARTIAL"] = "1"
    if a.all:
        text, stats, reqs, bufs = lift_program(a.source, a.protos, a.chunk)
        with open(a.all, "w", encoding="utf-8", newline="\n") as f:
            f.write(finish_text(text) + "\n")
        print("%d functions, %d unlifted blocks, %d unstructured jumps, %d constant requests"
              % (stats["functions"], stats["errors"], stats["fallbacks"], len(reqs)))
        print("missing constants:", LAST_DUMP[0].misses if LAST_DUMP else None)
        return
    prog = Program(a.source, a.protos, a.chunk)
    if a.op:
        show_op(prog, a.op[0], *[int(x) for x in a.op[1].split(":")])
        return
    if a.lift:
        prog.requests = set()
        cap = prog.dump.protos[a.lift]
        vm = prog.vm_of(cap)
        fl = FunctionLifter(prog)
        lines = fl.lift(vm, vm.vmobj_of(cap), vm.proto_of(cap), UpList(), {})
        import codegen
        print("\n".join(lines).replace(codegen.LONG_NL, "\n"))
        print("-- stats %s, %d constant requests" % (fl.stats, len(prog.requests)))
        return
    if a.raw:
        s0, order, lf = prog.lift_raw(a.raw)
        print("-- proto %s entry %s:%s" % (a.raw, s0.mode, s0.pc))
        for k, node in sorted(order, key=lambda kn: kn[0][1]):
            print("[%s:%d d%d]%s" % (k[0], k[1], k[2], " op %s" % (getattr(node, "op", None),) if os.environ.get("DEVIRT_TB") else ""))
            if getattr(node, "error", None):
                print("  !! " + node.error)
            for line in fmt_node(node, "  "):
                print(line)
        print("-- %d constant requests" % len(lf.requests))


# --------------------------------------------------------------------------
# whole functions -> Luau

REG_PREFIX = "rstuvwxyzabcdefghijklmnopq"
REG_ARRAY = 1000000     # register-resident arrays: Reg(REG_ARRAY + base)


class FunctionLifter:
    """Lifts one proto (and, recursively, the closures it creates) to Luau lines."""

    def __init__(self, prog):
        self.prog = prog
        self.stats = {"functions": 0, "errors": 0, "fallbacks": 0}
        self.lifted = set()

    def lift(self, vm, vmobj, proto, upvals, upnames, depth=0):
        self.stats["functions"] += 1
        self.lifted.add(id(proto))
        lf = ProtoLifter(vm, self.prog.dump, vmobj, proto, upvals, self.prog.globals)
        st = make_stepper(vm, lf)
        s0, order = self.prog.walk_stable(vm, lf, st, 400000, purpose="final")
        self.prog.requests |= lf.requests

        bad = unresolved_nodes(order)
        allow_partial = not bool(os.environ.get("DEVIRT_STRICT"))
        if bad and not allow_partial:
            details = "; ".join(
                "%s:%s: %s" % (k[0], k[1], why) for k, why in bad[:12]
            )
            if len(bad) > 12:
                details += "; ... +%d more" % (len(bad) - 12)
            raise WalkIncomplete(
                "refusing partial devirtualization: %d unresolved VM state(s): %s" %
                (len(bad), details)
            )
        max_final_states = int(os.environ.get("DEVIRT_V14_MAX_FINAL_STATES", "50000"))
        if len(order) > max_final_states:
            raise WalkIncomplete("v14.x final graph too large for safe structuring: %d states (limit %d)"
                                 % (len(order), max_final_states))
        if lf.reg_arrays:
            k0 = s0.key(vm.kstack_link)
            for k, node in order:
                if k == k0:
                    node.stmts[0:0] = [Assign(Reg(REG_ARRAY + b), S.NewTable()) for b in sorted(lf.reg_arrays)]
                    break
        frames = {}
        for c in lf.children:
            if any(isinstance(e, (RegFile, FrameProxy)) for e in c.upvals):
                if id(c.proto) not in frames:
                    frames[id(c.proto)] = self.frame_regs(vm, vmobj, c)
                c.frame_map = frames[id(c.proto)]
                c.frame_regs = sorted({r for i, e in enumerate(c.upvals, 1) if isinstance(e, RegFile)
                                       for r in c.frame_map.get(i, ())})
        me = sys.modules[__name__]
        apply_frame_calls(order)
        drop_idle_closes(order, lf.captured_regs)
        prefix = REG_PREFIX[depth % len(REG_PREFIX)]
        lines, self.params, nerr, fallbacks = backend.lower(
            s0.key(vm.kstack_link), order, me, vm.kstack_link, prefix, upnames,
            lambda x, names: self.closure(vm, vmobj, x, names, depth))
        self.stats["fallbacks"] += fallbacks
        if os.environ.get("DEVIRT_DEBUG"):
            pid = self.prog.dump.pid_of_table.get(proto.tid)
            lines.insert(0, "-- proto %s" % (pid if pid is not None else "t%s" % proto.tid))
        self.stats["errors"] += nerr
        return lines

    def frame_regs(self, vm, vmobj, c, depth=0):
        """{upvalue index: registers} a closure reads or writes through the
        register frames it captured (`s[k] = s`), found by walking it (and
        its own closures that get the frame passed through)."""
        idx = [i for i, e in enumerate(c.upvals, 1) if isinstance(e, (RegFile, FrameProxy))]
        cvm = getattr(c, "vm", None) or vm
        memo = self.__dict__.setdefault("_frame_memo", {})
        mkey = (id(c.proto), id(cvm), tuple(idx))
        if mkey in memo:
            return memo[mkey]
        uses = memo[mkey] = {}
        try:
            lf = ProtoLifter(cvm, self.prog.dump, vmobj, c.proto, UpList(idx), self.prog.globals)
            lf.walk_only = True
            st = make_stepper(cvm, lf)
            self.prog.walk_stable(cvm, lf, st, 400000, purpose="frame scan")
        except Unsupported:
            return uses
        for i, r in lf.frame_uses:
            uses.setdefault(i, set()).add(r)
        if depth < 8:
            for g in lf.children:
                if any(isinstance(e, FrameProxy) for e in g.upvals):
                    for gi, regs in self.frame_regs(cvm, vmobj, g, depth + 1).items():
                        e = g.upvals[gi - 1]
                        if isinstance(e, FrameProxy):
                            uses.setdefault(e.idx, set()).update(regs)
        return uses

    def closure(self, vm, vmobj, c, parent_names, depth):
        import codegen as CG
        proto = c.proto
        if id(proto) in self.lifted:
            return CG.FuncE(["function(...) --[[ recursive proto ]] end"])
        capnames = getattr(c, "capnames", {})
        upnames = {}
        fmap = getattr(c, "frame_map", {})
        for i, e in enumerate(c.upvals, 1):
            if isinstance(e, RegFile):
                # the parent's frame: upv[i][r] is the parent's local r
                for r in fmap.get(i, ()):
                    upnames[(i, r)] = capnames.get(r, "nil")
            elif isinstance(e, FrameProxy):
                # a frame the parent got as its own upvalue
                for r in fmap.get(i, ()):
                    upnames[(i, r)] = parent_names.get(("up", (e.idx, r)), "upv%d_%d" % (e.idx, r))
            elif isinstance(e, LTable):
                vals = list(e.h.values())
                ints = [v for v in vals if isinstance(v, int)]
                if any(isinstance(v, RegFile) for v in vals) and ints:
                    upnames[i] = capnames.get(ints[0], "nil")
                else:
                    # a box of the parent's own upvalue list
                    ups = [v for v in vals if isinstance(v, UpContainer)]
                    upnames[i] = parent_names.get(("up", ups[0].idx), "upv%d" % ups[0].idx) if ups else "nil"
            elif isinstance(e, Reg):
                upnames[i] = capnames.get(e.n, "nil")
            elif isinstance(e, MaybeBox):
                upnames[i] = capnames.get(e.reg, "nil")
            elif isinstance(e, (BoxProxy, Upval)):
                upnames[i] = parent_names.get(("up", e.idx), "upv%d" % e.idx)
            else:
                upnames[i] = "nil"
        params = ["..."]
        fidx = [i for i, e in enumerate(c.upvals, 1) if isinstance(e, (RegFile, FrameProxy))]
        cvm = getattr(c, "vm", None) or vm
        # the same proto closed over at several sites (the walk visits a
        # closure op once per state, tail duplication copies code): lift once
        ckey = (id(proto), id(cvm), tuple(fidx), depth, tuple(sorted(upnames.items(), key=repr)))
        memo = self.__dict__.setdefault("_closure_memo", {})
        if ckey in memo:
            lines, params = memo[ckey]
        else:
            try:
                lines = self.lift(cvm, vmobj, proto, UpList(fidx), upnames, depth + 1)
                params = self.params
            except Unsupported as ex:
                lines = [
                    "-- unresolved native/runtime closure: %s" % str(ex).replace("\n", " "),
                    "return nil",
                ]
            memo[ckey] = (lines, params)
        self.lifted.discard(id(proto))
        f = CG.FuncE(["function(%s)" % ", ".join(params)] + ["\t" + l for l in lines] + ["end"])
        f.captures = set(upnames.values())
        return f


def stmt_exprs(st):
    import codegen as CG
    out = []
    if isinstance(st, CG.AssignS):
        out += [t for t in st.targets]
        out += list(st.values.items)
    elif isinstance(st, (CG.CallS, CG.TempDef)):
        out.append(st.call)
    elif isinstance(st, CG.SetListS):
        out.append(st.tbl)
        out += list(st.values.items)
    return out


def collect_regs(body):
    import codegen as CG
    import structure as ST
    regs = set()

    def ex(e):
        if e is None:
            return
        for x in CG.walk(e):
            if isinstance(x, Reg):
                regs.add(x.n)

    def multi(m):
        if m is None:
            return
        for x in m.items:
            ex(x)
        if m.tail is not None:
            ex(CG.TailRef(m.tail))

    def blk(stmts):
        for s_ in stmts:
            if isinstance(s_, CG.AssignS):
                for t in s_.targets:
                    ex(t)
                multi(s_.values)
            elif isinstance(s_, (CG.CallS, CG.TempDef)):
                ex(s_.call)
            elif isinstance(s_, CG.SetListS):
                ex(s_.tbl)
                multi(s_.values)
            elif isinstance(s_, ST.SIf):
                ex(s_.cond)
                blk(s_.then)
                blk(s_.els)
            elif isinstance(s_, ST.SLoop):
                blk(s_.body)
                ex(s_.cond)
                if s_.kind == "for":
                    regs.add(s_.forinfo[0])
                    for x in s_.forinfo[1]:
                        ex(x)
                elif s_.kind == "forin":
                    regs.update(s_.forinfo[0])
                    for x in s_.forinfo[1]:
                        ex(x)
            elif isinstance(s_, ST.SReturn):
                multi(s_.values)
    blk(body)
    return regs


def refine_loops(body):
    """Placeholder: loop shapes (for / while cond) are recognized later."""
    return body


def _vm_roots(prog):
    """[(maker tag, [(seq, pid, cap), ...] sorted)] with the payload VM last, and its tag."""
    by_vm = {}
    for key, cap in prog.dump.protos.items():
        if cap.get("__maker") is None:
            continue
        # the root of a VM is the first proto it made a closure of
        by_vm.setdefault(cap["__maker"], []).append((cap.get("__seq") or 0, key, cap))
    # the payload is the VM created last (Luraph's loader VM makes its
    # closures first; a payload that stopped early may have fewer protos):
    # it comes last and the file ends by running it
    vms = sorted(by_vm.items(), key=lambda kv: min(x[0] for x in kv[1]))
    payload = vms[-1][0] if vms else None
    vms.sort(key=lambda kv: kv[0] == payload)
    for _, lst in vms:
        lst.sort(key=lambda x: (x[0], x[1]))
    # The script's main function is the proto Luraph's bootstrap root (pid 1)
    # called last; the runtime records it. Usually it is the root of the VM
    # made last, but each proto picks its interpreter, so the bootstrap and
    # the script can share one VM implementation (the root of that VM is
    # then the bootstrap) and later VMs may belong to script functions.
    rc = prog.dump.raw.get("root_callee")
    for tag, lst in vms:
        hit = [x for x in lst if rc is not None and str(x[1]) == str(rc)]
        if hit:
            lst.remove(hit[0])
            lst.insert(0, hit[0])
            payload = tag
            vms.sort(key=lambda kv: kv[0] == payload)
            break
    return vms, payload


def program_roots(prog):
    """[(tag, pid, cap)] of the root protos lift_program lifts, in order."""
    vms, payload = _vm_roots(prog)
    loaders = bool(os.environ.get("DEVIRT_LOADERS"))
    return [(tag, lst[0][1], lst[0][2]) for tag, lst in vms if tag == payload or loaders]


def lift_program(source, protos_path, chunk_paths=(), fetch=None):
    """The root proto of every VM -> Luau text (plus stats and constant requests)."""
    prog = Program(source, protos_path, chunk_paths)
    prog.dump.fetcher = fetch
    LAST_DUMP[:] = [prog.dump]
    prog.requests = set()
    fl = FunctionLifter(prog)
    out = []
    vms, payload = _vm_roots(prog)
    payload_pid = None
    # Luraph's loader VMs are not part of the script (never called): lifted
    # only on request (DEVIRT_LOADERS=1, as local functions). The payload is
    # the chunk's own code: written at top level unless loaders are shown.
    loaders = bool(os.environ.get("DEVIRT_LOADERS"))
    for tag, lst in vms:
        _, pid, cap = lst[0]          # pid: the proto key (a number, or t<table id>)
        where = tag.decode("latin-1")
        if tag != payload and not loaders:
            if os.environ.get("DEVIRT_DEBUG"):
                out.append("-- skipped non-payload loader VM")
            continue
        try:
            vm = prog.vm_of(cap)
        except Unsupported as ex:
            out.append("-- VM %s: root proto #%s not lifted: %s" % (where, pid, ex))
            out.append("")
            continue
        proto = vm.proto_of(cap)
        vmobj = vm.vmobj_of(cap)
        role = "the script" if tag == payload else "Luraph loader, not called"
        if loaders or os.environ.get("DEVIRT_DEBUG"):
            out.append("-- lifted VM root: %s" % role)
        if tag == payload:
            payload_pid = pid
        lines = fl.lift(vm, vmobj, proto, UpList(), {}, 0)
        if tag == payload and not loaders:
            out.append("")
            if fl.params:
                out.append("local %s = ..." % ", ".join(fl.params))
            out += lines
            payload_pid = None
            continue
        out.append("local function vm_root_%s(%s)" % (pid, ", ".join(fl.params)))
        out += ["\t" + l for l in lines]
        out.append("end")
        out.append("")
    if payload_pid is not None:
        out.append("return vm_root_%s(...)" % payload_pid)
    # Luraph runtime functions the script calls (SharedFn): stubs up front
    shared = []
    for n in sorted(prog.dump.shared.values()):
        shared += [
            "-- unresolved Luraph runtime helper; preserved as a safe stub",
            "local function luraph_runtime%d(...)" % n,
            "\treturn nil",
            "end",
            "",
        ]
    if shared:
        at = next((i for i, l in enumerate(out) if l and not l.startswith("--")), len(out))
        out[at:at] = shared
    text = backend.polish("\n".join(out))
    return text, fl.stats, prog.requests, buffer_patches(prog.dump)


finish_text = backend.finish_text


LAST_DUMP = []


def buffer_patches(dump):
    """The lifter's in-place string decryption as a request for the runtime:
    "path,to,holder,key/offset:hexbytes/...;..." (only bytes that differ)."""
    return format_patches(*stable_patches(dump))


def stable_patches(dump):
    """dump.buf_patch / tab_patch keyed by table path instead of object id
    (table ids differ between runs): ({(holder path, offset): byte},
    {(table path, key): number}), only values that differ from the dump."""
    paths = dump.paths()
    bw = {}
    for (bid, off), v in dump.buf_patch.items():
        buf, tid, key = dump.buf_loc[bid]
        if not isinstance(v, int) or buf.data[off] == v or tid not in paths:
            continue
        bw[(",".join(str(x) for x in paths[tid]), key, off)] = v
    tw = {}
    for (tid, key), v in dump.tab_patch.items():
        base = dump.tables[tid].h.get(key)
        if tid in paths and not (isinstance(base, (int, float)) and base == v):
            tw[(",".join(str(x) for x in paths[tid]), key)] = v
    return bw, tw


def format_patches(bw, tw):
    per = {}
    for (path, key, off), v in bw.items():
        per.setdefault("%s,%s" % (path, key), {})[off] = v
    out = []
    for holder, bs in per.items():
        runs = []
        for off in sorted(bs):
            if runs and runs[-1][0] + len(runs[-1][1]) == off:
                runs[-1][1].append(bs[off])
            else:
                runs.append((off, [bs[off]]))
        out.append(holder + "".join("/%d:%s" % (off, bytes(b).hex()) for off, b in runs))
    out.sort()      # (table ids differ between runs: compare by path)
    # table entries: "path/=key:number/..."
    tabs = {}
    for (path, key), v in tw.items():
        tabs.setdefault(path, []).append((key, v))
    tab_out = [path + "".join("/=%d:%s" % (k, S.fmt_num(v)) for k, v in sorted(kv))
               for path, kv in tabs.items()]
    return ";".join(out + sorted(tab_out))


def same_patches(old, new):
    """Whether `old` (the patches of an earlier round, paths of that run's
    dump) are the patches `new` of the last lift (LAST_DUMP). The shortest
    path to a table changes between runs on ties, so the old paths are
    resolved in the new dump and written with its paths first."""
    if old == new:
        return True
    if not LAST_DUMP:
        return False
    dump = LAST_DUMP[0]
    res = PathResolver(dump)
    pkey = {tid: ",".join(str(x) for x in p) for tid, p in dump.paths().items()}

    def cur(path):
        t = res.get(path)
        return pkey.get(t.tid, path) if t is not None else path
    out, tabs = [], []
    for spec in old.split(";") if old else []:
        head, sep, rest = spec.partition("/")
        if rest.startswith("="):
            tabs.append(cur(head) + sep + rest)
        else:
            path, _, key = head.rpartition(",")
            out.append("%s,%s" % (cur(path), key) + sep + rest)
    return ";".join(sorted(out) + sorted(tabs)) == new


class WalkCache:
    """Results of walking single protos (collect_requests), kept across
    constant rounds by the proto's table path. A walk that asked for no
    constant (and missed none) sees the same data next round, so it is not
    repeated. Table ids differ between runs and so can the shortest path to a
    table (ties), so stored paths are resolved by walking them (PathResolver)."""

    def __init__(self):
        self.entries = {}       # (path of the proto, id(vm)) -> entry


class PathResolver:
    """A table path as written by Dump.paths() ("seq,name,key,..." with
    "slot@value" steps) -> the table it names in this dump, or None."""

    def __init__(self, dump):
        self.dump = dump
        self.caps = {}
        for cap in dump.protos.values():
            if cap.get("__seq") is not None:
                self.caps[str(cap["__seq"])] = cap
        self.memo = {}

    def get(self, path):
        if path in self.memo:
            return self.memo[path]
        t = self.dump.overrides.get(path)
        if not isinstance(t, LTable):
            parts = path.split(",")
            t = None
            if len(parts) == 2:
                cap = self.caps.get(parts[0])
                t = cap.get(parts[1]) if cap is not None else None
            elif len(parts) > 2 and "@" not in parts[-1]:
                parent = self.get(",".join(parts[:-1]))
                try:
                    k = int(parts[-1])
                except ValueError:
                    k = None
                if isinstance(parent, LTable) and k is not None:
                    t = parent.h.get(k)
            if not isinstance(t, LTable):
                t = None
        self.memo[path] = t
        return t


def collect_requests(source, protos_path, chunk_paths=(), cache=None, fetch=None):
    """What an intermediate constant round needs from lift_program, without
    the structuring/codegen/naming: every proto lift_program would lift is
    walked (SCCP, which is where requests and in-place decryption happen),
    its closures followed. -> (stats, requests, buffer patches)."""
    prog = Program(source, protos_path, chunk_paths)
    LAST_DUMP[:] = [prog.dump]
    dump = prog.dump
    if cache is None:
        cache = WalkCache()
    paths = dump.paths()
    pkey = {tid: ",".join(str(x) for x in p) for tid, p in paths.items()}
    res = PathResolver(dump)
    live = {}
    for (path, vmid), ent in cache.entries.items():
        t = res.get(path)
        if t is not None:
            live[(t.tid, vmid)] = (path, ent)
    kept = {}
    stats = {"functions": 0, "errors": 0, "fallbacks": 0, "walked": 0}
    requests = set()
    bw, tw = PatchLog(), PatchLog()
    dump.fetcher = fetch
    dump.extra_patches = (bw, tw)
    todo = []
    for tag, pid, cap in reversed(program_roots(prog)):
        try:
            vm = prog.vm_of(cap)
        except Unsupported:
            continue
        todo.append((vm, vm.vmobj_of(cap), vm.proto_of(cap)))
    seen = set()
    while todo:
        vm, vmobj, proto = todo.pop()
        if id(proto) in seen:
            continue
        seen.add(id(proto))
        found = live.get((proto.tid, id(vm)))
        use = found and _translate(found[1], res, pkey)
        if use:
            kept[(found[0], id(vm))] = found[1]
            ent = found[1]
            kids, ebw, etw = use
        else:
            ent = _walk_one(prog, vm, vmobj, proto, pkey)
            stats["walked"] += 1
            key = pkey.get(proto.tid)
            if key is not None and ent["clean"]:
                kept[(key, id(vm))] = ent
            kids = [res.get(c) if isinstance(c, str) else c for c in ent["children"]]
            ebw, etw = ent["bw"], ent["tw"]
        stats["functions"] += 1
        stats["errors"] += ent["errors"]
        requests |= ent["requests"]
        bw.update(ebw)
        tw.update(etw)
        kvms = [prog.vms.get(t) or _JIT_TAGGED.get(t) or vm for t in ent.get("child_vms") or [None] * len(kids)]
        todo += [(kvm, vmobj, c) for c, kvm in reversed(list(zip(kids, kvms))) if c is not None]
    cache.entries = kept
    stats["fetched"] = len(dump.fetched)
    if os.environ.get("DEVIRT_TIMING") and dump.fetched:
        print("[*]   live requests: %d, patches %.1fs, round trips %.1fs (harness %.1fs), %d KB of patches sent"
              % ((len(dump.fetched),) + tuple(dump.fetch_time[:3]) + (dump.fetch_time[3] // 1024,)),
              file=sys.stderr)
    prog.requests = requests
    return stats, requests, format_patches(bw, tw)


def _walk_one(prog, vm, vmobj, proto, pkey):
    dump = prog.dump
    saved = dump.buf_patch, dump.tab_patch
    dump.buf_patch, dump.tab_patch = PatchLog(), PatchLog()
    nmiss = sum(dump.misses.values())
    ent = {"requests": set(), "children": [], "errors": 0, "clean": False, "bw": {}, "tw": {}}
    try:
        lf = ProtoLifter(vm, dump, vmobj, proto, UpList(), prog.globals)
        lf.walk_only = True
        st = make_stepper(vm, lf)
        # Request collection intentionally accepts unresolved nodes after the
        # walk converges: those nodes often contain exactly the missing lazy
        # constant requests needed by the next round.  Restart exhaustion, on
        # the other hand, is never treated as a successful walk.
        s0, order = prog.walk_stable(vm, lf, st, 400000, purpose="request")
    except Unsupported:
        ent["errors"] = 1
        return ent
    finally:
        ent["bw"], ent["tw"] = stable_patches(dump)
        dump.buf_patch, dump.tab_patch = saved
    ent["requests"] = lf.requests
    ent["errors"] = sum(1 for _, n in order if getattr(n, "error", None))
    if os.environ.get("DEVIRT_ERRS"):
        for s, n in order:
            if getattr(n, "error", None):
                print("[walk] %s %s %s" % (pkey.get(proto.tid, proto.tid), s[:2], n.error),
                      file=sys.stderr)
    kids = [c for c in lf.children if isinstance(c.proto, LTable)]
    ent["children"] = [pkey.get(c.proto.tid, c.proto) for c in kids]
    ent["child_vms"] = [getattr(getattr(c, "vm", None), "tag", None) for c in kids]
    ent["clean"] = not lf.requests and sum(dump.misses.values()) == nmiss and \
        all(isinstance(c, str) for c in ent["children"])
    return ent


def _translate(ent, res, pkey):
    """A cached entry's paths -> this dump: (child tables, buffer patches,
    table patches), patches keyed by the current shortest path (the one the
    runtime looks up); None if a path no longer resolves."""
    kids = []
    for c in ent["children"]:
        t = res.get(c)
        if t is None:
            return None
        kids.append(t)
    out = []
    for d in (ent["bw"], ent["tw"]):
        nd = {}
        for k, v in d.items():
            t = res.get(k[0])
            if t is None or t.tid not in pkey:
                return None
            nd[(pkey[t.tid],) + k[1:]] = v
        out.append(nd)
    return kids, out[0], out[1]


run_big_stack = backend.run_big_stack


if __name__ == "__main__":
    run_big_stack(main)
