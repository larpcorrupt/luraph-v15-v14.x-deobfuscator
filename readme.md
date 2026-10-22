DSC.GG/oxyenv
MY CONTACT ON DISCORD: larpcorrupt USER ID: 1481960463289028649




# SUPPORT THE PROJECT ! BTC: bc1p3zu6tv74hq4dugumjqk5xv2juu0vwa2ec80qwafnayhrplmk6flq655kz4
# Luraph v14.x / v15 Deobfuscator

A research-oriented **Lua/Luau deobfuscation and devirtualization framework** focused on recovering readable code from Luraph-protected scripts.

Currently targets:

- **Luraph v14.7**
- **Luraph v14.8**
- **Luraph v14.9**
- **Luraph v15**

The project combines runtime tracing, VM instrumentation, constant recovery, symbolic lifting, control-flow reconstruction, anti-tamper/probe removal, and source reconstruction.

> This project is under active development. Difficult scripts may still contain unresolved VM states or imperfectly reconstructed code. The goal is to recover as much of the real program structure as possible rather than pretend every sample can be restored to its exact original source.

---

## Features

### Luraph v14.7 / v14.8 / v14.9

The v14 frontend contains dedicated engines for each supported version.

```text
14.7 -> obfuscators.luraph_v14_7
14.8 -> obfuscators.luraph_v14_8
14.9 -> obfuscators.luraph_v14_9
```

Features include:

- Luraph version detection
- VM closure instrumentation
- Runtime constant recovery
- Repeated devirtualization/lifting rounds
- VM state reconstruction
- Control-flow recovery
- Partial-graph recovery by default when some states remain unresolved (`DEVIRT_STRICT=1` rejects partial graphs)
- Roblox/Luau runtime emulation
- Behavior tracing
- String recovery
- Constant folding
- Readability cleanup
- Removal of known Luraph environment/anti-tamper probes
- Alternate VM root selection for larger scripts
- Protection against incorrectly returning only a tiny behavior trace when richer static recovery is available

Known probe families that are cleaned include repeated empty event tests involving APIs such as:

```lua
ChildRemoved
DescendantRemoving
AncestryChanged
```

including common probe suites involving:

```lua
game
workspace
Folder
HttpService
RunService
```

Normal user code using these events is not supposed to be removed simply because the API appears once.

---

## Luraph v15

Luraph v15 uses the main plugin-based deobfuscator.

The v15 pipeline supports:

- automatic Luraph v15 detection
- header-stripped sample detection
- behavior tracing
- VM instrumentation
- anti-tamper trap attribution
- constant-request reruns
- symbolic VM lifting
- devirtualization
- readable Luau reconstruction

The registered plugin name is:

```text
luraph_v15
```

---

## Repository Layout

```text
luraph-v15-v14.x-deobfuscator/
│
├── Deobfuscator/
│   ├── CLAUDE.md
│   ├── LURAPH.md
│   ├── IRONBREW1.md
│   ├── samples/
│   │
│   └── deobf/
│       ├── cli.py
│       ├── deob.py
│       ├── harness.py
│       ├── codegen.py
│       ├── structure.py
│       ├── variables.py
│       ├── loops.py
│       ├── fold.py
│       ├── tidy.py
│       ├── traceout.py
│       ├── envlog.luau
│       ├── roblox_api.luau
│       │
│       ├── obfuscators/
│       │   ├── luraph_v14_7
│       │   ├── luraph_v14_8
│       │   ├── luraph_v14_9
│       │   ├── luraph_v15
│       │   ├── ironbrew1
│       │   └── generic
│       │
│       └── bin/
│           ├── luau.exe
│           ├── luau-compile.exe
│           ├── luau-analyze.exe
│           └── ...
│
└── readme.md
```

---

# Installation

Clone the repository:

```bash
git clone https://github.com/KryptIT/luraph-v15-v14.x-deobfuscator.git
cd luraph-v15-v14.x-deobfuscator/Deobfuscator/deobf
```

You need Python 3.

The repository currently includes Windows Luau binaries under:

```text
Deobfuscator/deobf/bin/
```

For other operating systems, you may need to provide compatible Luau tooling yourself.

---

# Usage

## Luraph v14.x

Basic usage:

```bash
py cli.py input.lua -o deobfuscated.lua
```

The frontend will attempt to detect the version automatically.

You can also force an engine:

```bash
py cli.py input.lua -o deobfuscated.lua --engine 14.7
```

```bash
py cli.py input.lua -o deobfuscated.lua --engine 14.8
```

```bash
py cli.py input.lua -o deobfuscated.lua --engine 14.9
```

If the Luraph header was removed and the version cannot be determined safely, specify `--engine` manually.

### Example

```bash
py cli.py protected.lua -o clean.lua --engine 14.7
```

Typical output:

```text
[*] engine: Luraph v14.7
[*] input : protected.lua
[*] tracing ... (run 1)
[*] constants decoded on request ...
[*] devirt round 1 ...
[*] devirt round 2 ...
[+] result: clean.lua
```

---

## Luraph v15

Use the main plugin frontend:

```bash
py deob.py input.lua -o deobfuscated.lua --obfuscator luraph_v15
```

Automatic detection can also be used:

```bash
py deob.py input.lua -o deobfuscated.lua
```

Check detection without deobfuscating:

```bash
py deob.py input.lua --detect
```

Example result:

```text
luraph_v15    1.00    Luraph v15
```

---

# Useful Options

## Behavior trace only

Skip VM lifting and only recover observed runtime behavior:

### v14

```bash
py cli.py input.lua --no-devirt
```

### v15

```bash
py deob.py input.lua --no-devirt
```

This is much faster, but it is **not full devirtualization**.

A behavior trace only contains code paths and effects observed during execution.

---

## Debug output

Keep intermediate reconstruction files:

```bash
py deob.py input.lua --debug
```

or:

```bash
py cli.py input.lua --debug --keep-work
```

Useful when working on:

- VM lifting
- root selection
- unresolved states
- traces
- constants
- reconstructed control flow

---

## Dump recovered strings

```bash
py deob.py input.lua --strings
```

or:

```bash
py cli.py input.lua --strings
```

---

## Change timeout

```bash
py cli.py input.lua --timeout 180
```

The v14 runtime defaults to a 120 second hard timeout.

The main `deob.py` frontend defaults to 90 seconds per run.

---

## More devirtualization rounds

```bash
py cli.py input.lua --devirt-rounds 400
```

Useful for difficult samples where constants or VM states are discovered gradually.

---

## Increase trap reruns

```bash
py cli.py input.lua --max-runs 20
```

---

## Raw runtime output

For the main frontend:

```bash
py deob.py input.lua --raw raw.txt
```

For v14:

```bash
py cli.py input.lua --raw
```

---

# PyPy

Large scripts can spend a significant amount of time inside the Python symbolic lifter.

The main deobfuscator can automatically switch to **PyPy** for sufficiently large inputs.

Force PyPy:

```bash
py deob.py input.lua --pypy
```

Disable it:

```bash
py deob.py input.lua --no-pypy
```

If PyPy is requested but unavailable, the tool falls back to the current Python installation.

---

# How It Works

At a high level, the deobfuscator performs several stages:

```text
Protected Lua/Luau
       │
       ▼
Version / obfuscator detection
       │
       ▼
Instrumented runtime harness
       │
       ├──► behavior trace
       │
       ├──► constants
       │
       └──► VM information
       │
       ▼
VM lifting / symbolic execution
       │
       ▼
Control-flow reconstruction
       │
       ▼
Probe / anti-tamper cleanup
       │
       ▼
Variable + expression reconstruction
       │
       ▼
Readable Lua/Luau
```

The deobfuscator does **not** simply run the protected file and copy its print output.

For supported Luraph versions, the goal is to recover the virtualized program itself.

---

# Static Recovery vs Behavior Tracing

These are different things.

A behavior trace might recover something like:

```lua
print("[TRADE] initialized")
warn("[TRADE] no active trade")
```

That does **not** mean the original program contained only those statements.

The actual virtualized program may contain:

```lua
local inventory = getInventory()

for _, item in inventory do
    if prices[item.Name] then
        ...
    end
end

local function startTrade(player)
    ...
end
```

Modern versions of the v14 engine prioritize the richer static/devirtualized result when available instead of replacing a large recovered program with a tiny execution trace.

When an individual VM state cannot be lifted, the preferred behavior is to preserve as much surrounding reconstructed code as possible.

---

# Limitations

Deobfuscation is not equivalent to recovering the author's exact original source file.

Information destroyed during compilation/obfuscation may not exist anymore, including:

- original local variable names
- original formatting
- comments
- some source-level abstractions
- exact expression choices
- some control-flow structure

Extremely complicated samples may also contain:

- unresolved VM states
- partially reconstructed functions
- environment-dependent branches
- APIs missing from the emulated Roblox environment
- anti-analysis behavior not yet modeled
- new Luraph VM layouts not yet implemented

If you find a sample that produces obviously incomplete output, open an issue and include the Luraph version, command used, terminal log, and the smallest sample that reproduces the issue.

---

# Other Engines

The main framework currently also contains:

```text
ironbrew1
generic
```

`generic` is the fallback environment/behavior tracer for scripts that do not match a supported obfuscator.

The primary focus of this repository remains **Luraph v14.x and v15 devirtualization**.

---

# Research / Development

Useful internal documentation is available in:

```text
Deobfuscator/LURAPH.md
Deobfuscator/IRONBREW1.md
Deobfuscator/CLAUDE.md
```

The project also contains dedicated modules for:

```text
VM lifting
symbolic execution
control-flow structuring
variable recovery
loop recovery
constant folding
idiom recovery
Luau AST processing
Roblox environment emulation
runtime tracing
```

---

# Contributing

Contributions, test samples, bug reports, VM research, opcode discoveries, and reconstruction improvements are welcome.

Especially useful contributions include:

- samples that fail to devirtualize
- new Luraph VM layouts
- unresolved opcode/state examples
- incorrect control-flow reconstruction
- false-positive probe removal
- Roblox API emulation fixes
- cleaner generated Luau output
- performance improvements

When reporting a problem, include the console output whenever possible.

---

# Disclaimer

This project is intended for **research, interoperability, reverse engineering, and analysis of code you own or are authorized to inspect**.

It is not affiliated with, endorsed by, or maintained by Luraph.

Luraph and related names belong to their respective owners.

---

# Credits

Developed and maintained by **KryptIT / larpcorrupt**.

Repository:

https://github.com/KryptIT/luraph-v15-v14.x-deobfuscator
