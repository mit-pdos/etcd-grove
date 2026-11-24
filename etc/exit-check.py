#!/usr/bin/env python3
"""No robustness theorem's program reports a violation by exiting (notes/robustness.md, "An exit is a
safe run"; notes/decisions.md, "Go's process exit stays angelic, and checkers panic").

Perennial models `syscall.Exit` (so `os.Exit`, and a logger's `Fatal`, which call it) as `AngelicExit`:
the exiting goroutine steps to itself forever and the program's other goroutines keep running. Under
`Robust` (Robustness/Statement.lean) an exit of any status is therefore a safe run: a program that
checks a property and exits on a violation proves nothing about the property. This script finds the
programs the robustness theorems are about and lists every process or goroutine exit in their own
code, which must have an entry in `etc/exit-allow.txt` with its reason (an exit on a usage error of
the command line, before any check runs; never one on a check's failure).

The programs: every `TopLevelDefs.lean` (`<part>/Proof/<mangled Go path>/TopLevelDefs.lean`, the
module holding the programs a `TopLevelRobustness` statement names) boots packages by their
`<X>.initialize'`; `X` resolves, as Lean resolves it inside the example's namespace, to a package
of the translations (`<part>/Code/**.lean`: `def <X> : GoString := go!"<Go path>"`). Their own code:
every non-test Go package of their compiled closure (`go list -deps`, in their Go module) whose
directory is under `examples/`; their dependencies (raft, etcd, the standard library) are not
checked here. The exits: `etc/exitcheck` (type-checked, so a function value `f := os.Exit` counts).

Fails on an exit with no entry, an entry nothing hits (stale), a `TopLevelDefs.lean` whose programs do
not resolve, or a package that does not load. A `TopLevelDefs.lean` with no `initialize'` (shared
definitions, a draft) names no program and is listed as such. Needs `go`; seconds.

usage: etc/exit-check.py [-v]   (-v: list every exit found, allowed or not)
"""
import collections, os, pathlib, re, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOW = ROOT / "etc/exit-allow.txt"
EXAMPLES = ROOT / "examples"
SKIP_DIRS = {".lake", ".git", "old", "node_modules"}
# Build tags of a program package, as etc/goose.py translates it (project tracecheck: `with_tla`).
TAGS = {"github.com/mit-pdos/etcd-grove/examples/raft/tracecheck": "with_tla"}

INIT = re.compile(r"(?<![\w.'«»])((?:[\w«»]+\.)*)initialize'")
GOSTRING = re.compile(r'^noncomputable def ([\w.«»]+) : GoString := go!"([^"]+)"', re.M)


def walk(pattern):
    for p in ROOT.rglob(pattern):
        rel = p.relative_to(ROOT)
        if not SKIP_DIRS.intersection(rel.parts):
            yield rel


def go_env():
    env = dict(os.environ)
    env.pop("GOWORK", None)  # the example modules' own go.work, where they have one
    env["PATH"] = "/usr/local/go/bin:" + os.path.expanduser("~/go/bin") + ":" + env.get("PATH", "")
    env.setdefault("GOTOOLCHAIN", "go1.27.1")
    return env


def part_of(rel):
    """The part root of a module file ('' for the main tree): the directory above `Proof/`/`Code/`."""
    parts = rel.parts
    for i, s in enumerate(parts):
        if s in ("Proof", "Code"):
            return "/".join(parts[:i])
    return None


def gostrings():
    """{part: {Lean package namespace: Go path}} of the translations."""
    defs = collections.defaultdict(dict)
    for rel in walk("*.lean"):
        part = part_of(rel)
        if part is None or "Code" not in rel.parts:
            continue
        for m in GOSTRING.finditer((ROOT / rel).read_text(errors="replace")):
            defs[part][m.group(1)] = m.group(2)
    return defs


def programs(defs):
    """[(TopLevelDefs file, sorted Go paths)], and errors."""
    out, errs = [], []
    for rel in sorted(walk("TopLevelDefs.lean")):
        part = part_of(rel)
        i = rel.parts.index("Proof")
        ns = list(rel.parts[i + 1:-1])
        text = (ROOT / rel).read_text(errors="replace")
        paths = set()
        for x in sorted({m.group(1).rstrip(".") for m in INIT.finditer(text)}):
            found = None
            for k in range(len(ns), -1, -1):  # innermost namespace first, as Lean resolves
                name = ".".join(ns[:k] + ([x] if x else []))
                for p in (part, ""):
                    if name in defs.get(p, {}):
                        found = defs[p][name]
                        break
                if found:
                    break
            if found is None:
                errs.append(f"{rel}: `{x + '.' if x else ''}initialize'` names no translated package")
            else:
                paths.add(found)
        out.append((rel, sorted(paths)))
    return out, errs


def modules():
    """[(Go module path, directory)] of examples/, longest path first."""
    mods = []
    for gomod in EXAMPLES.rglob("go.mod"):
        for line in gomod.read_text().splitlines():
            if line.startswith("module "):
                mods.append((line.split()[1], gomod.parent))
                break
    return sorted(mods, key=lambda m: -len(m[0]))


def module_of(gopath, mods):
    for path, d in mods:
        if gopath == path or gopath.startswith(path + "/"):
            return d
    return None


def load_allow():
    allow = {}
    for i, line in enumerate(ALLOW.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 4 or not parts[3].strip():
            raise RuntimeError(f"{ALLOW.name}:{i}: want <file>\\t<function>\\t<line text>\\t<reason>")
        allow[tuple(parts[:3])] = parts[3]
    return allow


def main():
    verbose = "-v" in sys.argv[1:]
    env = go_env()
    try:
        allow = load_allow()
    except RuntimeError as e:
        print(f"exit-check: FAILED: {e}")
        return 1
    progs, bad = programs(gostrings())
    mods = modules()
    by_mod = collections.defaultdict(set)
    named = [(rel, ps) for rel, ps in progs if ps]
    for rel, ps in named:
        for p in ps:
            d = module_of(p, mods)
            if d is None:
                bad.append(f"{rel}: {p} is in no Go module of examples/")
            else:
                by_mod[(d, TAGS.get(p, ""))].add(p)
    with tempfile.TemporaryDirectory() as tmp:
        tool = pathlib.Path(tmp) / "exitcheck"
        b = subprocess.run(["go", "build", "-o", str(tool), "."], cwd=ROOT / "etc/exitcheck", env=env,
                           capture_output=True, text=True)
        if b.returncode != 0:
            print(f"exit-check: FAILED: building etc/exitcheck: {b.stderr.strip()[:500]}")
            return 1
        hits, npkgs = set(), 0
        for (d, tags), paths in sorted(by_mod.items()):
            r = subprocess.run([str(tool), "-C", str(d), "-under", str(EXAMPLES), "-tags", tags, *sorted(paths)],
                               env=env, capture_output=True, text=True)
            if r.returncode != 0:
                bad.append(f"{d.relative_to(ROOT)}: {r.stderr.strip()[:500]}")
                continue
            m = re.search(r"(\d+) packages checked", r.stderr)
            npkgs += int(m.group(1)) if m else 0
            for line in r.stdout.splitlines():
                loc, fn, text = line.split("\t", 2)
                hits.add((loc.rsplit(":", 2)[0], fn, text, loc))
    seen = set()
    for f, fn, text, loc in sorted(hits):
        key = (f, fn, text)
        seen.add(key)
        if verbose:
            print(f"  {loc}\t{fn}\t{text}\t{'allowed: ' + allow[key] if key in allow else 'NO ENTRY'}")
        if key not in allow:
            bad.append(f"an exit in a robustness theorem's program: {loc}\t{fn}\t{text}")
    for key in sorted(set(allow) - seen):
        bad.append(f"stale entry (nothing hits it): {key[0]}\t{key[1]}\t{key[2]}")
    unnamed = [str(rel) for rel, ps in progs if not ps]
    if verbose and unnamed:
        print("  no program named (no initialize'): " + ", ".join(unnamed))
    if bad:
        print("exit-check: FAILED (a checker must panic, not exit: notes/robustness.md; etc/exit-allow.txt):")
        for b in bad:
            print("  " + b)
        return 1
    print(f"exit-check: ok ({len(named)} TopLevelDefs, {sum(len(v) for v in by_mod.values())} program "
          f"packages, {npkgs} own packages checked, {len(seen)} allowed exits; {len(unnamed)} name no program)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
