#!/usr/bin/env python3
"""Generate a package's interface: what a client sees of each of its importable modules and of
each of its functions' proofs.

For each module the package lists as importable (`etc/api/<pkg>.txt`, `etc/api-check.py`), and
for each function's proof file (`Proof/<pkg>/<F>.lean` of a spec file `Spec/<pkg>/<F>.lean`: its
`<F>.wp_proof`, or the axiom in its place, is shown with `<F>.spec` unfolded), writes
`interface/<module path>.txt`: every declaration a client of the module sees, as Lean's module
system exports it (`etc/interface.lean`: an ordinary `import`, `importModules (level :=
.exported)`): its kind and signature, and the body of a definition only when it is exported
(`@[expose]`). `private` declarations, proofs and sealed bodies are absent. The ambient section
variables every declaration takes (`[GooseExts] ... [sem : go.Semantics]`) are left out of
the signatures and listed once at the top. Commit the output: a change to what a package exposes
is then a diff to review.

`--layout` also checks the layout rules on every module of the package (`etc/interface.lean`'s
`names` mode): a spec file `Spec/<pkg>/<F>.lean` exposes only `<F>.spec` (`__` read as `.`), and
the proof file `Proof/<pkg>/<F>.lean` of a spec file exposes only `<F>.wp_proof`. The violations
found are compared with `etc/api/<pkg>-layout.txt` (`--update` rewrites it): only new ones fail.

It never builds: the modules must be up to date (`lake build`), else it stops. `$LAKE_OPTS` is
passed to lake (`--packages=...` in a worktree on another Perennial pin), as for `etc/tcb-report.py`.

usage: etc/gen-interface.py etc/api/raft.txt [--check] [--layout] [--update]
  --check   exit 1 if interface/ differs from what the build gives (or, with --layout, if
            there are layout violations not in the baseline); writes nothing
"""
import argparse
import difflib
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import textwrap

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "interface"
AMBIENT = [r"\[GooseExts\]", r"\[GooseSemantics\]", r"\[GooseInterp\]",
           r"\[go_gctx : GoGlobalContext\]", r"\{hlc : HasLC\}",
           r"\{GF : BundledGFunctors\}", r"\[hG : HeapGS (?:HasLC\.hasLC|hlc) GF\]",
           r"\[sem : go\.Semantics\]", r"\[package_sem : [\w.]+\.Assumptions\]",
           r"\[StorageModel GF\]", r"\[AllG GF\]"]
AMBIENT_RE = re.compile(r"\s*(?:" + "|".join(AMBIENT) + r")")
PREFIX = "Perennial.EtcdGrove."
WIDTH = 100


def run(cmd, **kw):
    if cmd[0] == "lake":  # `$LAKE_OPTS` (`--packages=...`), as `etc/tcb-report.py`
        cmd = ["lake", *os.environ.get("LAKE_OPTS", "").split(), *cmd[1:]]
    return subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True, **kw)


def importable(config):
    r = run([sys.executable, "-I", str(ROOT / "etc/api-check.py"), config, "--list"])
    if r.returncode != 0:
        sys.exit(r.stdout + r.stderr)
    return r.stdout.split()


def package_modules(config):
    inside = [l.split()[1] for l in pathlib.Path(config).read_text().splitlines()
              if l.startswith("inside ")]
    mods = []
    for pre in inside:
        for p in sorted((ROOT / pre).rglob("*.lean")):
            mods.append(".".join(p.relative_to(ROOT).with_suffix("").parts))
    return mods


def ensure_built(mods):
    r = run(["lake", "build", "--no-build", *mods])
    if r.returncode != 0:
        sys.exit("gen-interface: the modules are not up to date; run `lake build` first\n"
                 + (r.stdout + r.stderr)[-2000:])


def dump(mode, mods, outdir):
    r = run(["lake", "env", "lean", "--run", str(ROOT / "etc/interface.lean"), mode, str(outdir), *mods])
    if r.returncode != 0:
        sys.exit("gen-interface: etc/interface.lean failed\n" + (r.stdout + r.stderr)[-4000:])


GOSTR = re.compile(r"\[(\d+#8(?:,\s*\d+#8)*)\]")


def gostr(m):
    """A printable byte list (a `go!"..."` string, which Lean prints as its bytes) back as a string."""
    bs = [int(x.split("#")[0]) for x in m.group(1).split(",")]
    if all(32 <= b < 127 and b != 34 for b in bs):
        return 'go!"' + bytes(bs).decode() + '"'
    return m.group(0)


def tidy(text):
    """Drop the ambient binders and the namespace prefix of the declared names; rewrap."""
    text = GOSTR.sub(gostr, text)
    blocks = text.split("\n\n")
    head, out = blocks[0], []
    for b in blocks[1:]:
        if not b.strip():
            continue
        if b.startswith(("structure ", "syntax ")):
            first, _, fields = b.partition("\n")
            first = " ".join(AMBIENT_RE.sub("", first).split())
            kind, _, rest = first.partition(" ")
            rest = rest[len(PREFIX):] if rest.startswith(PREFIX) else rest
            out.append("\n".join(textwrap.wrap(f"{kind} {rest}", WIDTH, subsequent_indent="    ")
                                  + ([fields] if fields else [])))
            continue
        unfolded = ""
        if "\n  -- `" in b:
            b, _mark, rest = b.partition("\n  -- `")
            unfolded = "\n  -- `" + rest.rstrip()
        sig, sep, body = b.partition(" :=\n")
        sig = " ".join(AMBIENT_RE.sub("", sig).split())
        kind, _, rest = sig.partition(" ")
        if kind == "def" and rest.startswith("(sealed) "):
            kind, rest = "def (sealed)", rest[len("(sealed) "):]
        if rest.startswith(PREFIX):
            rest = rest[len(PREFIX):]
        if kind == "inductive":
            # constructors: "inductive Sig\n  | ctor..." were joined; split them back
            parts = re.split(r" \| ", f"{kind} {rest}")
            lines = textwrap.wrap(parts[0], WIDTH, subsequent_indent="    ")
            for c in parts[1:]:
                c = c[len(PREFIX):] if c.startswith(PREFIX) else c
                lines += textwrap.wrap("| " + c, WIDTH, initial_indent="  ", subsequent_indent="      ")
            out.append("\n".join(lines))
            continue
        lines = textwrap.wrap(f"{kind} {rest}" + (" :=" if sep else ""), WIDTH,
                              subsequent_indent="    ")
        if sep:
            lines.append(body.rstrip())
        out.append("\n".join(lines) + unfolded)
    note = ("-- Every declaration also takes the ambient section variables (left out below): "
            "the Go semantics\n-- (`ext`, `ffi`, `go_gctx`, `sem`, the package's `Assumptions`), "
            "`GF`, `hG`, `StorageModel GF`, `AllG GF`.")
    return head.rstrip() + "\n" + note + "\n\n" + "\n\n".join(out) + "\n"


def generate(mods):
    with tempfile.TemporaryDirectory() as tmp:
        dump("full", mods, tmp)
        res = {}
        for m in mods:
            rel = pathlib.Path(*m.split(".")).with_suffix(".txt")
            res[rel] = tidy((pathlib.Path(tmp) / rel).read_text())
        return res


def roots(config):
    return [l.split()[1] for l in pathlib.Path(config).read_text().splitlines()
            if l.startswith("root ")]


def fn_of(mod, rts):
    """The function a `Spec`/`Proof` module is of: its path below the package's root, `__` as `.`."""
    rest = mod.split(".", 1)[1]
    for r in sorted(rts, key=len, reverse=True):
        if rest.startswith(r + "."):
            return rest[len(r) + 1:].replace("__", ".")
    return None


def layout(config, mods):
    """Layout violations: (module, declaration, why)."""
    rts = roots(config)
    with tempfile.TemporaryDirectory() as tmp:
        dump("names", mods, tmp)
        decls = {}
        for m in mods:
            f = pathlib.Path(tmp, *m.split(".")).with_suffix(".names")
            decls[m] = [l.split() for l in f.read_text().splitlines() if l.strip()]
    bad = []
    spec_mods = {m for m in mods if m.startswith("Spec.")}
    for m in mods:
        top, rest = m.split(".", 1)
        fn = fn_of(m, rts)
        if fn is None or fn in ("Api",):
            continue
        if top == "Spec":
            want = PREFIX + fn + ".spec"
            names = [d[-1] for d in decls[m]]
            if want not in names:
                bad.append((m, want, "missing: a spec file declares its spec"))
            for k, n in ((d[0], d[-1]) for d in decls[m]):
                if not n.startswith(PREFIX + fn + ".spec"):
                    bad.append((m, n, f"exposed by a spec file ({k})"))
        elif top == "Proof" and "Spec." + rest in spec_mods:
            want = PREFIX + fn + ".wp_proof"
            names = [d[-1] for d in decls[m]]
            if want not in names:
                bad.append((m, want, "missing: a proof file proves its spec"))
            for k, n in ((d[0], d[-1]) for d in decls[m]):
                if n != want:
                    bad.append((m, n, f"exposed by a proof file ({k})"))
    return sorted(bad)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("config")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--layout", action="store_true")
    ap.add_argument("--update", action="store_true")
    a = ap.parse_args()
    allmods = package_modules(a.config)
    specs = {m for m in allmods if m.startswith("Spec.")}
    # the importable modules, and every function's proof file (`Proof/<pkg>/<F>.lean` of a spec
    # `Spec/<pkg>/<F>.lean`): its theorem, the spec unfolded
    mods = sorted(set(importable(a.config)) |
                  {m for m in allmods if m.startswith("Proof.") and "Spec." + m.split(".", 1)[1] in specs})
    ensure_built(sorted(set(mods) | (set(allmods) if a.layout else set())))
    status = 0

    new = generate(mods)
    pkgdirs = {rel.parent for rel in new}
    old = {}
    for d in pkgdirs:
        for f in (OUT / d).glob("*.txt") if (OUT / d).is_dir() else []:
            old[f.relative_to(OUT)] = f.read_text()
    changed = sorted(r for r in set(new) | set(old) if new.get(r) != old.get(r))
    if a.check:
        for r in changed:
            print(f"interface/{r}: {'stale' if r in old and r in new else 'missing' if r in new else 'not importable any more'}")
            if r in old and r in new:
                diff = difflib.unified_diff(old[r].splitlines(), new[r].splitlines(), lineterm="", n=1)
                print("\n".join(list(diff)[2:40]))
        if changed:
            status = 1
    else:
        for r in changed:
            f = OUT / r
            if r in new:
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(new[r])
            else:
                f.unlink()
        print(f"gen-interface: {len(new)} module(s), {len(changed)} file(s) written", file=sys.stderr)

    if a.layout:
        base = pathlib.Path(a.config).with_name(pathlib.Path(a.config).stem + "-layout.txt")
        found = [f"{m} {n}  # {why}" for m, n, why in layout(a.config, allmods)]
        known = set(l for l in base.read_text().splitlines() if l and not l.startswith("#")) if base.exists() else set()
        fresh = [l for l in found if l not in known]
        gone = sorted(known - set(found))
        if a.update:
            base.write_text("# Layout violations known (etc/gen-interface.py --layout --update); remove them,\n"
                            "# don't add to them.\n" + "\n".join(found) + "\n")
            print(f"gen-interface: {base}: {len(found)} violation(s)", file=sys.stderr)
        else:
            for l in fresh:
                print("layout: " + l)
            for l in gone:
                print("layout (fixed, drop from the baseline): " + l)
            print(f"gen-interface: {len(found)} layout violation(s), {len(fresh)} new", file=sys.stderr)
            if a.check and fresh:
                status = 1
    sys.exit(status)


if __name__ == "__main__":
    main()
