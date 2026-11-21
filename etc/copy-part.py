#!/usr/bin/env python3
"""Copy into the part `RaftNoAx/` the main tree's modules its closed theorem needs that reach raft.

usage: etc/copy-part.py [--check] [--list]

  --check   write nothing; exit 1 if a copy differs from what is checked in (or is missing, or a
            copy is stale), listing the files.
  --list    print the modules of the closure that the part has (copied or generated), with why.

The part `RaftNoAx/` (notes/raft-noax-part.md) holds the raft proof, and kvdurable's on it, over a
raft of its own (project raft-noax of etc/goose.py) and kvdurable's own translation (project
kvdurable-noax), as `RaftWitness/` does for the witness experiment. Its translations have the same
Lean names as the main tree's, so no module may import both: every module of the import closure of
the main tree's `ROOTS` that (transitively) imports a translation the part has (`seeds`: the main
modules of the packages the part's goose pieces translate, those of `RENAME`'s packages too) has a
copy in the part, `RaftNoAx/<path>`, module `RaftNoAx.<module>`; every other module is the main
tree's, imported as it is.

The copies, by kind:
- `Code/`, `GeneratedProof/`: none; etc/goose.py translates them into the part (projects raft-noax
  and kvdurable-noax, the parts of projects kvreconf and etcd).
- the package initializers etc/gen-init.py copies for the part (`PARTS['RaftNoAx']`), and the
  `Link.lean` files (etc/gen-link.py --raft-noax / --kvdurable-noax): none, those scripts write them.
- every other module of the closure that reaches a seed (`Spec/`, `Proof/`), and the trusted code
  and manual proofs (`TrustedCode/`, `ManualProof/`) of the part's translated packages, with the
  Goose configuration (`Code/**.toml`) of those packages: copied, with the imports of the modules
  the part has prefixed by `RaftNoAx.`, `RENAME`'s package paths replaced (the Lean namespace,
  dotted, and the directory, slashed), and a first line naming the source.

A file of the part whose first line does not name this script is the part's own (as the hand-written
modules of `RaftTla/`, etc/gen-raft-tla.py, whose design this follows): a copy that stopped following
the main tree on purpose (delete its first line when you change it). It is neither written nor
checked. A copy no longer produced (its first line names this script) is deleted (`--check`:
reported).
"""

import importlib.util
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "etc"))
import goose  # noqa: E402


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, "etc", file))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


PART = "RaftNoAx"


def lean_pkg(go_path):
    """The Lean module path (dotted) of a Go package path."""
    return go_path.replace(".", "_").replace("-", "_").replace("/", ".")


KVD_MAIN = "github.com/mit-pdos/etcd-grove/examples/raft/kvdurable"
# The main tree's modules whose closure the part copies: the closed theorem's.
ROOTS = [f"Proof.{lean_pkg(KVD_MAIN)}.Results", f"Proof.{lean_pkg(KVD_MAIN)}.TopLevelRobustness"]
# Main package (Lean, dotted) -> the part's: kvdurable's proofs follow the part's translation's Go
# path (goose.KVDURABLE_NOAX_PKG); empty while that is kvdurable's own.
RENAME = {k: v for k, v in [(lean_pkg(KVD_MAIN), lean_pkg(goose.KVDURABLE_NOAX_PKG))] if k != v}

HEADER = f"The copy for the part `{PART}/` of"
NOTE = "(etc/copy-part.py; rerun it, do not edit)"

IMPORT_RE = re.compile(r"(?m)^((?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?)(\S+)")


def path_of(mod):
    return os.path.join(ROOT, *mod.split(".")) + ".lean"


def imports_of(mod, cache={}):
    if mod not in cache:
        p = path_of(mod)
        cache[mod] = ([m.group(2) for m in IMPORT_RE.finditer(header_part(open(p).read()))]
                      if os.path.exists(p) else None)
    return cache[mod]


def header_part(txt):
    """The part of a file its imports are in (up to the first section or declaration after its
    `module` line, its docstring before that left out: the text from `module`)."""
    s = re.search(r"(?m)^module\s*$", txt)
    s = s.start() if s else 0
    m = re.compile(r"(?m)^(@\[expose\]|public section|namespace |section|noncomputable )").search(txt, s)
    return txt[s:m.start()] if m else txt[s:]


def owned_pieces():
    """The part's translated packages: the owned paths (slashed) of every goose piece into it."""
    out = []
    for p in goose.PROJECTS:
        for root, _, _, owned in goose.pieces(p):
            if root == PART:
                out += owned
    return out


def unrename(dotted):
    for k, v in RENAME.items():
        dotted = re.sub(rf"(?<![\w.]){re.escape(v)}(?![\w])", k, dotted)
    return dotted


def rename(txt):
    for k, v in RENAME.items():
        txt = re.sub(rf"(?<![\w]){re.escape(k)}(?![\w])", v, txt)
        ks, vs = k.replace(".", "/"), v.replace(".", "/")
        txt = re.sub(rf"(?<![\w]){re.escape(ks)}(?![\w])", vs, txt)
    return txt


def under(mod, prefixes):
    return any(mod == q or mod.startswith(q + ".") for q in prefixes)


def closure():
    seen, todo = set(), list(ROOTS)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo += imports_of(m) or []
    return {m for m in seen if imports_of(m) is not None}


def compute():
    """(the closure's modules the part has, with why; the files to write: part path -> text)."""
    pkgs = [unrename(o.replace(os.sep, ".")) for o in owned_pieces()]
    seed_prefixes = [f"{d}.{p}" for d in ("Code", "GeneratedProof", "TrustedCode", "ManualProof") for p in pkgs]
    # every module of a renamed package goes with it, whether or not it reaches a seed
    seed_prefixes += [f"{d}.{k}" for d in ("Spec", "Proof") for k in RENAME]
    cl = closure()
    memo = {}

    def reaches(m):
        if m not in memo:
            memo[m] = False
            memo[m] = under(m, seed_prefixes) or any(reaches(x) for x in imports_of(m) if x in cl)
        return memo[m]
    part = {m for m in cl if reaches(m)}
    # the trusted code and manual proofs of the translated packages, whether or not in the closure
    for d in ("TrustedCode", "ManualProof"):
        for p in pkgs:
            base = os.path.join(ROOT, d, *p.split("."))
            for f in ([base + ".lean"] if os.path.isfile(base + ".lean") else []) + [
                    os.path.join(dp, x) for dp, _, fs in os.walk(base) for x in fs if x.endswith(".lean")]:
                part.add(os.path.relpath(f, ROOT)[:-len(".lean")].replace(os.sep, "."))
    gen_init = load("gen_init", "gen-init.py")
    by_gen_init = {p[:-len(".lean")].replace("/", ".")
                   for p in sorted(gen_init.part_paths(gen_init.PARTS[PART][0])) + gen_init.NOAX_MAIN_PATHS}
    why, files = {}, {}
    for m in sorted(part):
        if m.split(".")[0] in ("Code", "GeneratedProof"):
            why[m] = "etc/goose.py"
            continue
        if m in by_gen_init:
            why[m] = "etc/gen-init.py"
            continue
        if m.endswith(".Link"):
            why[m] = "etc/gen-link.py"
            continue
        why[m] = "copied"
        src = os.path.relpath(path_of(m), ROOT)
        txt = open(path_of(m)).read()
        head = header_part(txt)
        s = txt.index(head)

        def imp(mm):
            x = mm.group(2)
            return mm.group(1) + (f"{PART}.{x}" if x in part else x)
        txt = txt[:s] + IMPORT_RE.sub(imp, head) + txt[s + len(head):]
        txt = rename(txt)
        files[os.path.join(PART, rename(src))] = f"-- {HEADER} `{src}` {NOTE}.\n" + txt
    prune_unimported(why, files)
    # the Goose configuration of the translated packages
    for o in owned_pieces():
        src_o = unrename(o.replace(os.sep, ".")).replace(".", os.sep)
        base = os.path.join(ROOT, "Code", src_o)
        tomls = ([base + ".toml"] if os.path.isfile(base + ".toml") else []) + sorted(
            os.path.join(dp, x) for dp, _, fs in os.walk(base) for x in fs if x.endswith(".toml"))
        for f in tomls:
            src = os.path.relpath(f, ROOT)
            files[os.path.join(PART, rename(src))] = f"# {HEADER} `{src}` {NOTE}.\n" + open(f).read()
    return why, files


def prune_unimported(why, files):
    """Drop the copies no module of the part imports (to a fixpoint), but the roots (`Results`,
    `TopLevelRobustness`, `Link`): modules of the main tree's closure that only the main tree's
    versions of the part's own files import (stage 2 replaced the `proto` axioms' callers, so the
    copies of those axioms, `DescribeConfChange`'s, `fmt.Sprintf`'s and `strings.Join`'s were left
    behind, built but unreached; prove-raftex, 2026-11-20). The part's other modules (its own,
    the generated ones) are read from disk."""
    def mod_of(path):
        return path[:-len(".lean")].replace(os.sep, ".")
    texts = {}
    for dp, _, fs in os.walk(os.path.join(ROOT, PART)):
        for x in fs:
            if x.endswith(".lean"):
                p = os.path.relpath(os.path.join(dp, x), ROOT)
                t = open(os.path.join(ROOT, p)).read()
                first = t.split("\n", 1)[0]
                if not (HEADER in first and NOTE in first):  # a stale copy is not the part's
                    texts[mod_of(p)] = t
    copied = {}
    for p, t in files.items():
        if p.endswith(".lean"):
            texts[mod_of(p)] = t
            copied[mod_of(p)] = p
    importers = {}
    for m, t in texts.items():
        for mm in IMPORT_RE.finditer(header_part(t)):
            importers.setdefault(mm.group(2), set()).add(m)
    alive = set(texts)
    changed = True
    while changed:
        changed = False
        for m in sorted(alive & set(copied)):
            if m.endswith((".Results", ".TopLevelRobustness", ".Link")):
                continue
            if not any(i in alive for i in importers.get(m, ())):
                alive.discard(m)
                changed = True
    for m in set(copied) - alive:
        del files[copied[m]]
        why.pop(unrename(m[len(PART) + 1:]), None)


def existing_copies():
    out = set()
    for d in ("Code", "Spec", "Proof", "TrustedCode", "ManualProof"):
        for dp, _, fs in os.walk(os.path.join(ROOT, PART, d)):
            for x in fs:
                if not x.endswith((".lean", ".toml")):
                    continue
                f = os.path.join(dp, x)
                with open(f) as fh:
                    first = fh.readline()
                if HEADER in first and NOTE in first:
                    out.add(os.path.relpath(f, ROOT))
    return out


def main(argv):
    check, listing = "--check" in argv, "--list" in argv
    why, files = compute()
    if listing:
        for m, w in sorted(why.items()):
            print(f"{w:16} {m}")
        return 0
    bad, own = [], []
    for path, txt in sorted(files.items()):
        full = os.path.join(ROOT, path)
        old = open(full).read() if os.path.exists(full) else None
        if old == txt:
            continue
        if old is not None and not (HEADER in old.split("\n", 1)[0] and NOTE in old.split("\n", 1)[0]):
            own.append(path)
            continue
        if check:
            bad.append(path)
        else:
            os.makedirs(os.path.dirname(full), exist_ok=True)
            open(full, "w").write(txt)
    for path in sorted(existing_copies() - set(files)):
        if check:
            bad.append(path + " (stale)")
        else:
            os.remove(os.path.join(ROOT, path))
    counts = {}
    for w in why.values():
        counts[w] = counts.get(w, 0) + 1
    summary = ", ".join(f"{n} {w}" for w, n in sorted(counts.items()))
    if own:
        summary += f"; {len(own)} the part's own: " + " ".join(own)
    if check:
        for b in bad:
            print(f"copy-part: differs from the copy: {b}")
        print(f"copy-part: {len(files)} files ({summary}); {len(bad)} differ", file=sys.stderr)
        return 1 if bad else 0
    print(f"copy-part: {len(files)} files ({summary})", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
