#!/usr/bin/env python3
"""Copy into the parts `RaftNoAx/` and `KvNet/` the modules of other trees their closures need.

usage: etc/copy-part.py [--part NAME]... [--check] [--list]

  --part    only this part (RaftNoAx or KvNet; repeatable; default: both).
  --check   write nothing; exit 1 if a copy differs from what is checked in (or is missing, or a
            copy is stale), listing the files.
  --list    print the modules of the closure that the part has (copied or generated), with why
            (and, for a copy, from which tree).

A part is a module root of its own (`<Part>/Code/`, `<Part>/Spec/`, ...) whose translations have the
same Lean names as another tree's, so no module may import both. Each part here has **sources**:
the trees it takes modules from, in order (the main tree is `""`). A module path `X` (`Spec.net.
Listen`) means, in the part, the part's own file `<Part>/X.lean` if there is one, else the first
source tree that has it (`<Src>/X.lean`, or `X.lean` for the main tree). Every module of the
import closure of the part's **roots** that (transitively) imports a **seed** -- a translation the
part has (`seeds`: the modules of the packages the part's goose pieces translate, those of
`RENAME`'s packages too), a module the part takes from a source part (not the main tree), or one
etc/gen-init.py writes for the part -- is in the part, `<Part>/X.lean`, module `<Part>.X`; every
other module is the main tree's, imported as it is.

- `RaftNoAx/` (notes/raft-noax-part.md): raft's proofs over a raft of its own (project raft-noax of
  etc/goose.py). Its source is the main tree; its roots raft's (its `Link` and the modules
  etc/api/raft.txt lists as importable: KvNet's raft is the part's), read in the main tree (the
  part's own files are not followed). (Until 2026-11-24 also kvdurable's, over its own translation,
  project kvdurable-noax: retired, raft_kvnet_robust subsumes it.)
- `KvNet/` (notes/kvnet-part.md): kvnet's proof, over raft-noax's raft, the net extension's `net`
  (the part `Net/`) and the bodied `durable` over fsExt (the part `WalTester/`). Its sources are
  `RaftNoAx/`, `Net/`, `WalTester/` and the main tree; its roots its own modules under `KvNet/Spec`
  and `KvNet/Proof` (`Imports.lean`, the smoke test, until kvnet's proof has a `Results`), read
  with the part's own files first. A module two source parts both have (other than one gen-init
  writes for the part) is a clash: the script stops and names it.

The copies, by kind:
- `Code/`, `GeneratedProof/`: none; etc/goose.py translates them into the part (RaftNoAx: projects
  raft-noax, the part of project etcd; KvNet: project kvnet, the
  parts of projects raft-noax, net, durable and etcd).
- the package initializers etc/gen-init.py writes for the part (`PARTS[part]`, `KVNET_INITS`), and
  the part's own and the main tree's `Link.lean` files (etc/gen-link.py): none, those scripts write
  them (a source part's `Link`, raft-noax's or `durable`'s that kvnet's `Link` uses, is copied).
- every other module of the closure that reaches a seed (`Spec/`, `Proof/`), and the trusted code
  and manual proofs (`TrustedCode/`, `ManualProof/`) of the part's translated packages, with the
  Goose configuration (`Code/**.toml`) of those packages (from the source tree whose goose piece
  translates the same package: KvNet's `durable` is `WalTester/`'s, bodied, with no configuration):
  copied, with the imports of the modules the part has prefixed by `<Part>.`, `RENAME`'s package
  paths replaced (the Lean namespace, dotted, and the directory, slashed), and a first line naming
  the source (a source part's own first line, when it is a copy itself, dropped).

A file of the part whose first line does not name this script is the part's own (as the hand-written
modules of `RaftTla/`, etc/gen-raft-tla.py, whose design this follows): a copy that stopped following
its source on purpose (delete its first line when you change it). It is neither written nor
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


def lean_pkg(go_path):
    """The Lean module path (dotted) of a Go package path."""
    return go_path.replace(".", "_").replace("-", "_").replace("/", ".")


# Main package (Lean, dotted) -> the part's: a part's proofs of a package translated under another Go
# path. None now (until 2026-11-24 RaftNoAx's kvdurable, kvdurablenoax). (Read by etc/gen-link.py.)
RENAME = {}

NOTE = "(etc/copy-part.py; rerun it, do not edit)"

IMPORT_RE = re.compile(r"(?m)^((?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?)(\S+)")


def header(part):
    return f"The copy for the part `{part}/` of"


def is_copy_line(first, part=None):
    """`first` is the first line of a copy made by this script (into `part`, or any part)."""
    return NOTE in first and (header(part) in first if part else "The copy for the part `" in first)


def header_part(txt):
    """The part of a file its imports are in (up to the first section or declaration after its
    `module` line, its docstring before that left out: the text from `module`)."""
    s = re.search(r"(?m)^module\s*$", txt)
    s = s.start() if s else 0
    m = re.compile(r"(?m)^(@\[expose\]|public section|namespace |section|noncomputable )").search(txt, s)
    return txt[s:m.start()] if m else txt[s:]


def under(mod, prefixes):
    return any(mod == q or mod.startswith(q + ".") for q in prefixes)


def unrename(dotted, table=None):
    for k, v in (RENAME if table is None else table).items():
        dotted = re.sub(rf"(?<![\w.]){re.escape(v)}(?![\w])", k, dotted)
    return dotted


def rename(txt, table=None):
    for k, v in (RENAME if table is None else table).items():
        txt = re.sub(rf"(?<![\w]){re.escape(k)}(?![\w])", v, txt)
        ks, vs = k.replace(".", "/"), v.replace(".", "/")
        txt = re.sub(rf"(?<![\w]){re.escape(ks)}(?![\w])", vs, txt)
    return txt


def read(path):
    with open(path) as fh:
        return fh.read()


def first_line(path):
    with open(path) as fh:
        return fh.readline()


class Part:
    """One part: its root, its source trees (in order, `""` the main tree), how its roots are found,
    whether its own files are read first, its renamed packages, and the paths gen-init writes."""

    def __init__(self, name, sources, roots, own_first, renames, gen_init_paths):
        self.name, self.sources, self._roots = name, sources, roots
        self.own_first, self.renames, self._gen_init_paths = own_first, renames, gen_init_paths
        self._files, self._imports = {}, {}

    # -- the part's view of a module path ---------------------------------------------------------
    def own_file(self, mod):
        """The part's own (not copied) file of `mod`, if any: a translation, a generated module, or
        a hand-written one."""
        p = os.path.join(ROOT, self.name, *mod.split(".")) + ".lean"
        if os.path.exists(p) and not is_copy_line(first_line(p), self.name):
            return p
        return None

    def source_file(self, mod):
        """(source root, file) of `mod` in the first source tree that has it, or None; a clash
        (two source parts, neither the main tree) stops the script unless gen-init writes `mod`."""
        found = []
        for s in self.sources:
            p = os.path.join(ROOT, *([s] if s else []), *mod.split(".")) + ".lean"
            if os.path.exists(p):
                found.append((s, p))
        parts = [f for f in found if f[0]]
        if len(parts) > 1 and mod not in self.gen_init_mods() and not mod.endswith(".Link"):
            sys.exit(f"copy-part: {self.name}: {mod} is in more than one source tree "
                     f"({', '.join(s + '/' for s, _ in parts)}): a clash to decide (notes/kvnet-part.md)")
        return found[0] if found else None

    def resolve(self, mod):
        """(source root or `self.name` for the part's own file, file) of `mod`, or None."""
        if mod not in self._files:
            r = None
            if self.own_first:
                o = self.own_file(mod)
                if o:
                    r = (self.name, o)
            if r is None:
                r = self.source_file(mod)
            self._files[mod] = r
        return self._files[mod]

    def imports_of(self, mod):
        """The module paths (unprefixed) `mod` imports, in the part's view; None if no file."""
        if mod not in self._imports:
            r = self.resolve(mod)
            if r is None:
                self._imports[mod] = None
            else:
                src, path = r
                self._imports[mod] = [self.view(strip(m.group(2), src))
                                      for m in IMPORT_RE.finditer(header_part(read(path)))]
        return self._imports[mod]

    def roots(self):
        return self._roots(self)

    def pkg(self, owned):
        """The Lean package path (dotted) the source trees name a package the part owns by (a renamed
        package's is the source's, `RENAME`; KvNet's packages are its own)."""
        d = owned.replace(os.sep, ".")
        return d if self.own_first else unrename(d, self.renames)

    def view(self, mod):
        """A module path a source file imports, as the part names it (its renamed packages')."""
        return rename(mod, self.renames) if self.own_first else mod

    def gen_init_mods(self):
        if not hasattr(self, "_gi"):
            self._gi = {p[:-len(".lean")].replace("/", ".") for p in self._gen_init_paths()}
        return self._gi

    # -- what the part translates -----------------------------------------------------------------
    def pieces(self):
        """The goose pieces into the part: (project, owned paths)."""
        out = []
        for p in goose.PROJECTS:
            for root, _, _, owned in goose.pieces(p):
                if root == self.name:
                    out.append((p, owned))
        return out

    def owned(self):
        return [o for _, os_ in self.pieces() for o in os_]

    def piece_source(self, owned):
        """The source tree whose goose piece translates the same package as the part's piece owning
        `owned` (its configuration, trusted code and manual proofs are that tree's), or None (a
        package only the part translates)."""
        for s in self.sources:
            for p in goose.PROJECTS:
                for root, _, _, ow in goose.pieces(p):
                    if root == s and owned in ow:
                        return s
        return None


def strip(mod, src):
    """`mod` as imported by a file of the tree `src`, without that tree's prefix."""
    return mod[len(src) + 1:] if src and mod.startswith(src + ".") else mod


# raft's API modules that are not about the noax raft: its raftpb has no enum name tables
# (`ccTypeNames`, `ccTransitionNames`) nor the main raftpb's message decoding (`msgDecodeRaw`), so
# these do not build in RaftNoAx (VM build, 2026-11-24); KvNet uses none of them.
NOT_NOAX = {"Proof.go_etcd_io.raft.v3.raftpb.CCEnumName", "Proof.go_etcd_io.raft.v3.PbMessage",
            "Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__String",
            "Spec.go_etcd_io.raft.v3.raftpb.ConfChangeTransition__String"}


def raft_api_roots():
    """Raft's own roots: its `Link` and the modules its clients may import (`importable` in
    etc/api/raft.txt, a trailing `.*` every main-tree module below the prefix), but the trace
    validation's (`Traced*`) and `NOT_NOAX`."""
    out = ["Proof.go_etcd_io.raft.v3.Link"]
    with open(os.path.join(ROOT, "etc", "api", "raft.txt")) as fh:
        for line in fh:
            w = line.split()
            if len(w) < 2 or w[0] != "importable" or ".Traced" in w[1]:
                continue  # (the trace-validation API, `RaftTla/`'s, not the part's)
            if w[1].endswith(".*"):
                d = os.path.join(ROOT, *w[1][:-2].split("."))
                out += sorted(os.path.relpath(os.path.join(dp, x), ROOT)[:-len(".lean")].replace(os.sep, ".")
                              for dp, _, fs in os.walk(d) for x in fs if x.endswith(".lean"))
            else:
                out.append(w[1])
    return [m for m in out if m not in NOT_NOAX]


def raftnoax_roots(part):
    """RaftNoAx's roots: raft's (`raft_api_roots`; KvNet takes its raft from the part)."""
    return raft_api_roots()


def own_roots(part):
    """The part's own hand-written modules under `Spec/` and `Proof/` (not copies, not generated),
    and the modules gen-init writes for it (built with the part, so their imports must be there)."""
    out = sorted(part.gen_init_mods())
    gi = part.gen_init_mods()
    for d in ("Spec", "Proof"):
        for dp, _, fs in os.walk(os.path.join(ROOT, part.name, d)):
            for x in fs:
                if not x.endswith(".lean"):
                    continue
                f = os.path.join(dp, x)
                m = os.path.relpath(f, os.path.join(ROOT, part.name))[:-len(".lean")].replace(os.sep, ".")
                if m in gi or is_copy_line(first_line(f)):
                    continue
                out.append(m)
    return sorted(out)


_GEN_INIT = []


def gen_init():
    if not _GEN_INIT:
        _GEN_INIT.append(load("gen_init", "gen-init.py"))
    return _GEN_INIT[0]


def raftnoax_gen_init_paths():
    gi = gen_init()
    return sorted(gi.part_paths(gi.PARTS["RaftNoAx"][0]))


def kvnet_gen_init_paths():
    return sorted(gen_init().kvnet_paths())


PARTS = {
    "RaftNoAx": Part("RaftNoAx", [""], raftnoax_roots, False, {}, raftnoax_gen_init_paths),
    "KvNet": Part("KvNet", ["Net", "WalTester", "RaftNoAx", ""], own_roots, True, {},
                  kvnet_gen_init_paths),
}


def closure(part):
    seen, todo = set(), list(part.roots())
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo += part.imports_of(m) or []
    return {m for m in seen if part.imports_of(m) is not None or under_translated(part, m)}


def under_translated(part, m):
    pkgs = [part.pkg(o) for o in part.owned()]
    return under(m, [f"{d}.{p}" for d in ("Code", "GeneratedProof") for p in pkgs])


def compute(part):
    """(the closure's modules the part has, with why; the files to write: part path -> text)."""
    P = part.name
    pkgs = [part.pkg(o) for o in part.owned()]
    seed_prefixes = [f"{d}.{p}" for d in ("Code", "GeneratedProof", "TrustedCode", "ManualProof") for p in pkgs]
    # every module of a renamed package goes with it, whether or not it reaches a seed
    seed_prefixes += [f"{d}.{k}" for d in ("Spec", "Proof") for k in part.renames if not part.own_first]
    cl = closure(part)
    gi = part.gen_init_mods()
    memo = {}

    def seed(m):
        r = part.resolve(m)
        return (under(m, seed_prefixes) or m in gi or (r is not None and r[0] != "")
                or m.endswith(".Link") and r is not None and r[0] == P)

    def reaches(m):
        if m not in memo:
            memo[m] = False
            memo[m] = seed(m) or any(reaches(x) for x in (part.imports_of(m) or []) if x in cl)
        return memo[m]
    members = {m for m in cl if reaches(m)}
    # the trusted code and manual proofs of the translated packages, whether or not in the closure
    # (the source tree's whose piece translates the package)
    for o in part.owned():
        s = part.piece_source(o)
        if s is None and part.sources != [""]:
            continue
        p = part.pkg(o)
        for d in ("TrustedCode", "ManualProof"):
            base = os.path.join(ROOT, *([s] if s else []), d, *p.split("."))
            for f in ([base + ".lean"] if os.path.isfile(base + ".lean") else []) + [
                    os.path.join(dp, x) for dp, _, fs in os.walk(base) for x in fs if x.endswith(".lean")]:
                m = os.path.relpath(f, os.path.join(ROOT, *([s] if s else [])))[:-len(".lean")].replace(os.sep, ".")
                members.add(m)
                part._files[m] = (s or "", f)
                part._imports.pop(m, None)
    why, files = {}, {}
    for m in sorted(members):
        if m.split(".")[0] in ("Code", "GeneratedProof"):
            if not under(m, seed_prefixes):
                sys.exit(f"copy-part: {P}: {m} reaches the part but is no translation of it: "
                         f"translate its package into the part (etc/goose.py)")
            why[m] = "etc/goose.py"
            continue
        if m in gi:
            why[m] = "etc/gen-init.py"
            continue
        r = part.resolve(m)
        if m.endswith(".Link") and (r is None or r[0] in (P, "")):
            why[m] = "etc/gen-link.py"
            continue
        if r is None:
            sys.exit(f"copy-part: {P}: {m} is imported but no tree has it")
        src, path = r
        if src == P:
            why[m] = "own"
            continue
        why[m] = "copied" + (f" from {src}/" if src else "")
        rel = os.path.relpath(path, ROOT)
        txt = read(path)
        if src and is_copy_line(txt.split("\n", 1)[0]):
            txt = txt.split("\n", 1)[1]
        head = header_part(txt)
        s = txt.index(head)

        def imp(mm, src=src, m=m):
            x = part.view(strip(mm.group(2), src))
            if x in members:
                return mm.group(1) + f"{P}.{x}"
            if src and mm.group(2).startswith(src + "."):
                sys.exit(f"copy-part: {P}: {m} (from {src}/) imports {mm.group(2)}, which the part "
                         f"does not have")
            return mm.group(1) + x
        txt = txt[:s] + IMPORT_RE.sub(imp, head) + txt[s + len(head):]
        if part.renames:
            txt = rename(txt, part.renames)
        if part.renames and not part.own_first:
            dst = os.path.join(P, rename(rel))
        else:
            dst = os.path.join(P, *m.split(".")) + ".lean"
        files[dst] = f"-- {header(P)} `{rel}` {NOTE}.\n" + txt
    prune_unimported(part, why, files)
    # the Goose configuration of the translated packages
    for o in part.owned():
        s = part.piece_source(o)
        if s is None and part.sources != [""]:
            continue
        src_o = part.pkg(o).replace(".", os.sep)
        base = os.path.join(ROOT, *([s] if s else []), "Code", src_o)
        tomls = ([base + ".toml"] if os.path.isfile(base + ".toml") else []) + sorted(
            os.path.join(dp, x) for dp, _, fs in os.walk(base) for x in fs if x.endswith(".toml"))
        for f in tomls:
            rel = os.path.relpath(f, ROOT)
            txt = read(f)
            if s and is_copy_line(txt.split("\n", 1)[0]):
                txt = txt.split("\n", 1)[1]
            dst = os.path.join(P, rename(rel)) if not s else os.path.join(P, os.path.relpath(f, os.path.join(ROOT, s)))
            files[dst] = f"# {header(P)} `{rel}` {NOTE}.\n" + txt
    return why, files


def prune_unimported(part, why, files):
    """Drop the copies no module of the part imports (to a fixpoint), but the roots (`Results`,
    `TopLevelRobustness`, `Link`): modules of the main tree's closure that only the main tree's
    versions of the part's own files import (stage 2 replaced the `proto` axioms' callers, so the
    copies of those axioms, `DescribeConfChange`'s, `fmt.Sprintf`'s and `strings.Join`'s were left
    behind, built but unreached; prove-raftex, 2026-11-20). The part's other modules (its own,
    the generated ones) are read from disk."""
    P = part.name

    def mod_of(path):
        return path[:-len(".lean")].replace(os.sep, ".")
    texts = {}
    for dp, _, fs in os.walk(os.path.join(ROOT, P)):
        for x in fs:
            if x.endswith(".lean"):
                p = os.path.relpath(os.path.join(dp, x), ROOT)
                t = read(os.path.join(ROOT, p))
                if not is_copy_line(t.split("\n", 1)[0], P):  # a stale copy is not the part's
                    texts[mod_of(p)] = t
    copied = {}
    for p, t in files.items():
        if p.endswith(".lean"):
            texts[mod_of(p)] = t
            copied[mod_of(p)] = p
    importers = {}
    gi = {f"{P}.{x}" for x in part.gen_init_mods()} if part.own_first else set()
    for m, t in texts.items():
        for mm in IMPORT_RE.finditer(header_part(t)):
            x = mm.group(2)
            # (a module gen-init writes for the part imports the main tree's `X` until the part has
            # its copy, which gen-init then imports on its next run: it counts as importing it)
            if m in gi and f"{P}.{x}" in copied:
                x = f"{P}.{x}"
            importers.setdefault(x, set()).add(m)
    alive = set(texts)
    roots = {f"{P}.{r}" for r in part.roots()}
    changed = True
    while changed:
        changed = False
        for m in sorted(alive & set(copied)):
            if m.endswith((".Results", ".TopLevelRobustness", ".Link")) or m in roots:
                continue
            if m.startswith((f"{P}.TrustedCode.", f"{P}.ManualProof.")) and part.sources != [""]:
                continue  # (a translated package's, kept whether or not imported)
            if not any(i in alive for i in importers.get(m, ())):
                alive.discard(m)
                changed = True
    for m in set(copied) - alive:
        del files[copied[m]]
        why.pop(unrename(m[len(P) + 1:], part.renames), None)


def existing_copies(P):
    out = set()
    for d in ("Code", "Spec", "Proof", "TrustedCode", "ManualProof"):
        for dp, _, fs in os.walk(os.path.join(ROOT, P, d)):
            for x in fs:
                if not x.endswith((".lean", ".toml")):
                    continue
                f = os.path.join(dp, x)
                if is_copy_line(first_line(f), P):
                    out.add(os.path.relpath(f, ROOT))
    return out


def run(part, check, listing):
    P = part.name
    why, files = compute(part)
    if listing:
        for m, w in sorted(why.items()):
            print(f"{P:9} {w:22} {m}")
        return 0
    bad, own = [], []
    for path, txt in sorted(files.items()):
        full = os.path.join(ROOT, path)
        old = read(full) if os.path.exists(full) else None
        if old == txt:
            continue
        if old is not None and not is_copy_line(old.split("\n", 1)[0], P):
            own.append(path)
            continue
        if check:
            bad.append(path)
        else:
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "w") as fh:
                fh.write(txt)
    for path in sorted(existing_copies(P) - set(files)):
        if check:
            bad.append(path + " (stale)")
        else:
            os.remove(os.path.join(ROOT, path))
    counts = {}
    for w in why.values():
        w = w.split(" ")[0]
        counts[w] = counts.get(w, 0) + 1
    summary = ", ".join(f"{n} {w}" for w, n in sorted(counts.items()))
    if own:
        summary += f"; {len(own)} the part's own: " + " ".join(own)
    if check:
        for b in bad:
            print(f"copy-part: differs from the copy: {b}")
        print(f"copy-part: {P}: {len(files)} files ({summary}); {len(bad)} differ", file=sys.stderr)
        return 1 if bad else 0
    print(f"copy-part: {P}: {len(files)} files ({summary})", file=sys.stderr)
    return 0


def main(argv):
    check, listing = "--check" in argv, "--list" in argv
    names = [argv[i + 1] for i, a in enumerate(argv) if a == "--part"] or list(PARTS)
    for n in names:
        if n not in PARTS:
            sys.exit(f"copy-part: no part {n} (parts: {' '.join(PARTS)})")
    rc = 0
    for n in names:
        rc |= run(PARTS[n], check, listing)
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
