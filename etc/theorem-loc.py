#!/usr/bin/env python3
"""Per-theorem line counts: the Lean trusted computing base (TCB) and the Go code verified.

usage: etc/theorem-loc.py THEOREM... [--collection FILE] [--file PATH]
                          [--list-tcb] [--list-verified] [--json OUT] [--tsv]
                          [--go-src DIR] [--no-go] [--refresh-go]

For each top-level theorem (e.g. `etcd_safe`, found in a `Results.lean` of `Proof/` or a
part's `<root>/Proof/`), print

  * TCB lines: the non-blank, non-comment Lean lines of this repository's `Spec/` and `Proof/` (and
    the parts') that the theorem trusts -- the axioms its proof rests on, and the definitions that
    its *statement* and those axioms are written in terms of, transitively through definition
    bodies but never into proofs (theorems, lemmas).  Perennial, Iris, Lean and Goose's output
    (`Code/`, `GeneratedProof/`, `TrustedCode/`, `ManualProof/`) are trusted as a whole and not
    counted.  Split into
      - premises: what the statement reaches (its hypotheses, the program, ...);
      - axioms:   the axioms, and the definitions reached only through them (mostly the Iris
                  specs they assert: `X.wp_proof : X.spec`).
  * Verified Go lines: the code lines (`etc/verified-code.go`'s `sloc`: lines from `func` to the
    closing brace holding code) of the Go functions whose proofs the theorem's proof reaches --
    a `T.M.wp_proof` that is a theorem, not an axiom -- split into code outside this repository
    (etcd, Raft, bbolt, Kubernetes, ...: "system") and this repository's own (`examples/`,
    `third_party/`: drivers, models, Porcupine).  Generated files, test-helper packages and the
    modules a project's `counted_modules` leaves out are excluded, as etc/verified-code.py does;
    Go's standard library (no source here) is not counted.

The axioms are those of the `etc/tcb-collections/*.txt` file whose `roots` patterns match the
theorem's `Results.lean` (or its name), family collections (with `axioms` lines) excepted;
`--collection` picks one.  Those files' `axiom` lines are
etc/tcb-report.py's baseline (`--collection FILE --check --update` refreshes one after a build),
and a collection covers every root of its file: for a `Results.lean` with several theorems, each
gets the file's union.

Needs no Lean build: everything is read off the source text, so it approximates what
etc/tcb-report.lean computes from the elaborated environment.  Not followed: instances found by
typeclass resolution, coercions, notation and macros defined here, generalized field notation on
local variables (`x.foo`, `x : T` local) and anonymous-constructor notation (`.foo`); a name
overloaded through several `open`s counts every candidate.  Verified methods with no Go body of
their own (promoted from an embedded field, interface methods) and Go's standard library are
reported as unmapped.

The Go sources are etc/verified-code.py's: `--go-src DIR` (default .lake/go-src) holds a checkout of
each project of etc/goose.py at its pinned revision (cloned or fetched there if not), with the
prophecy patches applied (etc/proph_patch.py); packages a project translates from outside its
checkout (`k8s.io/apiserver/...` for the in-repository Kubernetes examples) are found with
`go list` in the project's module.  The function list is cached in
.lake/theorem-loc-gofuncs.json (`--refresh-go` rebuilds it; `--no-go` skips the Go counts).
"""

import argparse
import collections
import glob
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
import goose  # noqa: E402
import proof_roots  # noqa: E402

PARTS = list(proof_roots.PART_ROOTS)
PROJECT_SUBDIRS = ("Spec", "Proof")
PROOF_KINDS = ("theorem", "lemma", "example")

# --- reading Lean source -------------------------------------------------------

IDPART = r"(?:«[^»\n]*»|[^\W\d][\w'!?]*)"
TOKEN = re.compile(r"(?<![\w.'«»!?])(?:_root_\.)?" + IDPART + r"(?:\." + IDPART + r")*")
MODS = r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public|scoped|local|meta)\s+)*"
DECL_KW = ("def", "abbrev", "theorem", "lemma", "structure", "class", "inductive", "instance",
           "axiom", "opaque", "example", "irreducible_def")
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*" + MODS + r"(class\s+inductive|" + "|".join(DECL_KW)
                     + r")\b(.*)$")
SCOPE_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)*" + MODS
                      + r"(namespace|section|end|open|variable|mutual)\b\s*(.*)")
CMD_RE = re.compile(r"^(?:@\[|/--|#|" + "|".join(
    list(DECL_KW) + ["namespace", "end", "section", "variable", "open", "universe", "set_option",
                     "attribute", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
                     "macro", "macro_rules", "syntax", "elab", "elab_rules", "deriving", "mutual",
                     "import", "module", "public", "private", "protected", "noncomputable",
                     "partial", "unsafe", "local", "scoped", "add_decl_doc", "export", "omit",
                     "include", "initialize", "meta", "declare_syntax_cat", "run_cmd", "nonrec"])
    + r")\b")
KEYWORDS = set("""fun λ let have show from by at with match if then else do return in for unless
 where deriving forall exists Type Prop Sort true false calc this mut try catch finally extends
 structure class instance def theorem abbrev open namespace section end variable universe
 iprop""".split())
IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)


def norm_name(n):
    return n.replace("«", "").replace("»", "")


def strip(text):
    """`text` with comments and string/char literals blanked (newlines kept)."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j + 1
        elif (c == "'" and i + 2 < n
              and (text[i + 2] == "'" or (text[i + 1] == "\\" and 0 < text.find("'", i + 2) - i < 8))
              and not (i > 0 and (text[i - 1].isalnum() or text[i - 1] in "_'"))):
            j = text.find("'", i + 2 if text[i + 1] == "\\" else i + 1)
            for k in range(i + 1, j):
                out[k] = " "
            i = j + 1
        else:
            i += 1
    return "".join(out)


class Decl:
    __slots__ = ("name", "kind", "file", "start", "end", "code", "ns", "opens", "vars",
                 "project", "cat")


def module_file(mod):
    p = os.path.join(ROOT, *mod.split(".")) + ".lean"
    return p if os.path.exists(p) else None


def is_project_file(path):
    rel = os.path.relpath(path, ROOT).split(os.sep)
    if rel[0] in PROJECT_SUBDIRS:
        return True
    return len(rel) > 1 and rel[0] in PARTS and rel[1] in PROJECT_SUBDIRS


_STRIPPED = {}


def stripped_lines(path):
    if path not in _STRIPPED:
        with open(path, encoding="utf-8") as f:
            _STRIPPED[path] = strip(f.read()).split("\n")
    return _STRIPPED[path]


def import_closure(path):
    seen, todo = set(), [path]
    while todo:
        p = todo.pop()
        if p in seen:
            continue
        seen.add(p)
        for m in IMPORT_RE.finditer("\n".join(stripped_lines(p))):
            q = module_file(m.group(1))
            if q and q not in seen:
                todo.append(q)
    return seen


_PARSED = {}


def parse_file(path):
    """The declarations of a Lean file, with their scopes, and the alias names (structure
    fields and constructors, inductive constructors) that stand for one of them."""
    if path in _PARSED:
        return _PARSED[path]
    with open(path, encoding="utf-8") as f:
        rl = f.read().split("\n")
    cl = stripped_lines(path)
    proj = is_project_file(path)
    scopes = [("root", [], [], [])]  # (kind, namespace components, opens, variable commands)
    decls, aliases = [], []
    starts = {i for i, l in enumerate(cl) if l.strip() and not l[0].isspace() and CMD_RE.match(l)}
    starts |= {i for i, l in enumerate(rl) if l.startswith("/--") or l.startswith("@[")}
    starts = sorted(starts)
    pending = None  # the doc comment / attribute line a declaration starts at
    for idx, i in enumerate(starts):
        nxt = starts[idx + 1] if idx + 1 < len(starts) else len(cl)
        s = cl[i].strip()
        if not s or (s.startswith("@[") and not DECL_RE.match(s)
                     and not re.search(r"\bsection\b", s)):
            pending = i if pending is None else pending
            continue
        body = "\n".join(cl[i:nxt])
        m = SCOPE_RE.match(s)
        if m:
            kw, rest = m.group(1), m.group(2).strip()
            if kw == "namespace":
                scopes.append(("ns", rest.split()[0].split("."), [], []))
            elif kw in ("section", "mutual"):
                scopes.append((kw, [], [], []))
            elif kw == "end":
                if len(scopes) > 1:
                    scopes.pop()
            elif kw == "open":
                if not re.search(r"\bin\s*$", body.strip()) and " in\n" not in body:
                    scopes[-1][2].extend(t for t in TOKEN.findall(body[body.find("open") + 4:])
                                         if t not in ("scoped", "hiding", "renaming"))
            elif kw == "variable":
                scopes[-1][3].append(body)
            pending = None
            continue
        m = DECL_RE.match(s)
        if not m:
            pending = None
            continue
        kw = "class" if m.group(1).startswith("class") else m.group(1)
        rest = re.sub(r"^\s*\(priority\s*:=[^)]*\)", "", m.group(2)).lstrip()
        nm = TOKEN.match(rest)
        name = nm.group(0) if nm and kw != "example" else None
        if kw == "instance" and name and rest[len(name):].lstrip()[:1] not in (":", "(", "{", "[", "⦃"):
            name = None  # an anonymous instance
        e = nxt - 1
        while e > i and not rl[e].strip():
            e -= 1
        d = Decl()
        d.kind, d.file, d.start, d.end, d.project, d.cat = kw, path, (pending if pending is not None else i), e, proj, None
        pending = None
        d.code = "\n".join(cl[i:e + 1])
        d.ns = [c for sc in scopes for c in sc[1]]
        d.opens = [o for sc in scopes for o in sc[2]]
        d.vars = [v for sc in scopes for v in sc[3]]
        d.name = None if name is None else (
            name[len("_root_."):] if name.startswith("_root_.") else ".".join(d.ns + [name]))
        decls.append(d)
        if d.name and kw in ("structure", "class", "inductive"):
            aliases.append((d.name + ".mk", d))
            for bl in cl[i + 1:e + 1]:
                for pat in (r"^\s+\|\s*(" + IDPART + r")", r"^\s+(" + IDPART + r")\s*::"):
                    fm = re.match(pat, bl)
                    if fm:
                        aliases.append((d.name + "." + fm.group(1), d))
                        break
                else:
                    fm = re.match(r"^\s{2,4}\(?((?:" + IDPART + r"\s+)*" + IDPART + r")\s*(?::|:=)", bl)
                    if fm:
                        aliases += [(d.name + "." + f, d) for f in fm.group(1).split()]
            for par in re.findall(r"extends\s+([^:\n]+?)(?:\s+where|\s*:|$)", d.code, re.M):
                aliases += [(d.name + ".to" + p.split(".")[-1], d) for p in TOKEN.findall(par)]
    _PARSED[path] = (decls, aliases)
    return _PARSED[path]


def binders(code):
    """Names bound in `code` (approximately), which shadow global names."""
    b = set()
    for m in re.finditer(r"[({\[⦃]\s*((?:" + IDPART + r"\s+)*" + IDPART + r")\s*:(?!=)", code):
        b.update(m.group(1).split())
    for m in re.finditer(r"(?:fun|λ|∀|∃!?|Σ|Π)\s+([^,=↦]*?)(?:,|=>|↦)", code):
        b.update(TOKEN.findall(m.group(1)))
    for m in re.finditer(r"\b(?:let|have|obtain)\s+(" + IDPART + r")", code):
        b.add(m.group(1))
    return b


def statement_of(code):
    """A declaration's signature: up to its first top-level `:=` (or `where`)."""
    depth = 0
    for i, c in enumerate(code):
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and code.startswith(":=", i):
            return code[:i]
        elif depth == 0 and re.match(r"\swhere\b", code[i:i + 7]):
            return code[:i]
    return code


class Env:
    """The declarations of the import closure of one file, with Lean-style name resolution."""

    def __init__(self, path):
        self.index = collections.defaultdict(list)
        self.decls = []
        for p in sorted(import_closure(path)):
            ds, al = parse_file(p)
            self.decls += ds
            for d in ds:
                if d.name:
                    self.index[norm_name(d.name)].append(d)
            for n, d in al:
                self.index[norm_name(n)].append(d)

    def get(self, name):
        return self.index.get(norm_name(name))

    def resolve(self, tok, d, locs):
        """What `tok`, written in declaration `d` with the local names `locs`, may refer to:
        `ns ++ tok` for the enclosing namespaces (innermost first), plus each `open`; else the
        same for a prefix of `tok` (a projection `C.f` of a constant `C`)."""
        if tok.startswith("_root_."):
            return self.get(tok[7:]) or []
        comps = tok.split(".")
        if comps[0] in locs or tok in KEYWORDS:
            return []
        for k in range(len(comps), 0, -1):
            t = ".".join(comps[:k])
            hits = []
            for i in range(len(d.ns), -1, -1):
                h = self.get(".".join(d.ns[:i] + [t]))
                if h:
                    hits = list(h)
                    break
            for o in d.opens:
                for i in range(len(d.ns), -1, -1):
                    h = self.get(".".join(d.ns[:i] + [o, t]))
                    if h:
                        hits += h
                        break
            if hits:
                return hits
        return []

    def walk(self, seeds, seen, visit):
        """Breadth over `(decl, text)`: every declaration a token of `text` resolves to is
        passed to `visit(decl)` once; when it returns true its own text is walked too."""
        todo = list(seeds)
        while todo:
            d, text = todo.pop()
            locs = binders(text)
            for tok in set(TOKEN.findall(text)):
                for t in self.resolve(tok, d, locs):
                    if id(t) in seen:
                        continue
                    seen.add(id(t))
                    if visit(t):
                        todo.append((t, t.code + "\n" + "\n".join(t.vars)))


def code_lines(d):
    return sum(1 for l in stripped_lines(d.file)[d.start:d.end + 1] if l.strip())


def find_theorem(name, file=None):
    if file is None:
        dirs = [os.path.join(ROOT, d) for d in ["Proof", "Spec"] + PARTS]
        r = subprocess.run(["grep", "-rlE", r"^(theorem|lemma) " + re.escape(name) + r"([[:space:]({:]|$)",
                            "--include=*.lean", *[d for d in dirs if os.path.isdir(d)]],
                           capture_output=True, text=True)
        cands = r.stdout.split()
        if len(cands) != 1:
            sys.exit(f"theorem-loc: {name}: {'found in ' + ', '.join(cands) if cands else 'not found'}"
                     "; pass --file")
        file = cands[0]
    return os.path.abspath(file)


def find_collection(rel, name):
    """The `etc/tcb-collections/*.txt` whose `roots` patterns match the theorem's file (preferred)
    or its name; of several, the one with the fewest axioms.  A family collection (one with
    `axioms PATTERN` lines, grpc.txt) is never picked: its baseline is only the family's axioms,
    under every root its patterns match, not one theorem's trust base."""
    by_file, by_name = [], []
    for f in sorted(glob.glob(os.path.join(ROOT, "etc", "tcb-collections", "*.txt"))):
        with open(f, encoding="utf-8") as fh:
            lines = fh.read().splitlines()
        if any(l.startswith("axioms ") for l in lines):
            continue
        pats = [l.split(None, 1)[1] for l in lines if l.startswith("roots ")]
        n = sum(1 for l in lines if l.startswith("axiom "))
        if any(re.search(p, rel) for p in pats):
            by_file.append((n, f))
        elif any(re.search(p, name) for p in pats):
            by_name.append((n, f))
    c = sorted(by_file) or sorted(by_name)
    return c[0][1] if c else None


# --- the TCB -----------------------------------------------------------------------


def tcb(env, root, collection):
    """The trusted declarations of `root`: (decls with `.cat` in stmt/axiom/axvocab, the
    collection's axioms not found)."""
    seen, out = {id(root)}, []

    def visit(cat):
        def v(t):
            if t.kind in PROOF_KINDS:
                return False
            if t.project:
                t.cat = cat
                out.append(t)
            return True
        return v

    env.walk([(root, statement_of(root.code) + "\n" + "\n".join(root.vars))], seen, visit("stmt"))
    missing, seeds = [], []
    if collection:
        with open(collection, encoding="utf-8") as f:
            names = [l.split()[1] for l in f if l.startswith("axiom ")]
        for n in names:
            full = n if n.startswith("Perennial.") else proof_roots.namespace() + n
            hits = env.get(full) or []
            hits = [d for d in hits if d.kind == "axiom"] or hits
            if not hits:
                missing.append(n)
                continue
            a = hits[0]
            if id(a) not in seen:
                seen.add(id(a))
                if a.project:
                    a.cat = "axiom"
                    out.append(a)
            seeds.append((a, a.code + "\n" + "\n".join(a.vars)))
        env.walk(seeds, seen, visit("axvocab"))
    return out, missing


# --- the Go code verified -----------------------------------------------------------


def load_verified_code():
    spec = importlib.util.spec_from_file_location("verified_code", os.path.join(ROOT, "etc", "verified-code.py"))
    vc = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(vc)
    return vc


def go_functions(go_src, refresh):
    """Every Go function of the projects' sources (and of the out-of-checkout modules their
    translated packages are in), each with `root` (the project's module root, "" for the main
    tree), `inrepo` (code of this repository) and `counted`."""
    cache = os.path.join(ROOT, ".lake", "theorem-loc-gofuncs.json")
    with open(os.path.join(ROOT, "etc", "goose.py"), "rb") as f:
        key = hashlib.sha256(f.read() + os.path.abspath(go_src).encode()).hexdigest()
    if not refresh and os.path.exists(cache):
        with open(cache) as f:
            c = json.load(f)
        if c.get("key") == key:
            return c["funcs"]
    vc = load_verified_code()
    src = vc.go_sources(go_src)
    out = []
    env = dict(os.environ, GOFLAGS="-mod=mod")
    for name, d in src.items():
        p = vc.PROJECTS[name]
        dirs = [d]
        # translated packages outside the checkout's own module (a dependency's, from the module cache)
        ext = [q for q in p.packages if not (q == "." or q.startswith("./"))]
        if ext and p.local is not None:
            r = subprocess.run(["go", "list", "-e", "-find", "-f",
                                "{{if not .Standard}}{{with .Module}}{{.Dir}}{{end}}{{end}}", *ext],
                               cwd=d, capture_output=True, text=True, env=env)
            dirs += sorted({x for x in r.stdout.split() if x and os.path.isdir(x)
                            and not os.path.abspath(x).startswith(ROOT)})
        print(f"theorem-loc: listing the Go functions of {name}", file=sys.stderr)
        counted = set(p.counted_modules or [])
        for g in vc.go_functions(dirs):
            inrepo = g["src"] == d and p.local is not None
            ok = not g["generated"] and not vc.TEST_PKG.search(g["pkg"][len(g["module"]):])
            if g["src"] == d and counted and g["module"] not in counted:
                ok = False
            out.append(dict(root=p.root or "", pkg=g["pkg"], recv=g["recv"].lstrip("*"),
                            name=g["name"], file=g["file"], line=g["line"], sloc=g["sloc"],
                            module=g["module"], inrepo=inrepo, counted=ok, project=name))
    os.makedirs(os.path.dirname(cache), exist_ok=True)
    with open(cache, "w") as f:
        json.dump(dict(key=key, funcs=out), f)
    return out


def go_index(funcs):
    """(module root, package as Lean paths spell it) -> {(recv, name): function}; a function in
    several projects' sources is the one counted (else the first)."""
    ix = collections.defaultdict(dict)
    for g in funcs:
        k = (g["root"], re.sub(r"[.\-]", "_", g["pkg"]))
        prev = ix[k].get((g["recv"], g["name"]))
        if prev is None or (g["counted"] and not prev["counted"]):
            ix[k][(g["recv"], g["name"])] = g
    return ix


def verified(env, root, goix):
    """The Go functions whose proofs `root`'s proof reaches, and the proofs reached that are of
    no Go function here (standard library, promoted or interface methods)."""
    seen, proofs, assumed = {id(root)}, [], []

    def visit(t):
        if t.name and t.name.endswith(".wp_proof") and t.project:
            (proofs if t.kind in ("theorem", "lemma") else assumed).append(t)
        return t.kind in ("theorem", "lemma") and t.project

    env.walk([(root, root.code)], seen, visit)
    funcs, unmapped = {}, []
    for t in proofs:
        rel = os.path.relpath(t.file, ROOT).split(os.sep)
        mroot = ""
        if rel[0] in PARTS:
            mroot, rel = rel[0], rel[1:]
        dirs = rel[1:-1]  # below Proof/
        comps = [norm_name(c) for c in t.name.split(".")[:-1]]
        cands = ([(comps[-2], comps[-1])] if len(comps) >= 2 else []) + [("", comps[-1])]
        # spec variants of one function (`Stats_kv`): drop `_suffix`es
        for rv, nm in list(cands):
            ps = nm.split("_")
            cands += [(rv, "_".join(ps[:j])) for j in range(len(ps) - 1, 0, -1)]
        hit = None
        for k in range(len(dirs), 0, -1):
            for r in ([mroot, ""] if mroot else [""]):
                fs = goix.get((r, "/".join(dirs[:k])))
                if fs:
                    hit = next((fs[c] for c in cands if c in fs), None)
                    if hit:
                        break
            if hit:
                break
        if hit:
            funcs[(hit["pkg"], hit["recv"], hit["name"], hit["root"])] = hit
        else:
            unmapped.append(t)
    return list(funcs.values()), unmapped, assumed


# --- the report ----------------------------------------------------------------------


def n_axioms(coll):
    """The axioms of a collection (its baseline's `axiom` lines: etc/tcb-report.py's count)."""
    if not coll:
        return 0
    with open(coll, encoding="utf-8") as f:
        return sum(1 for l in f if l.startswith("axiom "))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    ap.add_argument("theorems", nargs="+")
    ap.add_argument("--collection")
    ap.add_argument("--file")
    ap.add_argument("--list-tcb", action="store_true")
    ap.add_argument("--list-verified", action="store_true")
    ap.add_argument("--json")
    ap.add_argument("--tsv", action="store_true")
    ap.add_argument("--go-src", default=os.path.join(ROOT, ".lake", "go-src"))
    ap.add_argument("--no-go", action="store_true")
    ap.add_argument("--refresh-go", action="store_true")
    args = ap.parse_args()

    goix = None if args.no_go else go_index(go_functions(args.go_src, args.refresh_go))
    rows, details = [], {}
    for name in args.theorems:
        file = find_theorem(name, args.file)
        rel = os.path.relpath(file, ROOT)
        coll = args.collection or find_collection(rel, name)
        env = Env(file)
        root = next((d for d in env.decls if d.file == file and d.name
                     and d.name.split(".")[-1] == name and d.kind in ("theorem", "lemma")), None)
        if root is None:
            sys.exit(f"theorem-loc: {name} not found in {rel}")
        for d in env.decls:
            d.cat = None
        decls, missing = tcb(env, root, coll)
        n = {c: sum(code_lines(d) for d in decls if d.cat == c) for c in ("stmt", "axiom", "axvocab")}
        row = dict(theorem=name, file=rel,
                   collection=os.path.relpath(coll, ROOT) if coll else None,
                   axioms=n_axioms(coll),
                   axioms_missing=missing, tcb=sum(n.values()), tcb_premises=n["stmt"],
                   tcb_axioms=n["axiom"] + n["axvocab"], tcb_axiom_decls=n["axiom"])
        det = dict(tcb=[dict(name=d.name, kind=d.kind, cat=d.cat, file=os.path.relpath(d.file, ROOT),
                             start=d.start + 1, end=d.end + 1, lines=code_lines(d)) for d in decls])
        if goix is not None:
            fs, unmapped, assumed = verified(env, root, goix)
            cf = [g for g in fs if g["counted"]]
            row.update(verified_go=sum(g["sloc"] for g in cf if not g["inrepo"]),
                       verified_go_inrepo=sum(g["sloc"] for g in cf if g["inrepo"]),
                       verified_funcs=sum(1 for g in cf if not g["inrepo"]),
                       assumed_funcs=len(assumed), unmapped_proofs=len(unmapped))
            det.update(verified=sorted(fs, key=lambda g: (g["pkg"], g["recv"], g["name"])),
                       unmapped=[dict(name=t.name, file=os.path.relpath(t.file, ROOT)) for t in unmapped])
        rows.append(row)
        details[name] = det
        if not coll:
            print(f"theorem-loc: {name}: no etc/tcb-collections file matches {rel}; "
                  "axioms not counted (pass --collection)", file=sys.stderr)
        if missing:
            print(f"theorem-loc: {name}: {len(missing)} axioms of {row['collection']} not found in "
                  f"the source (stale baseline?): {' '.join(missing[:10])}", file=sys.stderr)

    cols = ["theorem", "tcb", "tcb_premises", "tcb_axioms", "axioms"]
    if goix is not None:
        cols += ["verified_go", "verified_go_inrepo", "verified_funcs", "assumed_funcs", "unmapped_proofs"]
    if args.tsv:
        print("\t".join(cols))
        for r in rows:
            print("\t".join(str(r[c]) for c in cols))
    else:
        w = max(len(r["theorem"]) for r in rows)
        print(f"{'theorem':<{w}}  " + "  ".join(f"{c:>12}" for c in cols[1:]))
        for r in rows:
            print(f"{r['theorem']:<{w}}  " + "  ".join(f"{r[c]:>12,}" for c in cols[1:]))
    for name in args.theorems:
        det = details[name]
        if args.list_tcb:
            print(f"\n{name}: trusted declarations (code lines, part, kind, name, place)")
            for d in sorted(det["tcb"], key=lambda d: (d["cat"], d["file"], d["start"])):
                print(f"  {d['lines']:5d}  {d['cat']:7s} {d['kind']:9s} {d['name']}  {d['file']}:{d['start']}-{d['end']}")
        if args.list_verified and "verified" in det:
            print(f"\n{name}: verified Go functions (sloc, counted, in repository, function)")
            for g in det["verified"]:
                fn = f"{g['pkg']}.{g['recv'] + '.' if g['recv'] else ''}{g['name']}"
                print(f"  {g['sloc']:5d}  {'counted' if g['counted'] else 'not-cnt'} "
                      f"{'in-repo' if g['inrepo'] else 'system '} {fn}")
            for u in det["unmapped"]:
                print(f"      -  unmapped {u['name']}  ({u['file']})")
    if args.json:
        with open(args.json, "w") as f:
            json.dump(dict(rows=rows, details=details), f, indent=1)


if __name__ == "__main__":
    main()
