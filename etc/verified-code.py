#!/usr/bin/env python3
"""Account for how much of the translated Go code is verified.

usage: etc/verified-code.py [-o REPORT.txt|REPORT.md]... [--markdown] [--functions]
                            [--package PREFIX]... [--go-src DIR] [--json TCB.json]
                            [--reuse]

  -o           where to write the report (default: stdout), in Markdown if the file
               name ends in `.md` and in plain text otherwise; may be repeated
  --markdown   print Markdown instead of plain text on stdout
  --functions  also list every function, with its state, of the files of the "by
               file" tables
  --package    a summary row for the Go packages at or below PREFIX (an import path),
               and the "by file" tables and --functions only of those; may be repeated
  --go-src     where the Go sources are: DIR/<project> for each project of
               `etc/goose.py`, a checkout of its Go repository at the revision pinned
               there; default .lake/go-src, cloned or fetched there (shallow) and
               checked out at the pinned revision
  --json       the output of etc/tcb-report.lean, shared with etc/tcb-report.py
               (default .lake/tcb.json); --reuse skips re-running Lean if it is of
               the current root modules (etc/proof_roots.py)

For a Goose verification project laid out as CLAUDE.md describes; nothing in it names
a project.  Needs a built project (`lake build`) and `go` (to parse the Go sources, with
`etc/verified-code.go`).  Every Go function and method is in exactly one state:

  * verified   -- it has a spec, proved: this repository's `Proof/<fn>.lean` is a
                  theorem whose proof has no `sorry` of its own (read off the
                  elaborated environment, as `etc/tcb-report.py` does).  Its callees'
                  specs may be assumed or unfinished;
                  "sorry-free" counts this repository's verified functions whose
                  linked result reaches no `sorry` at all;
  * unfinished -- it has a spec whose proof has a `sorry` of its own;
  * assumed    -- its spec is an axiom (the trust boundary);
  * translated -- Goose translates it, but nothing specifies it;
  * not translated.
A function of a package Goose translates as types and names only (no bodies) is not
translated; the tables count these as "names only".

The projects (the Go repositories, their pinned revisions, the packages translated
into `Code/` and the Go modules counted, `counted_modules`) are `etc/goose.py`'s; each
project's code is counted apart.  The specs are those of the linked results of every
`Link.lean` under `Proof/` (etc/proof_roots.py), each about the functions of the
project whose translation its directory names (the one owning `Code/<that directory>`,
or `<root>/Code/...` for a part's `<root>/Proof/...`).  A spec of a package whose Go
code is not in the sources (a dependency's, translated too, or a part's) is not
counted, but listed with that package.

Per project the report shows its modules (if more than one), the packages Goose
translates any of (with bodies, or names only), and by file: every file of the packages
Goose translates with bodies, and every other file with a function Goose translates
with its body or specifies (in a package translated names-only but for some
functions).

Code is measured in functions and in Go code lines: the lines from `func` to the
closing brace that hold code (not blank, not only comments).  Type, constant and
variable declarations are not counted.  Excluded from the totals, and listed: test
files, test-helper packages, generated files, and the modules of a checkout that its
project's `counted_modules` leaves out (tests, tools).
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys
import textwrap

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True  # no etc/__pycache__
sys.path.insert(0, os.path.join(ROOT, "etc"))
import goose  # noqa: E402  (etc/goose.py: the projects, their pins and libraries)

PROJECTS = {p.name: p for p in goose.PROJECTS}
import proof_roots  # noqa: E402  (etc/proof_roots.py: the root modules, running Lean)

# The namespace of this repository's declarations (not part of a spec's name).
NS = proof_roots.namespace()


def link_project(mod):
    """The project (of `etc/goose.py`) whose Go functions the linked results of `mod` are
    about: the one owning the translation of the package directory its path names
    (`Proof.<dir>.Link`: `Code/<dir>`; `<root>.Proof.<dir>.Link`: `<root>/Code/<dir>`)."""
    parts = mod.split(".")[:-1]
    root = parts[0] if parts[0] in proof_roots.PART_ROOTS else ""
    d = "/".join(parts[2:] if root else parts[1:])
    for p in goose.PROJECTS:
        owned = [(r, o) for r, _, _, own in goose.pieces(p) for o in own]
        if any(r == root and (d == o or d.startswith(o + "/")) for r, o in owned):
            return p.name
    sys.exit(f"verified-code: no project of etc/goose.py translates {d} (for {mod})")


# The modules of linked results (each states `T.wp_M : T.M.spec`): every `Link.lean`
# under `Proof/` -> the project whose functions they are about.
LINKS = {m: link_project(m) for m in proof_roots.link_modules()}
# The namespace each Link names its results in, beyond `NS` (etc/proof_roots.py).
LINK_NS = {m: proof_roots.link_namespace(m) for m in LINKS}
# The qualifiers of the packages Goose translates (`v3`, `zap`, `proto`, …).
QUALIFIERS = {pkg.rsplit("/", 1)[-1].replace("-", "_").replace(".", "_")
              for p in goose.PROJECTS for _, _, pkgs, _ in goose.pieces(p) for pkg in pkgs}
# a package whose path has a segment like this is a test helper
TEST_PKG = re.compile(r"(^|/)[^/]*(test|mock)[^/]*(/|$)")

STATES = ["verified", "unfinished", "assumed", "translated", "not translated"]


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def git(cwd, *args):
    r = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else ""


# --- the Go code -------------------------------------------------------------


def fork(p):
    if p.local is not None:
        return p.local
    return p.repo.removeprefix("https://github.com/")


def go_sources(base):
    """DIR/<project> at the project's pinned revision, cloned or fetched if needed."""
    os.makedirs(base, exist_ok=True)
    dirs = {}
    for name, p in PROJECTS.items():
        if p.local is not None:
            dirs[name] = os.path.join(ROOT, p.local)
            continue
        d = os.path.join(base, name)
        if not os.path.isdir(d):
            print(f"verified-code: cloning {p.repo} into {d}", file=sys.stderr)
            if subprocess.run(["git", "init", "-q", d]).returncode != 0:
                sys.exit(f"verified-code: could not create {d}; pass --go-src")
        if git(d, "rev-parse", "HEAD") != p.rev:
            print(f"verified-code: checking out {fork(p)} at {p.rev[:9]}", file=sys.stderr)
            ok = (
                git(d, "cat-file", "-t", p.rev) == "commit"
                or subprocess.run(
                    ["git", "fetch", "-q", "--depth", "1", p.repo, p.rev], cwd=d
                ).returncode
                == 0
            )
            ok = ok and subprocess.run(
                ["git", "checkout", "-q", "--detach", p.rev], cwd=d
            ).returncode == 0
            if not ok:
                sys.exit(f"verified-code: could not check out {p.repo} at {p.rev}")
        dirs[name] = d
    return dirs


def go_module(d):
    m = re.search(r"^module\s+(\S+)", read(os.path.join(d, "go.mod")), re.M)
    return m.group(1).strip('"')


def project_part_packages():
    """project -> {Go package of one of its `parts` -> the part's module root}: packages
    translated into a module root of their own, from another source than the checkout
    (whose path may be that of a package of the sources)."""
    return {p.name: {q: part.root for part in p.parts for q in part.packages}
            for p in goose.PROJECTS}


def project_packages(src):
    """project -> its translated Go packages (import paths), the first its main one."""
    return {
        n: [go_module(src[n]) if q == "." else q for q in p.packages]
        for n, p in PROJECTS.items()
    }


def go_functions(dirs):
    r = subprocess.run(
        ["go", "run", "verified-code.go", *dirs],
        cwd=os.path.join(ROOT, "etc"),
        capture_output=True,
        text=True,
    )
    sys.stderr.write(r.stderr)
    if r.returncode != 0:
        sys.exit("verified-code: etc/verified-code.go failed")
    return [json.loads(line) for line in r.stdout.splitlines()]


# --- what is translated and what is proved -------------------------------------


def lean_ident(s):
    return s.replace("«", "").replace("»", "").rstrip("'")


def goose_functions(pkgs):
    """(package, receiver, name) of every function Goose translates (with a body), and
    of every top-level name it declares (`def X : GoString`: functions, also
    variables), from the translations (`Code/<package>.lean`)."""
    bodies, names = set(), set()
    for n in PROJECTS:
        for pkg in pkgs[n]:
            f = os.path.join(ROOT, "Code", pkg.replace(".", "_").replace("-", "_") + ".lean")
            if not os.path.exists(f):
                sys.exit(f"verified-code: no translation of {pkg} at {f}")
            text = read(f)
            for m in re.finditer(r"^(?:noncomputable )?def (\S+)\.impl ", text, re.M):
                parts = [lean_ident(x) for x in m.group(1).split(".")]
                recv, name = (parts[0], parts[1]) if len(parts) == 2 else ("", parts[0])
                bodies.add((pkg, recv, name))
            for m in re.finditer(
                r"^(?:noncomputable )?def (\S+) \[FfiSyntax\] \[GoGlobalContext\] : GoString",
                text,
                re.M,
            ):
                names.add((pkg, "", lean_ident(m.group(1))))
    return bodies, names


def local_proofs(objs):
    """This repository's specs: (project, the Lean name of the function (`T.M`)) ->
    (state, sorry-free), from the linked results of `LINKS`."""
    roots, axioms = {}, set()
    for o in objs:
        if o["t"] == "root" and o["module"] in LINKS:
            roots[o["name"]] = o
        elif o["t"] == "axiom":
            axioms.add(o["name"])
    out = {}
    for n, r in roots.items():
        # `T.wp_M : T.M.spec`
        name = n.removeprefix(NS)
        # A Link with a namespace of its own (`etc/gen-link.py --concurrency`) names its
        # package's functions in it (`concurrency.wp_NewSession`) and another package's
        # with that package's qualifier after it (`concurrency.v3.wp_OpPut`, clientv3's
        # `OpPut`): the namespace is dropped before a qualifier of another package.
        lns = LINK_NS[r["module"]]
        if lns and name.startswith(lns):
            rest = name.removeprefix(lns).split(".")
            if len(rest) > 1 and rest[0] in QUALIFIERS and rest[0] + "." != lns:
                name = ".".join(rest)
        *pre, last = name.split(".")
        fn = ".".join(pre + [last.removeprefix("wp_")])
        inherited = {s for u in r["uses"] if u in roots for s in roots[u]["sorries"]}
        own = set(r["sorries"]) - inherited
        if f"{NS}{fn}.wp_proof" in axioms:
            state = "assumed"
        elif own:
            state = "unfinished"
        else:
            state = "verified"
        out[(LINKS[r["module"]], fn)] = (state, not r["sorries"])
    return out


def qualifier(pkg):
    """How this repository's names qualify a Go package: its last segment, as Goose
    spells it (`go-humanize`: `go_humanize`)."""
    return pkg.rsplit("/", 1)[-1].replace("-", "_").replace(".", "_")


def resolve_local(fn, pkgs, part_pkgs, by_key, known):
    """The Go function a spec of this repository is about, and whether it is of a
    package of the project's `parts` (not the Go code of the sources, though its path
    may be), or None (Go's standard library: `slices.Sort`, `big.NewInt`, …).  `pkgs`
    are the project's packages, the first its main one; a name is qualified by the last
    segment of another (`pkg.T.M`, `pkg.F`; then it is of that package, translated or
    not), or else is of the main package, or of another one that has it."""
    parts = [lean_ident(x) for x in fn.split(".")]
    qual = {qualifier(q): q for q in pkgs[1:]}
    # a qualifier of both a part's package and another (`v3`: etcd's raft dependency and
    # clientv3) is the other's if that package has the function
    if len(parts) > 1 and parts[0] in {qualifier(q) for q in part_pkgs} and not (
            parts[0] in qual and len(parts) <= 3
            and ((qual[parts[0]], *parts[1:]) if len(parts) == 3
                 else (qual[parts[0]], "", parts[1])) in by_key.keys() | known):
        pkg = next(q for q in part_pkgs if qualifier(q) == parts[0])
        rest = parts[1:]
        return ((pkg, rest[0], rest[1]) if len(rest) == 2 else (pkg, "", rest[0])), True
    if parts[0] in qual and len(parts) > 1:
        pkg, rest = qual[parts[0]], parts[1:]
        if len(rest) <= 2:
            return ((pkg, rest[0], rest[1]) if len(rest) == 2 else (pkg, "", rest[0])), False
        return None
    for pkg in pkgs:
        key = (pkg, parts[0], parts[1]) if len(parts) == 2 else (pkg, "", parts[0])
        if key in by_key or key in known:
            return key, False
    # qualified by the main package's own qualifier (the register's `register.Register.Put`)
    if len(parts) in (2, 3) and parts[0] == qualifier(pkgs[0]):
        rest = parts[1:]
        key = (pkgs[0], rest[0], rest[1]) if len(rest) == 2 else (pkgs[0], "", rest[0])
        if key in by_key or key in known:
            return key, False
    return None


# --- the report --------------------------------------------------------------


def pct(a, b):
    return f"{100 * a / b:.1f}%" if b else "–"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("-o", "--out", action="append", default=[])
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--functions", action="store_true")
    ap.add_argument("--go-src", default=os.path.join(ROOT, ".lake", "go-src"))
    ap.add_argument("--json", default=os.path.join(ROOT, ".lake", "tcb.json"))
    ap.add_argument("--reuse", action="store_true")
    ap.add_argument("--package", action="append", default=[], metavar="PREFIX")
    args = ap.parse_args()

    src = go_sources(os.path.abspath(args.go_src))
    funcs = go_functions(list(src.values()))
    by_key = collections.defaultdict(list)  # (pkg, recv, name) -> Go functions
    for g in funcs:
        if g["name"] not in ("init", "_"):
            by_key[(g["pkg"], g["recv"], g["name"])].append(g)

    local = local_proofs(proof_roots.load(args.json, "verified-code", args.reuse))
    pkgs = project_packages(src)
    part_pkgs = project_part_packages()
    goose, named = goose_functions(pkgs)
    named -= goose
    # the translated packages whose Go code is in the sources (not a dependency's)
    in_src = {k[0] for k in by_key}

    state = {}  # key -> (state, sorry-free, where the spec is)
    for k in goose:
        state[k] = ("translated", False, "")
    outside = []
    dep_specs = collections.defaultdict(collections.Counter)  # package -> state -> specs
    for (proj, fn), (s, free) in sorted(local.items()):
        res = resolve_local(fn, pkgs[proj], part_pkgs[proj], by_key, goose | named)
        k, in_part = res if res else (None, False)
        if in_part:
            dep_specs[f"{k[0]} (translated into {part_pkgs[proj][k[0]]}/)"][s] += 1
            continue
        if k is not None and k[0] not in in_src:
            dep_specs[k[0]][s] += 1
            continue
        if k is None or k not in by_key:
            outside.append((fn, s))
            continue
        state[k] = (s, free, f"`{fn}.wp_proof`")
    missing = sorted(k for k in goose if k not in by_key and k[0] in in_src)
    deps = sorted({k[0] for k in goose | named if k[0] not in in_src} | set(dep_specs))

    def st(k):
        return state.get(k, ("not translated", False, ""))

    # classify every Go function
    src_proj = {d: n for n, d in src.items()}
    seen_mods = collections.defaultdict(set)  # project -> the modules of its checkout
    for g in funcs:
        seen_mods[src_proj[g["src"]]].add(g["module"])
    counted = {n: set(PROJECTS[n].counted_modules or seen_mods[n]) for n in src}
    order = {n: i for i, n in enumerate(PROJECTS)}
    rows = []  # (project, module, pkg, g, state, free)
    excluded = collections.Counter()  # reason -> code lines
    excluded_n = collections.Counter()
    excluded_tr = collections.Counter()  # reason -> translated functions
    for g in funcs:
        k = (g["pkg"], g["recv"], g["name"])
        s, free, _ = st(k) if g["name"] not in ("init", "_") else st(None)
        proj, mod, pkg = src_proj[g["src"]], g["module"], g["pkg"]
        reason = None
        if mod not in counted[proj]:
            reason = "modules not counted (tests, tools: `counted_modules` in etc/goose.py)"
        elif g["generated"]:
            reason = "generated code"
        elif TEST_PKG.search(pkg[len(mod):]):
            reason = "test-helper packages"
        if reason:
            excluded[reason] += g["sloc"]
            excluded_n[reason] += 1
            if s == "translated":
                excluded_tr[reason] += 1
            elif s != "not translated":
                outside.append((fname(g), f"{s}, {reason}"))
            continue
        g["translated"] = k in goose
        g["named"] = k in named
        rows.append((proj, mod, pkg, g, s, free))
    projects = sorted({r[0] for r in rows}, key=order.get)

    def tally(rs):
        n = collections.Counter()
        loc = collections.Counter()
        for *_, g, s, free in rs:
            n[s] += 1
            loc[s] += g["sloc"]
            if g["translated"]:
                n["tr"] += 1
                loc["tr"] += g["sloc"]
            if g["named"]:
                n["named"] += 1
            if s == "verified" and free:
                n["free"] += 1
                loc["free"] += g["sloc"]
        return n, loc

    out = []
    w = out.append
    head = git(ROOT, "rev-parse", "--short", "HEAD")
    man = json.loads(read(os.path.join(ROOT, "lake-manifest.json")))
    pin = next((p["rev"][:9] for p in man["packages"] if p["name"] == "perennial"), "?")
    revs = {n: git(d, "rev-parse", "--short", "HEAD") or "?" for n, d in src.items()}

    w("# Verified code\n")
    w(
        f"Generated by `etc/verified-code.py` at `{head}`; Perennial `{pin}`; Go sources "
        + ", ".join(
            f"{n}: `{fork(PROJECTS[n])}` at `{r}`"
            for n, r in revs.items()
        )
        + ". Do not edit by hand.\n"
    )
    w(
        "Every Go function and method is counted once, in its best state: **verified** "
        "(a proved spec whose proof has no `sorry` of its own; its callees' specs may be "
        "assumed), **unfinished** (a spec whose proof has a `sorry`), **assumed** (a spec "
        "that is an axiom), **translated** (Goose translates it, nothing specifies it), "
        "or not translated (\"names only\": Goose declares its name, not its body). "
        "Lines are Go code lines (not blank, not comments) from "
        "`func` to the closing brace. Specs are this repository's (elaborated: "
        "`.lake/tcb.json`).\n"
    )

    w("## Summary\n")
    w(
        "| code | functions | verified | sorry-free | unfinished | assumed | translated "
        "| code lines | verified lines | translated lines |"
    )
    w("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    scopes = [(x, [r for r in rows if r[0] == x]) for x in projects]
    for q in args.package:
        rs = [r for r in rows if r[2] == q or r[2].startswith(q.rstrip("/") + "/")]
        if not rs:
            sys.exit(f"verified-code: no Go package {q} or below it in the sources")
        scopes.append((f"`{q}`", rs))
    for scope, rs in scopes:
        n, loc = tally(rs)
        tot_n, tot_l = len(rs), sum(r[3]["sloc"] for r in rs)
        tr_l = loc["tr"]
        w(
            f"| {scope} | {tot_n} | {n['verified']} ({pct(n['verified'], tot_n)}) "
            f"| {n['free']} | {n['unfinished']} | {n['assumed']} | {n['translated']} "
            f"| {tot_l} | **{loc['verified']} ({pct(loc['verified'], tot_l)})** "
            f"| {tr_l} ({pct(tr_l, tot_l)}) |"
        )
    w(
        "\n\"sorry-free\": verified, and the linked result reaches no `sorry` through its "
        "callees (known only for this repository's proofs). \"translated lines\" counts "
        "the functions Goose translates, whatever their state (an assumed spec may be of "
        "a function it does not translate).\n"
    )

    def group_table(title, groups, total=None):
        w(
            f"| {title} | functions | verified | unfinished | assumed | translated "
            "| names only | code lines | verified lines |"
        )
        w("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
        for gname in sorted(groups, key=lambda x: -sum(r[3]["sloc"] for r in groups[x])):
            rs = groups[gname]
            n, loc = tally(rs)
            tot_l = sum(r[3]["sloc"] for r in rs)
            w(
                f"| `{gname}` | {len(rs)} | {n['verified']} | {n['unfinished']} "
                f"| {n['assumed']} | {n['translated']} | {n['named']} | {tot_l} "
                f"| {loc['verified']} ({pct(loc['verified'], tot_l)}) |"
            )
        if total:
            label, rs = total
            n, loc = tally(rs)
            w(f"| {label} | {len(rs)} | | | | | | {sum(r[3]['sloc'] for r in rs)} | |")
        w("")

    for proj in projects:
        prs = [r for r in rows if r[0] == proj]
        mods = collections.defaultdict(list)
        for r in prs:
            mods[r[1]].append(r)
        if len(mods) > 1:
            w(f"## {proj}, by module\n")
            group_table("module", mods)
        pkgs_of = collections.defaultdict(list)
        for r in prs:
            pkgs_of[r[2]].append(r)
        touched = {
            q: rs for q, rs in pkgs_of.items()
            if any(r[4] != "not translated" or r[3]["named"] for r in rs)
        }
        rest = [r for q, rs in pkgs_of.items() if q not in touched for r in rs]
        w(f"## {proj}, by package\n")
        w("The packages Goose translates any of (bodies or names only).\n")
        n_rest = len(pkgs_of) - len(touched)
        group_table("package", touched,
                    (f"{n_rest} other packages", rest) if rest else None)

    # the files of the packages Goose translates with bodies (all of them, translated
    # or not), and every other file with a function Goose translates with its body or
    # a spec of this repository's (of a package translated names-only but for some
    # functions), in the packages of --package
    def selected(pkg):
        return not args.package or any(
            pkg == q or pkg.startswith(q.rstrip("/") + "/") for q in args.package)

    bodied = {r[2] for r in rows if r[3]["translated"]} - {r[2] for r in rows if r[3]["named"]}
    shown_files = {
        r[3]["file"] for r in rows
        if selected(r[2]) and (r[2] in bodied or r[3]["translated"]
                               or r[4] in ("verified", "unfinished", "assumed"))
    }
    for scope in projects:
        w(f"## {scope}, by file\n")
        w("| file | functions | verified | translated | code lines | verified lines |")
        w("|---|---:|---:|---:|---:|---:|")
        files = collections.defaultdict(list)
        for r in rows:
            if r[0] == scope and r[3]["file"] in shown_files:
                files[r[3]["file"]].append(r)
        if not files:
            w("| (none) | | | | | |")
        for f in sorted(files, key=lambda x: -sum(r[3]["sloc"] for r in files[x])):
            rs = files[f]
            n, loc = tally(rs)
            tot_l = sum(r[3]["sloc"] for r in rs)
            w(
                f"| `{f}` | {len(rs)} | {n['verified']} | {n['translated']} | {tot_l} "
                f"| {loc['verified']} ({pct(loc['verified'], tot_l)}) |"
            )
        w("")

    w("## Specified but not verified\n")
    w("| function | state | code lines | proof |")
    w("|---|---|---:|---|")
    for r in sorted(rows, key=lambda r: (order[r[0]], r[2], r[3]["recv"], r[3]["name"])):
        if r[4] in ("unfinished", "assumed"):
            g = r[3]
            where = st((g["pkg"], g["recv"], g["name"]))[2]
            w(f"| `{fname(g)}` | {r[4]} | {g['sloc']} | {where} |")
    w("")

    w("## Excluded from the totals\n")
    w("| | functions | translated | code lines |")
    w("|---|---:|---:|---:|")
    for reason in sorted(excluded, key=lambda x: -excluded[x]):
        w(
            f"| {reason} | {excluded_n[reason]} | {excluded_tr[reason]} "
            f"| {excluded[reason]} |"
        )
    w("")
    if outside:
        w(
            "Specs of functions outside the totals (Go's standard library, generated "
            "code, …): "
            + ", ".join(f"`{f}` ({s})" for f, s in outside)
            + ".\n"
        )
    if missing:
        w(
            "Translated functions not found in the Go sources (the translation is of "
            "another commit): "
            + ", ".join(f"`{p}.{r + '.' if r else ''}{n}`" for p, r, n in missing)
            + ".\n"
        )
    if deps:
        def specs(p):
            c = dep_specs.get(p)
            return (" (specs: " + ", ".join(f"{c[x]} {x}" for x in STATES if c[x]) + ")"
                    if c else "")
        w(
            "Translated packages whose Go code is not in the sources counted here "
            "(dependencies), not counted: "
            + ", ".join(f"`{p}`{specs(p)}" for p in deps)
            + ".\n"
        )

    if args.functions:
        w("## Every function of the files above\n")
        w("| function | file | state | code lines |")
        w("|---|---|---|---:|")
        for r in sorted(rows, key=lambda r: (order[r[0]], r[2], r[3]["file"], r[3]["line"])):
            if r[3]["file"] in shown_files:
                g = r[3]
                s = r[4] + (" (sorry-free)" if r[4] == "verified" and r[5] else "")
                w(f"| `{fname(g)}` | `{g['file']}:{g['line']}` | {s} | {g['sloc']} |")
        w("")

    md = "\n".join(out)
    for path in args.out:
        with open(path, "w") as f:
            f.write(md if path.endswith(".md") else to_text(md))
        print(f"verified-code: wrote {path}", file=sys.stderr)
    if not args.out:
        print(md if args.markdown else to_text(md))
    return 0


def plain(s):
    """A Markdown line of this report without its inline markup."""
    return s.replace("**", "").replace("`", "")


def to_text(md, width=88):
    """The report in plain text: headings underlined, tables as aligned columns,
    paragraphs wrapped (the Markdown this script writes, not Markdown in general)."""
    out, lines, i = [], md.split("\n"), 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("|"):
            block = []
            while i < len(lines) and lines[i].startswith("|"):
                block.append([c.strip() for c in lines[i].strip().strip("|").split("|")])
                i += 1
            sep = block[1] if len(block) > 1 else []
            right = [c.endswith(":") for c in sep]
            rows = [[plain(c) for c in r] for k, r in enumerate(block) if k != 1]
            ncol = max(len(r) for r in rows)
            rows = [r + [""] * (ncol - len(r)) for r in rows]
            wid = [max(len(r[j]) for r in rows) for j in range(ncol)]
            rule = "  ".join("-" * x for x in wid)
            for k, r in enumerate(rows):
                cells = [
                    c.rjust(wid[j]) if j < len(right) and right[j] else c.ljust(wid[j])
                    for j, c in enumerate(r)
                ]
                out.append("  ".join(cells).rstrip())
                if k == 0:
                    out.append(rule)
            continue
        m = re.match(r"(#+) (.*)", line)
        if m:
            title = plain(m.group(2))
            out += [title, ("=" if len(m.group(1)) == 1 else "-") * len(title)]
        elif line.strip():
            out += textwrap.wrap(plain(line), width) or [""]
        else:
            out.append("")
        i += 1
    return "\n".join(out)


def fname(g):
    """`pkg.T.M`, without the package path's host (`example.com/`)."""
    p = g["pkg"]
    if "." in p.split("/", 1)[0] and "/" in p:
        p = p.split("/", 1)[1]
    return f"{p}.{g['recv'] + '.' if g['recv'] else ''}{g['name']}"


if __name__ == "__main__":
    sys.exit(main())
