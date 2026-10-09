#!/usr/bin/env python3
"""Account for how much of etcd raft's and etcd's Go code is verified.

usage: etc/verified-code.py [-o REPORT.txt|REPORT.md]... [--markdown] [--functions]
                            [--go-src DIR] [--json TCB.json] [--reuse]

  -o           where to write the report (default: stdout), in Markdown if the file
               name ends in `.md` and in plain text otherwise; may be repeated
  --markdown   print Markdown instead of plain text on stdout
  --functions  also list every function, with its state, of the packages Goose
               translates with bodies (raft's, etcd's cache)
  --go-src     where the Go sources are: DIR/<project> for each project of
               `etc/goose.py` (etcd-raft, etcd), a checkout of the translated fork
               at the revision pinned there; default .lake/go-src, cloned or
               fetched there (shallow) and checked out at the pinned revision
  --json       the output of etc/tcb-report.lean, shared with etc/tcb-report.py
               (default .lake/tcb.json); --reuse skips re-running Lean

Needs a built project (`lake build`) and `go` (to parse the Go sources, with
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

The projects (the Go repositories, their pinned revisions and the packages
translated, into `Code/`) are `etc/goose.py`'s.  The specs are those of the linked
results of `Proof.go_etcd_io.raft.v3.Link` (raft) and `Proof.go_etcd_io.etcd.cache.v3.Link`
(etcd's `cache` package; the B-tree it uses is not etcd's code and not counted).

Code is measured in functions and in Go code lines: the lines from `func` to the
closing brace that hold code (not blank, not only comments).  Type, constant and
variable declarations are not counted.  Excluded from the totals, and listed: test
files, test-helper packages, generated files (protobuf), and the etcd modules that
are not etcd itself (tests, tools).
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
NS = "Perennial.EtcdGrove."

sys.dont_write_bytecode = True  # no etc/__pycache__
sys.path.insert(0, os.path.join(ROOT, "etc"))
import goose  # noqa: E402  (etc/goose.py: the projects, their pins and libraries)

PROJECTS = {p.name: p for p in goose.PROJECTS}
# The modules of linked results (each states `T.wp_M : T.M.spec`) -> the project
# whose functions they are about.
LINKS = {
    "Proof.go_etcd_io.raft.v3.Link": "etcd-raft",
    "Proof.go_etcd_io.etcd.cache.v3.Link": "etcd",
    "Proof.go_etcd_io.etcd.server.v3.etcdserver.Link": "etcd",
}
# etc/tcb-report.lean's runs, as in etc/tcb-report.py: its default modules, then the etcd
# server's links, which cannot share an environment with the Raft proof (both name
# `go_etcd_io.raft.v3`, of different raft versions).
LEAN_RUNS = ([], ["Proof.go_etcd_io.etcd.server.v3.etcdserver.Link"])
RAFT_MOD = "go.etcd.io/raft/v3"
# The modules of the etcd repository that make up etcd (not its tests or tools).
ETCD_MODS = [
    "go.etcd.io/etcd/api/v3",
    "go.etcd.io/etcd/cache/v3",
    "go.etcd.io/etcd/client/pkg/v3",
    "go.etcd.io/etcd/client/v3",
    "go.etcd.io/etcd/etcdctl/v3",
    "go.etcd.io/etcd/etcdutl/v3",
    "go.etcd.io/etcd/pkg/v3",
    "go.etcd.io/etcd/server/v3",
]
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
    return p.repo.removeprefix("https://github.com/")


def go_sources(base):
    """DIR/<project> at the project's pinned revision, cloned or fetched if needed."""
    os.makedirs(base, exist_ok=True)
    dirs = {}
    for name, p in PROJECTS.items():
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


def module_of(pkg, mods):
    return max((m for m in mods if pkg == m or pkg.startswith(m + "/")), key=len)


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


def run_lean(json_path):
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    with open(json_path, "w") as f:
        for mods in LEAN_RUNS:
            f.flush()
            r = subprocess.run(
                ["lake", "env", "lean", "--run", "etc/tcb-report.lean", *mods],
                cwd=ROOT,
                stdout=f,
                env=env,
            )
            if r.returncode != 0:
                sys.exit("verified-code: etc/tcb-report.lean failed; is the project built?")


def local_proofs(json_path):
    """This repository's specs: (project, the Lean name of the function
    (`raftLog.slice`)) -> (state, sorry-free), from the linked results of `LINKS`."""
    roots, axioms = {}, set()
    for line in read(json_path).splitlines():
        o = json.loads(line)
        if o["t"] == "root" and o["module"] in LINKS:
            roots[o["name"]] = o
        elif o["t"] == "axiom":
            axioms.add(o["name"])
    out = {}
    for n, r in roots.items():
        # `T.wp_M : T.M.spec`
        *pre, last = n.removeprefix(NS).split(".")
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
    if not any(p == "etcd" for p, _ in out):
        print(f"verified-code: no results of Proof.go_etcd_io.etcd.cache.v3.Link in {json_path}; "
              "rerun without --reuse", file=sys.stderr)
    return out


def resolve_local(fn, pkgs, by_key, known):
    """The Go function a spec of this repository is about, or None (Go's standard
    library: `slices.Sort`, `big.NewInt`, …).  `pkgs` are the project's packages, the
    first its main one; a name is qualified by the last segment of another
    (`tracker.Inflights.Add`, `btree.New`), or else is of the main package, or of
    another one that has it (`ResponseHeader.GetRevision`)."""
    parts = fn.split(".")
    qual = {q.rsplit("/", 1)[-1]: q for q in pkgs[1:]}
    if parts[0] in qual and len(parts) > 1:
        cands, parts = [qual[parts[0]]], parts[1:]
    else:
        cands = pkgs
    for pkg in cands:
        key = (pkg, parts[0], parts[1]) if len(parts) == 2 else (pkg, "", parts[0])
        if key in by_key or key in known:
            return key
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
    args = ap.parse_args()

    src = go_sources(os.path.abspath(args.go_src))
    funcs = go_functions(list(src.values()))
    by_key = collections.defaultdict(list)  # (pkg, recv, name) -> Go functions
    for g in funcs:
        if g["name"] not in ("init", "_"):
            by_key[(g["pkg"], g["recv"], g["name"])].append(g)

    if not (args.reuse and os.path.exists(args.json)):
        run_lean(args.json)
    local = local_proofs(args.json)
    pkgs = project_packages(src)
    goose, named = goose_functions(pkgs)
    named -= goose
    # the translated packages whose Go code is in the sources (not a dependency's)
    in_src = {k[0] for k in by_key}

    state = {}  # key -> (state, sorry-free, where the spec is)
    for k in goose:
        state[k] = ("translated", False, "")
    outside = []
    for (proj, fn), (s, free) in sorted(local.items()):
        k = resolve_local(fn, pkgs[proj], by_key, goose | named)
        if k is None or k not in by_key:
            outside.append((fn, s))
            continue
        state[k] = (s, free, f"`{fn}.wp_proof`")
    missing = sorted(k for k in goose if k not in by_key and k[0] in in_src)
    deps = sorted({k[0] for k in goose | named if k[0] not in in_src})

    def st(k):
        return state.get(k, ("not translated", False, ""))

    # classify every Go function
    rows = []  # (scope, module, pkg, g, state, free)
    excluded = collections.Counter()  # reason -> code lines
    excluded_n = collections.Counter()
    excluded_tr = collections.Counter()  # reason -> translated functions
    mods = [RAFT_MOD] + ETCD_MODS
    for g in funcs:
        k = (g["pkg"], g["recv"], g["name"])
        s, free, _ = st(k) if g["name"] not in ("init", "_") else st(None)
        pkg = g["pkg"]
        in_mods = [m for m in mods if pkg == m or pkg.startswith(m + "/")]
        reason = None
        if not in_mods:
            reason = "etcd modules outside etcd itself (tests, tools, the root module)"
        elif g["generated"]:
            reason = "generated code (protobuf)"
        elif TEST_PKG.search(pkg[len(max(in_mods, key=len)) :]):
            reason = "test-helper packages"
        if reason:
            excluded[reason] += g["sloc"]
            excluded_n[reason] += 1
            if s == "translated":
                excluded_tr[reason] += 1
            elif s != "not translated":
                outside.append((fname(g), f"{s}, {reason}"))
            continue
        m = max(in_mods, key=len)
        g["translated"] = k in goose
        g["named"] = k in named
        rows.append(("Raft" if m == RAFT_MOD else "etcd", m, pkg, g, s, free))

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
            f"`{fork(PROJECTS[n])}` at `{r}` (in `Code/`)"
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
    for scope in ["Raft", "etcd"]:
        rs = [r for r in rows if r[0] == scope]
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

    for scope, title, key in [
        ("Raft", "Raft, by package", lambda r: r[2]),
        ("etcd", "etcd, by module", lambda r: r[1]),
    ]:
        w(f"## {title}\n")
        w(
            "| | functions | verified | unfinished | assumed | translated | names only "
            "| code lines | verified lines |"
        )
        w("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
        groups = collections.defaultdict(list)
        for r in rows:
            if r[0] == scope:
                groups[key(r)].append(r)
        for gname in sorted(groups, key=lambda x: -sum(r[3]["sloc"] for r in groups[x])):
            rs = groups[gname]
            n, loc = tally(rs)
            tot_l = sum(r[3]["sloc"] for r in rs)
            w(
                f"| `{gname}` | {len(rs)} | {n['verified']} | {n['unfinished']} "
                f"| {n['assumed']} | {n['translated']} | {n['named']} | {tot_l} "
                f"| {loc['verified']} ({pct(loc['verified'], tot_l)}) |"
            )
        w("")
        if scope == "etcd":
            touched = collections.defaultdict(list)
            for r in rows:
                if r[0] == "etcd":
                    touched[r[2]].append(r)
            touched = {
                p: rs
                for p, rs in touched.items()
                if any(r[4] != "not translated" or r[3]["named"] for r in rs)
            }
            w("The etcd packages Goose translates any of (bodies or names only):\n")
            w(
                "| package | functions | verified | unfinished | assumed | translated "
                "| names only | code lines | verified lines |"
            )
            w("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
            for p in sorted(touched):
                rs = touched[p]
                n, loc = tally(rs)
                tot_l = sum(r[3]["sloc"] for r in rs)
                w(
                    f"| `{p}` | {len(rs)} | {n['verified']} | {n['unfinished']} "
                    f"| {n['assumed']} | {n['translated']} | {n['named']} | {tot_l} "
                    f"| {loc['verified']} ({pct(loc['verified'], tot_l)}) |"
                )
            w("")

    # the packages Goose translates with bodies: raft's, and etcd's but those it
    # translates as names only (but a function or two)
    bodied = {r[2] for r in rows if r[3]["translated"]} - {
        r[2] for r in rows if r[0] == "etcd" and r[3]["named"]
    }
    for scope, title in [
        ("Raft", "Raft, by file"),
        ("etcd", "etcd, by file (the packages Goose translates with bodies)"),
    ]:
        w(f"## {title}\n")
        w("| file | functions | verified | translated | code lines | verified lines |")
        w("|---|---:|---:|---:|---:|---:|")
        files = collections.defaultdict(list)
        for r in rows:
            if r[0] == scope and r[2] in bodied:
                files[r[3]["file"]].append(r)
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
    for r in sorted(rows, key=lambda r: (r[0] != "Raft", r[2], r[3]["recv"], r[3]["name"])):
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
            "another commit of the fork): "
            + ", ".join(f"`{p}.{r + '.' if r else ''}{n}`" for p, r, n in missing)
            + ".\n"
        )
    if deps:
        w(
            "Translated packages whose Go code is not in the sources counted here "
            "(dependencies of etcd), not counted: "
            + ", ".join(f"`{p}`" for p in deps)
            + ".\n"
        )

    if args.functions:
        w("## Every function of the packages Goose translates with bodies\n")
        w("| function | file | state | code lines |")
        w("|---|---|---|---:|")
        for r in sorted(rows, key=lambda r: (r[0] != "Raft", r[2], r[3]["file"], r[3]["line"])):
            if r[2] in bodied:
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
    p = g["pkg"].removeprefix("go.etcd.io/")
    return f"{p}.{g['recv'] + '.' if g['recv'] else ''}{g['name']}"


if __name__ == "__main__":
    sys.exit(main())
