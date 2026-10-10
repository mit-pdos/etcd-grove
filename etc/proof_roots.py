"""The root theorems of `etc/tcb-report.py` and `etc/verified-code.py`, and running
`etc/tcb-report.lean` on them (shared by the two; not a script).

The layout (CLAUDE.md): `Code/<pkg>` and `GeneratedProof/<pkg>` are Goose translations,
`Spec/<pkg>/<fn>.lean` and `Proof/<pkg>/<fn>.lean` a Go function's spec and proof, and
a package's `Proof/<pkg>/Link.lean` links every proof to its callees' (`T.wp_M :
T.M.spec`; `Results.lean` beside it restates exported results).  A project of
`etc/goose.py` may translate more packages into a module root of its own (a `Part`,
`<root>/Code/`, ..., `<root>/Proof/`), for a Go path that is also translated from another
source; the modules that reach one part root's translations cannot be imported with
those that reach another's, or the main root's same path.

The roots are the theorems of every `Link.lean` and `Results.lean` under `Proof/` and
`<root>/Proof/`, so a new package's proofs are picked up when its directory has them.
`etc/tcb-report.lean` imports the modules of one run into one environment; the runs
group the root modules by the part roots they reach (none, for most), read off the
import graph of this repository's files.

The JSON (`.lake/tcb.json` by default) starts with a `{"t":"meta", ...}` line naming the
modules it was computed from and the commit; `load` refuses one that is not of the
current modules (the result of an interrupted or failed run, or of an older layout).
"""

import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True  # no etc/__pycache__
sys.path.insert(0, os.path.join(ROOT, "etc"))
import goose  # noqa: E402  (etc/goose.py: the projects, their parts)

# The module roots of the projects' parts (`<root>/Code/`, ..., `<root>/Proof/`).
PART_ROOTS = sorted({part.root for p in goose.PROJECTS for part in p.parts})
# This repository's specs and proofs, as module prefixes and directories.
PROJECT_MODS = tuple(["Spec.", "Proof."] + [f"{r}.{d}." for r in PART_ROOTS
                                             for d in ("Spec", "Proof")])
PROJECT_DIRS = tuple(m.rstrip(".").replace(".", "/") for m in PROJECT_MODS)
ROOT_DIRS = ("Proof",) + tuple(os.path.join(r, "Proof") for r in PART_ROOTS)
LOCAL_DIRS = ("Code", "GeneratedProof", "Spec", "Proof") + tuple(PART_ROOTS)
ROOT_FILES = ("Link.lean", "Results.lean")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(.*)$", re.M)
NAMESPACE = re.compile(r"^namespace\s+(\S+)", re.M)


def module_of(path):
    """`Proof/<pkg>/Link.lean` -> `Proof.<pkg>.Link`."""
    return os.path.relpath(path, ROOT).removesuffix(".lean").replace(os.sep, ".")


def path_of(mod):
    return os.path.join(ROOT, *mod.split(".")) + ".lean"


def mod_path(m):
    return m.replace(".", "/") + ".lean"


def is_project(mod):
    """Whether module `mod` is one of this repository's specs or proofs."""
    return mod.startswith(PROJECT_MODS)


def root_modules():
    """Every `Link`/`Results` module, sorted."""
    mods = []
    for d in ROOT_DIRS:
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            mods += [module_of(os.path.join(dp, f)) for f in fs if f in ROOT_FILES]
    return sorted(mods)


def link_modules():
    return [m for m in root_modules() if m.endswith(".Link")]


def namespace():
    """The namespace this repository's declarations are in (`A.B.`: the longest common
    prefix of the namespaces the `Link.lean` files open before their first theorem),
    stripped from the names shown."""
    common = None
    for m in link_modules():
        with open(path_of(m), encoding="utf-8") as f:
            text = f.read()
        first = re.search(r"^theorem\b", text, re.M)
        ns = [c for n in NAMESPACE.findall(text[: first.start() if first else None])
              for c in n.split(".")]
        if common is None:
            common = ns
        else:
            k = 0
            while k < min(len(common), len(ns)) and common[k] == ns[k]:
                k += 1
            common = common[:k]
    return "".join(c + "." for c in common or [])


def link_namespace(mod):
    """The namespace a `Link.lean` opens before its first theorem beyond `namespace()`
    (`concurrency.`, `btree.`; usually empty): its results are named in it."""
    with open(path_of(mod), encoding="utf-8") as f:
        text = f.read()
    first = re.search(r"^theorem\b", text, re.M)
    ns = "".join(c + "." for n in NAMESPACE.findall(text[: first.start() if first else None])
                 for c in n.split("."))
    return ns.removeprefix(namespace())


def link_pending(mod):
    """The results of a `Link.lean` that rest on a function specified but not proved yet (its
    `section links_pending`, `etc/gen-link.py`'s `fn: ?`): their names, as declared (`T.wp_M`)."""
    with open(path_of(mod), encoding="utf-8") as f:
        text = f.read()
    m = re.search(r"^section links_pending\b(.*?)^end links_pending\b", text, re.M | re.S)
    return set(re.findall(r"^theorem ([\w.«»']+)", m.group(1), re.M)) if m else set()


def _imports(mod, memo={}):
    if mod not in memo:
        try:
            with open(path_of(mod), encoding="utf-8") as f:
                text = f.read()
        except OSError:
            text = ""
        memo[mod] = [
            m for line in IMPORT.findall(text) for m in line.split()
            if m.split(".")[0] in LOCAL_DIRS
        ]
    return memo[mod]


def parts_reached(mod):
    """The part roots whose modules `mod` imports, transitively."""
    seen, todo, reached = set(), [mod], set()
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        if m.split(".")[0] in PART_ROOTS:
            reached.add(m.split(".")[0])
        todo += _imports(m)
    return tuple(sorted(reached))


def lean_runs():
    """The root modules in the groups `etc/tcb-report.lean` imports together."""
    runs = {}
    for m in root_modules():
        runs.setdefault(parts_reached(m), []).append(m)
    return [runs[k] for k in sorted(runs)]


def lean_args():
    """`etc/tcb-report.lean`'s options: which modules are this repository's."""
    return [f"--part={r}" for r in PART_ROOTS]


def shown(path):
    """`path` relative to the working directory if it is below it, else absolute."""
    r = os.path.relpath(path)
    return os.path.abspath(path) if r.startswith("..") else r


def git_head():
    r = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else "?"


def run(json_path, prog):
    """Run `etc/tcb-report.lean` on every root module into `json_path` (replaced only
    when every run succeeds)."""
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    runs = lean_runs()
    tmp = json_path + ".tmp"
    with open(tmp, "w") as f:
        meta = {"t": "meta", "modules": sorted(m for r in runs for m in r), "head": git_head()}
        f.write(json.dumps(meta) + "\n")
        for mods in runs:
            f.flush()
            r = subprocess.run(
                ["lake", *os.environ.get("LAKE_OPTS", "").split(), "env", "lean", "--run",
                 "etc/tcb-report.lean", *lean_args(), *mods],
                cwd=ROOT, stdout=f, env=env, check=False,
            )
            if r.returncode != 0:
                f.close()
                os.remove(tmp)
                sys.exit(f"{prog}: etc/tcb-report.lean {' '.join(mods)} failed "
                         f"(exit {r.returncode}); is the project built?")
    os.replace(tmp, json_path)


def load(json_path, prog, reuse):
    """The objects of `json_path`, after (re)computing it unless `reuse` and it is of the
    current root modules."""
    if not (reuse and os.path.exists(json_path)):
        run(json_path, prog)
    with open(json_path, encoding="utf-8") as f:
        objs = [json.loads(line) for line in f if line.strip()]
    meta = objs[0] if objs and objs[0]["t"] == "meta" else None
    want = root_modules()
    if meta is None:
        sys.exit(f"{prog}: {shown(json_path)} is empty or of an older etc/tcb-report.py "
                 "(no meta line); rerun without --reuse")
    if meta["modules"] != want:
        missing = sorted(set(want) - set(meta["modules"]))
        extra = sorted(set(meta["modules"]) - set(want))
        sys.exit(f"{prog}: {shown(json_path)} is not of the current root modules"
                 + (f" (missing {', '.join(missing)})" if missing else "")
                 + (f" (no longer roots: {', '.join(extra)})" if extra else "")
                 + "; rerun without --reuse")
    if meta["head"] != git_head():
        print(f"{prog}: note: {shown(json_path)} was computed at {meta['head']}, "
              f"HEAD is {git_head()}", file=sys.stderr)
    return objs[1:]
