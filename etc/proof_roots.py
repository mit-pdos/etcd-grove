"""The root theorems of `etc/tcb-report.py` and `etc/verified-code.py`, and running
`etc/tcb-report.lean` on them (shared by the two; not a script).

The layout (CLAUDE.md): `Code/<pkg>` and `GeneratedProof/<pkg>` are Goose translations,
`Spec/<pkg>/<fn>.lean` and `Proof/<pkg>/<fn>.lean` a Go function's spec and proof, and
a package's `Proof/<pkg>/Link.lean` links every proof to its callees' (`T.wp_M :
T.M.spec`; `Results.lean` beside it restates exported results).  A project of
`etc/goose.py` may translate more packages into a module root of its own (a `Part`,
`<root>/Code/`, ..., `<root>/Proof/`), for a Go path that is also translated from another
source; the modules that reach one part root's translations cannot be imported with
those that reach another's, or the main root's same path.  A project translated into a
root of its own (`Project.root`: the witness experiment's `RaftWitness/`; raft v3.7's parallel tree `Raft37/` was one) is a part root
here too.

The roots are the theorems of every `Link.lean`, `MainLinked.lean` (an example's `Main` linked
by hand) and `Results.lean` under `Proof/` and
`<root>/Proof/`, so a new package's proofs are picked up when its directory has them.
`etc/tcb-report.lean` imports the modules of one run into one environment; the runs
group the root modules by the part roots they reach (none, for most), and by the local
translations they reach of a standard-library package Perennial also translates (`Code.os`,
project `bboltfs`: it declares the same names as `Perennial.Code.os`, which raft's
translation imports), read off the import graph of this repository's files.

The JSON (`.lake/tcb.json` by default) starts with a `{"t":"meta", ...}` line naming the
modules it was computed from and the commit; `load` refuses one that is not of the
current modules (the result of an interrupted or failed run, or of an older layout).
"""

import concurrent.futures
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True  # no etc/__pycache__
sys.path.insert(0, os.path.join(ROOT, "etc"))
import goose  # noqa: E402  (etc/goose.py: the projects, their parts)

# The module roots of the projects' parts and of the projects translated into a root of
# their own (`<root>/Code/`, ..., `<root>/Proof/`).
PART_ROOTS = sorted({root for p in goose.PROJECTS for root, _, _, _ in goose.pieces(p) if root})
# This repository's specs and proofs, as module prefixes and directories.
# (`SpecPlan/`, the spec plan, is not a project's root: specs only, no proofs, no roots, no
# axioms or `sorry`s; the scripts built on these lists ignore it. CLAUDE.md, Layout.)
PROJECT_MODS = tuple(["Spec.", "Proof."] + [f"{r}.{d}." for r in PART_ROOTS
                                             for d in ("Spec", "Proof")])
PROJECT_DIRS = tuple(m.rstrip(".").replace(".", "/") for m in PROJECT_MODS)
ROOT_DIRS = ("Proof",) + tuple(os.path.join(r, "Proof") for r in PART_ROOTS)
LOCAL_DIRS = ("Code", "TrustedCode", "GeneratedProof", "ManualProof", "Spec", "Proof") + tuple(
    PART_ROOTS)
# `MainLinked.lean`: an example's `Main` linked by hand over its callees' Links (no
# `etc/gen-link.py` mode links several packages); its results are linked results too
ROOT_FILES = ("Link.lean", "MainLinked.lean", "Results.lean", "TopLevelRobustness.lean")
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
    return [m for m in root_modules() if m.endswith((".Link", ".MainLinked"))]


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


def _perennial_dir():
    """Perennial's checkout as Lake resolves it: the `perennial` entry of the manifest Lake reads
    (`--packages=FILE` in `$LAKE_OPTS`, as `etc/tcb-report.py` passes it to Lake, else
    `lake-manifest.json`), its `dir` for a `path` dependency, else `<packagesDir>/perennial`."""
    manifest = os.path.join(ROOT, "lake-manifest.json")
    opts = shlex.split(os.environ.get("LAKE_OPTS", ""))
    for i, o in enumerate(opts):
        if o.startswith("--packages="):
            manifest = o.split("=", 1)[1]
        elif o == "--packages" and i + 1 < len(opts):
            manifest = opts[i + 1]
    manifest = os.path.join(ROOT, manifest)
    try:
        with open(manifest, encoding="utf-8") as f:
            man = json.load(f)
    except (OSError, ValueError):
        man = {}
    pkgs_dir = os.path.join(ROOT, man.get("packagesDir", os.path.join(".lake", "packages")))
    for p in man.get("packages", []):
        if p.get("name") == "perennial" and p.get("type") == "path" and p.get("dir"):
            return os.path.join(ROOT, p["dir"])
    return os.path.join(pkgs_dir, "perennial")


PERENNIAL = _perennial_dir()


def shadows_perennial(mod):
    """Whether `mod` is this repository's translation `Code.<pkg>` of a package Perennial
    translates too (`Perennial.Code.<pkg>`): the two declare the same names, so no environment
    can hold both."""
    return mod.startswith("Code.") and os.path.exists(
        os.path.join(PERENNIAL, "Perennial", *mod.split(".")) + ".lean")


# (net-swap, etcd-dist D2, 2026-11-22) the part `Net/`'s `net` is also the main tree's: its modules
# (the translation's and `Net/{Spec,Proof}/net/`'s, not `net/http`, `net/rpc`, `net/textproto` nor the
# part's `Init` over its own initializer copies) do not make a module one of the part's.
def shared_net(m):
    if m in ("Net.Code.net", "Net.TrustedCode.net", "Net.GeneratedProof.net", "Net.ManualProof.net"):
        return True
    for d in ("Net.Spec.net.", "Net.Proof.net."):
        if m.startswith(d):
            rest = m[len(d):]
            return not rest.startswith(("http", "rpc", "textproto")) and rest != "Init"
    return False


def parts_reached(mod):
    """The part roots whose modules `mod` imports, transitively, and the local translations it
    imports that shadow Perennial's (`shadows_perennial`)."""
    seen, todo, reached = set(), [mod], set()
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        if m.split(".")[0] in PART_ROOTS and not shared_net(m):
            reached.add(m.split(".")[0])
        if shadows_perennial(m):
            reached.add(m)
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


def lean_script(script, env=None):
    """The command that runs the Lean script `script` (`etc/<name>.lean`, a `main` importing
    only Lean's own modules) under `lake env`: a native build of it, else `lean --run script`.
    The same program either way (the compiler's IR, compiled to C instead of interpreted; the
    script's own interpreted loops were half of etc/tcb-report.lean's largest run: 392s
    interpreted, 208s native, the same JSON, 2026-11-17). The build is kept in
    `.lake/lean-scripts/`, named by a SHA-256 of the script's text and the toolchain
    (`lean --version`, `lean --print-prefix`), and made once (`lean -c`, then `leanc` against
    the toolchain's shared library: a few seconds); a failed build falls back to `lean --run`.
    `$LEAN_SCRIPTS_NATIVE=0` always runs `lean --run`."""
    if os.environ.get("LEAN_SCRIPTS_NATIVE", "1") == "0":
        return ["lean", "--run", script]
    env = env or dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep
                      + os.environ.get("PATH", ""))
    src = os.path.join(ROOT, script)

    def out(*cmd):
        r = subprocess.run(lake("env", *cmd), cwd=ROOT, env=env, capture_output=True, text=True,
                           check=False)
        return r.returncode, r.stdout.strip(), r.stderr.strip()
    try:
        rc1, ver, _ = out("lean", "--version")
        rc2, prefix, _ = out("lean", "--print-prefix")
        if rc1 or rc2:
            raise OSError("lean --version / --print-prefix failed")
        with open(src, "rb") as f:
            key = hashlib.sha256(f.read() + b"\0" + ver.encode() + b"\0" + prefix.encode()).hexdigest()
        d = os.path.join(ROOT, ".lake", "lean-scripts")
        exe = os.path.join(d, f"{os.path.splitext(os.path.basename(script))[0]}-{key[:16]}")
        if not os.path.exists(exe):
            os.makedirs(d, exist_ok=True)
            tmp = tempfile.mkdtemp(dir=d, prefix=".build-")
            try:
                c = os.path.join(tmp, "main.c")
                rc, _, err = out("lean", "-c", c, src)
                if rc:
                    raise OSError(f"lean -c: {err[-500:]}")
                lib = os.path.join(prefix, "lib", "lean")
                r = subprocess.run([os.path.join(prefix, "bin", "leanc"), "-O3", "-o",
                                    os.path.join(tmp, "exe"), c, f"-L{lib}", "-lleanshared",
                                    f"-Wl,-rpath,{lib}"], cwd=ROOT, env=env, capture_output=True,
                                   text=True, check=False)
                if r.returncode:
                    raise OSError(f"leanc: {r.stderr.strip()[-500:]}")
                os.replace(os.path.join(tmp, "exe"), exe)
            finally:
                shutil.rmtree(tmp, ignore_errors=True)
        return [exe]
    except OSError as e:
        print(f"{script}: no native build ({e}); running `lean --run`", file=sys.stderr)
        return ["lean", "--run", script]


def lake(*args):
    """The `lake` command line, with `$LAKE_OPTS`."""
    return ["lake", *os.environ.get("LAKE_OPTS", "").split(), *args]


def check_built(prog, env):
    """Exit unless the build of every root module is up to date.  Nothing here builds:
    `lake build --no-build` only checks, and `etc/tcb-report.lean` reads the `.olean`s
    as they are, so on a stale build it would report on the proofs as last built."""
    r = subprocess.run(lake("build", "--no-build", *root_modules()), cwd=ROOT, env=env,
                       capture_output=True, text=True, check=False)
    if r.returncode == 0:
        return
    out = r.stdout + r.stderr
    tail = out.split("Some required targets logged failures:\n")[-1]
    stale = re.findall(r"^- (\S+)$", tail, re.M)
    if r.returncode == 3 and stale:
        more = f", and {len(stale) - 5} more" if len(stale) > 5 else ""
        sys.exit(f"{prog}: the build is not up to date ({', '.join(stale[:5])}{more} "
                 "and what imports them); run `lake build` (or `etc/timed-build.py`), "
                 "then rerun")
    sys.exit(f"{prog}: `{' '.join(lake('build', '--no-build'))} <root modules>` failed "
             f"(exit {r.returncode}):\n" + "\n".join(out.splitlines()[-20:]))


def run_groups(fn, groups, size=len):
    """`[fn(g) for g in groups]`, computed in parallel lanes: the groups' Lean runs are
    independent (each imports its own modules and reads only the `.olean`s), so the result is
    the same as one after another. `$TCB_JOBS` lanes (default 2), the largest group first: the
    examples' group (107 roots, 18.5 GiB, 8 of a run's 11 minutes, 2026-11-17) in one lane, the
    others one after another in the other (none above 7 GiB), so the peak memory is about the
    largest two groups' and the wall time the largest group's."""
    jobs = max(1, int(os.environ.get("TCB_JOBS") or 2))
    order = sorted(range(len(groups)), key=lambda i: -size(groups[i]))
    out = [None] * len(groups)
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futs = {ex.submit(fn, groups[i]): i for i in order}
        for f in concurrent.futures.as_completed(futs):
            out[futs[f]] = f.result()
    return out


TCB_CACHE_VERSION = "tcb-report-cache 2"
TCB_CACHE_SCRIPTS = ("tcb-report.lean", "proof_roots.py", "goose.py", "lean_cache.py")
TCB_CACHE_MAX_BYTES = 40 << 30  # the largest group's entry is 560 MB


def run(json_path, prog):
    """Run `etc/tcb-report.lean` on every root module into `json_path` (replaced only
    when every run succeeds), if their build is up to date.  The groups' runs are
    independent: they run in parallel (`run_groups`), each into its own file, concatenated
    in the groups' order, so the JSON is the same as run one after another."""
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    check_built(prog, env)
    runs = lean_runs()
    tmp = json_path + ".tmp"
    outs = [f"{tmp}.{i}" for i in range(len(runs))]
    script = lean_script("etc/tcb-report.lean", env)

    # a group's output from the cache (etc/lean_cache.py: keyed by everything the run can read,
    # its whole import closure's `.olean`s with their proofs, `.olean.private`, among it), when
    # the cache is on (`$TCB_CACHE` a directory; `etc/gates.sh` sets it, nothing else does)
    cache_dir = os.environ.get("TCB_CACHE") or None
    ctx, keys, hits = None, [None] * len(runs), 0
    if cache_dir:
        import lean_cache
        try:
            ctx = lean_cache.KeyContext(env, TCB_CACHE_VERSION, TCB_CACHE_SCRIPTS, ("TCB_",),
                                        os.path.join(ROOT, ".lake", "tcb-report-hashes.json"))
            for i, mods in enumerate(runs):
                keys[i] = ctx.key([*lean_args(), *mods], mods)[0]
        except lean_cache.NoCache as e:
            print(f"{prog}: not using the cache: {e}", file=sys.stderr)
            ctx = None

    def one(i):
        if ctx is not None:
            body = lean_cache.cache_get(cache_dir, keys[i], "tcb-report")
            if body is not None:
                with open(outs[i], "wb") as f:
                    f.write(body)
                return "hit"
        t0 = time.monotonic()
        with open(outs[i], "w") as f:
            rc = subprocess.run(
                lake("env", *script, *lean_args(), *runs[i]),
                cwd=ROOT, stdout=f, env=env, check=False,
            ).returncode
        print(f"{prog}: Lean run of {len(runs[i])} root modules ({runs[i][0]}, ...): "
              f"{time.monotonic() - t0:.0f}s", file=sys.stderr)
        if rc == 0 and ctx is not None:
            try:
                same = ctx.key([*lean_args(), *runs[i]], runs[i])[0] == keys[i]
            except lean_cache.NoCache:
                same = False
            if same:  # nothing rebuilt during the run
                with open(outs[i], "rb") as f:
                    lean_cache.cache_put(cache_dir, keys[i], f.read(), {
                        "modules": len(runs[i]), "head": git_head(), "root": ROOT}, "tcb-report")
        return rc

    try:
        codes = run_groups(one, list(range(len(runs))), size=lambda i: len(runs[i]))
        hits = codes.count("hit")
        codes = [0 if c == "hit" else c for c in codes]
        if ctx is not None:
            ctx.hasher.save()
            lean_cache.prune(cache_dir, TCB_CACHE_MAX_BYTES)
            print(f"{prog}: {hits} of {len(runs)} Lean runs from the cache", file=sys.stderr)
        for mods, rc in zip(runs, codes):
            if rc != 0:
                sys.exit(f"{prog}: etc/tcb-report.lean {' '.join(mods)} failed (exit {rc})")
        with open(tmp, "w") as f:
            meta = {"t": "meta", "modules": sorted(m for r in runs for m in r), "head": git_head()}
            f.write(json.dumps(meta) + "\n")
            for o in outs:
                with open(o) as g:
                    while True:
                        b = g.read(1 << 24)
                        if not b:
                            break
                        f.write(b)
        os.replace(tmp, json_path)
    finally:
        for o in outs + [tmp]:
            if os.path.exists(o):
                os.remove(o)


def _names(objs):
    """`objs` with each root's `axioms` and `defs` by name: `etc/tcb-report.lean` writes them as
    the indices (`i`) of its run's axiom and def lines (each run starting with a `group` line)."""
    out, group = [], []

    def flush():
        ax = {o["i"]: o["name"] for o in group if o["t"] == "axiom"}
        df = {o["i"]: o["name"] for o in group if o["t"] == "def"}
        for o in group:
            if o["t"] == "root":
                o["axioms"] = [ax[i] if isinstance(i, int) else i for i in o["axioms"]]
                o["defs"] = [df[i] if isinstance(i, int) else i for i in o["defs"]]
            if o["t"] in ("axiom", "def"):
                o.pop("i", None)
            out.append(o)
        group.clear()
    for o in objs:
        if o["t"] == "group":
            flush()
        elif o["t"] == "meta":
            out.append(o)
        else:
            group.append(o)
    flush()
    return out


def load(json_path, prog, reuse):
    """The objects of `json_path`, after (re)computing it unless `reuse` and it is of the
    current root modules."""
    if not (reuse and os.path.exists(json_path)):
        run(json_path, prog)
    with open(json_path, encoding="utf-8") as f:
        objs = [json.loads(line) for line in f if line.strip()]
    meta = objs[0] if objs and objs[0]["t"] == "meta" else None
    objs = _names(objs)
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
