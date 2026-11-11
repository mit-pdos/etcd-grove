#!/usr/bin/env python3
"""The model-as-parameter gate (per-type message models, stage A: the Scope's G, rules 1-7).

Runs `etc/ModelParamCheck.lean` (see its header for the rules) on the root modules of
`etc/tcb-report.py` (every `Link`/`MainLinked`/`Results` module, in the groups
`etc/proof_roots.py` imports together), with the modules declaring a registration added to the
main group, and its selftests (rule 6's negative tests) on the registration modules alone. Then:

- every `hit` not covered (rule 1), `atom` (rule 2), bad `reg` (rules 3, 4) or bad `sat` (rule 7)
  is a failure;
- every axiom a `Sat` theorem rests on (`satax`, already within Lean's allowlist by module and
  shape) must also appear verbatim on an `axiom` line of its `Code/` file (`[v6a]` 4; the `Code/`
  files are the translations `etc/goose.py --check` checks);
- every selftest must behave as declared (refused, or the one that must pass);
- a floor: at least `MIN_REGS` registrations, each with its `Sat` theorem.

    etc/model-param-check.py [--json FILE] [--reuse] [--no-cache] [--cache-dir DIR] [-v]

Never builds: the `.olean`s must be up to date. `$LAKE_OPTS` is passed to `lake`. Run it under a
memory cap (`systemd-run --scope -p MemoryMax=32G`).

**The cache.** The Lean runs (one per root group, and the selftests) took over an hour together
until `etc/ModelParamCheck.lean` stopped passing over every constant once per registration
(2026-11-11: about 4 minutes in all, the examples' group 2.5 of them);
each run's output is cached in a directory shared by the worktrees (`--cache-dir`, default
`$MODEL_PARAM_CACHE` or `/shared/tmp/model-param-cache`), under a SHA-256 key of everything the
run can depend on (`cache_key`):

- the run's command line after `lean --run`: the part options, `--selftest`, and its modules in
  order (so also the registration modules `reg_modules` found, the groups `proof_roots` formed);
- the content of every built module the run imports, transitively: the import closure read off
  Lake's `.trace` files (the imports each module was built with), and for each module the
  SHA-256 of its `.olean`, `.olean.server`, `.olean.private` and `.ilean` (missing ones
  recorded as missing), whichever package it is in (this repository, Perennial, Iris, ...);
  a module of a package with no `.trace`, other than the toolchain's own, refuses the cache;
- the toolchain: `lean-toolchain`, `lean --version`, the SHA-256 of the `lean` binary and of every
  `.olean` under its `lib/lean`;
- this script, `etc/ModelParamCheck.lean`, `etc/proof_roots.py`, `etc/goose.py`, `lakefile.toml`,
  `lake-manifest.json`, the manifest Lake reads (`--packages=` in `$LAKE_OPTS`), and the
  Perennial checkout's `HEAD`;
- the environment variables `MPC_*` (`MPC_ONLY` filters the walk) and `LEAN*` but `LEAN_PATH`.

File hashes are memoized per worktree (`.lake/model-param-hashes.json`) by path, size, inode,
mtime and ctime. An entry is written to a temporary file and renamed into place (concurrent runs
are safe: the last rename wins, with the same content), carries the SHA-256 of its body, and is
used only if that matches; a failed run is never cached. The judging below (rules, `satax`
against the `Code/` files, the selftests' reasons, `MIN_REGS`) takes seconds and always runs.

`etc/gates.sh` (and so `etc/land.sh`) uses the cache. `--no-cache` runs every Lean run afresh
(neither reads nor writes the cache): for a suspicious result, and for CI if it ever runs this
gate (a fresh runner has no cache to read).
"""
import argparse
import collections
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402

MIN_REGS = 36
REG = re.compile(r"(?:grpcReqModelOf|grpcRepModelOf|streamReqModelOf|streamRepModelOf|pbModelOf)\s+GF\s+\S+\s*=\s*some", re.S)


def reg_modules():
    mods = []
    for d in ("Proof", "Spec"):
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            for f in fs:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    s = open(p, encoding="utf-8").read()
                    if re.search(r"^axiom ", s, re.M) and REG.search(s):
                        mods.append(proof_roots.module_of(p))
    return sorted(mods)


CACHE_VERSION = "model-param-cache 1"
CORE_ROOTS = ("Init", "Lean", "Std", "Lake")
OLEAN_EXTS = (".olean", ".olean.server", ".olean.private", ".ilean")


class NoCache(Exception):
    pass


class Hasher:
    """SHA-256 of files, memoized by (path, size, inode, mtime, ctime) in `.lake/`."""

    def __init__(self):
        self.path = os.path.join(ROOT, ".lake", "model-param-hashes.json")
        try:
            with open(self.path) as f:
                self.memo = json.load(f)
        except (OSError, ValueError):
            self.memo = {}
        self.used = {}

    @staticmethod
    def _stat_key(st):
        return f"{st.st_size}:{st.st_ino}:{st.st_mtime_ns}:{st.st_ctime_ns}"

    @staticmethod
    def _sha(path):
        h = hashlib.sha256()
        with open(path, "rb") as f:
            while True:
                b = f.read(1 << 20)
                if not b:
                    break
                h.update(b)
        return h.hexdigest()

    def hash_many(self, paths):
        """{path: "<size>:<sha256>" or "missing"} for every path."""
        out, todo = {}, []
        for p in paths:
            p = os.path.realpath(p)
            try:
                st = os.stat(p)
            except FileNotFoundError:
                out[p] = "missing"
                continue
            k = self._stat_key(st)
            m = self.memo.get(p)
            if m and m[0] == k:
                out[p] = f"{st.st_size}:{m[1]}"
                self.used[p] = m
            else:
                todo.append((p, k, st.st_size))
        with concurrent.futures.ThreadPoolExecutor(16) as ex:
            for (p, k, size), h in zip(todo, ex.map(lambda t: self._sha(t[0]), todo)):
                # the file must not have changed while it was read
                if self._stat_key(os.stat(p)) != k:
                    raise NoCache(f"{p} changed while it was hashed")
                self.memo[p] = self.used[p] = [k, h]
                out[p] = f"{size}:{h}"
        return out

    def save(self):
        try:
            with tempfile.NamedTemporaryFile("w", dir=os.path.dirname(self.path), delete=False) as f:
                json.dump(self.used, f)
            os.replace(f.name, self.path)
        except OSError:
            pass


def _sha_text(data):
    return hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


class KeyContext:
    """What every run's key shares: the library directories, the toolchain, the scripts."""

    def __init__(self, env):
        self.hasher = Hasher()

        def out(*cmd):
            r = subprocess.run(proof_roots.lake("env", *cmd), cwd=ROOT, env=env,
                               capture_output=True, text=True, check=False)
            if r.returncode != 0:
                raise NoCache(f"`lake env {' '.join(cmd)}` failed: {r.stderr.strip()[:300]}")
            return r.stdout.strip()
        self.lean_path = [d for d in out("printenv", "LEAN_PATH").split(os.pathsep) if d]
        prefix = out("lean", "--print-prefix")
        self.core_lib = os.path.join(prefix, "lib", "lean")
        lean_bin = os.path.join(prefix, "bin", "lean")
        core = sorted(os.path.join(dp, f) for dp, _, fs in os.walk(self.core_lib) for f in fs
                      if f.endswith(OLEAN_EXTS))
        if not core:
            raise NoCache(f"no .olean under {self.core_lib}")
        files = [os.path.join(ROOT, "etc", f) for f in
                 ("model-param-check.py", "ModelParamCheck.lean", "proof_roots.py", "goose.py")]
        files += [os.path.join(ROOT, f) for f in ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]
        manifest = os.path.join(ROOT, "lake-manifest.json")
        opts = os.environ.get("LAKE_OPTS", "").split()
        for i, o in enumerate(opts):
            if o.startswith("--packages="):
                manifest = os.path.join(ROOT, o.split("=", 1)[1])
            elif o == "--packages" and i + 1 < len(opts):
                manifest = os.path.join(ROOT, opts[i + 1])
        files.append(manifest)
        hashes = self.hasher.hash_many([lean_bin] + files + core)
        perennial_head = subprocess.run(["git", "-C", proof_roots.PERENNIAL, "rev-parse", "HEAD"],
                                        capture_output=True, text=True).stdout.strip() or "?"
        self.common = {
            "version": CACHE_VERSION,
            "lean --version": out("lean", "--version"),
            "lean binary": hashes[os.path.realpath(lean_bin)],
            "core olean": _sha_text("\n".join(
                f"{os.path.relpath(p, self.core_lib)} {hashes[os.path.realpath(p)]}" for p in core)),
            "files": {os.path.relpath(f, ROOT) if f.startswith(ROOT) else f:
                      hashes[os.path.realpath(f)] for f in files},
            "perennial HEAD": perennial_head,
            # `MPC_ONLY` filters the walk; Lean's own variables (but the per-worktree LEAN_PATH,
            # whose modules are hashed) may change what it loads
            "env": {k: v for k, v in sorted(os.environ.items())
                    if k.startswith(("MPC_", "LEAN")) and k != "LEAN_PATH"},
        }
        self.trace_memo = {}

    def locate(self, mod):
        """The library directory holding `mod`'s build (its `.trace`), or None for the toolchain's."""
        rel = os.path.join(*mod.split("."))
        for d in self.lean_path:
            if os.path.exists(os.path.join(d, rel + ".trace")):
                return os.path.join(d, rel)
        if mod.split(".")[0] in CORE_ROOTS and os.path.exists(os.path.join(self.core_lib, rel + ".olean")):
            return None
        raise NoCache(f"no .trace for {mod} on LEAN_PATH")

    def imports(self, base):
        if base not in self.trace_memo:
            try:
                with open(base + ".trace") as f:
                    t = json.load(f)
            except (OSError, ValueError) as e:
                raise NoCache(f"cannot read {base}.trace: {e}")
            mods = set()

            def walk(x):
                if isinstance(x, list) and len(x) == 2 and isinstance(x[0], str):
                    if x[0] == "imports" and isinstance(x[1], list):
                        for lab, _ in x[1]:
                            mods.add(re.split(r"[ :]", lab, maxsplit=1)[0])
                    elif isinstance(x[1], list):
                        walk(x[1])
                elif isinstance(x, list):
                    for y in x:
                        walk(y)
            walk(t.get("inputs", []))
            self.trace_memo[base] = sorted(mods)
        return self.trace_memo[base]

    def key(self, argv, mods):
        """The run's cache key, and the number of modules in its import closure."""
        seen, todo, bases = set(), list(mods), {}
        while todo:
            m = todo.pop()
            if m in seen:
                continue
            seen.add(m)
            b = self.locate(m)
            if b is None:
                continue  # the toolchain's: in `core olean`
            bases[m] = b
            todo += self.imports(b)
        hashes = self.hasher.hash_many([b + e for b in bases.values() for e in OLEAN_EXTS])
        if any(hashes[os.path.realpath(b + ".olean")] == "missing" for b in bases.values()):
            raise NoCache("a module of the closure has no .olean")
        closure = "\n".join(
            m + " " + " ".join(hashes[os.path.realpath(bases[m] + e)] for e in OLEAN_EXTS)
            for m in sorted(bases))
        doc = dict(self.common, argv=argv, closure=_sha_text(closure))
        return _sha_text(json.dumps(doc, sort_keys=True)), len(bases)


def cache_get(cache_dir, key):
    try:
        with open(os.path.join(cache_dir, key + ".jsonl"), "rb") as f:
            head, _, body = f.read().partition(b"\n")
    except OSError:
        return None
    if head != b"#model-param " + _sha_text(body).encode():
        return None  # damaged: run again
    return body


def cache_put(cache_dir, key, body, meta):
    try:
        os.makedirs(cache_dir, exist_ok=True)
        with tempfile.NamedTemporaryFile("wb", dir=cache_dir, prefix=".tmp-", delete=False) as f:
            f.write(b"#model-param " + _sha_text(body).encode() + b"\n" + body)
        os.replace(f.name, os.path.join(cache_dir, key + ".jsonl"))
        with tempfile.NamedTemporaryFile("w", dir=cache_dir, prefix=".tmp-", delete=False) as f:
            json.dump(meta, f)
        os.replace(f.name, os.path.join(cache_dir, key + ".meta.json"))
    except OSError as e:
        print(f"model-param: could not write the cache ({e})", file=sys.stderr)


def run(json_path, cache_dir=None):
    """Run etc/ModelParamCheck.lean on every group (from the cache when `cache_dir` is given);
    returns (runs from the cache, runs)."""
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    regs = reg_modules()
    runs = proof_roots.lean_runs()
    # the registration modules join the group without part roots (the main tree)
    main = next((r for r in runs if not proof_roots.parts_reached(r[0])), None)
    if main is None:
        runs.append([])
        main = runs[-1]
    main.extend(m for m in regs if m not in main)
    jobs = [(mods, False) for mods in runs] + [(regs, True)]
    ctx = None
    if cache_dir is not None:
        try:
            ctx = KeyContext(env)
        except NoCache as e:
            print(f"model-param: not using the cache: {e}", file=sys.stderr)
    hits = 0
    with open(json_path + ".tmp", "wb") as f:
        for mods, st in jobs:
            argv = [*proof_roots.lean_args(), *(["--selftest"] if st else []), *mods]
            key = None
            if ctx is not None:
                try:
                    key, n = ctx.key(argv, mods)
                except NoCache as e:
                    print(f"model-param: not using the cache for a run of {len(mods)} modules: {e}",
                          file=sys.stderr)
            body = cache_get(cache_dir, key) if key else None
            if body is not None:
                hits += 1
                f.write(body)
                continue
            t0 = time.time()
            r = subprocess.run(proof_roots.lake("env", "lean", "--run", "etc/ModelParamCheck.lean", *argv),
                               cwd=ROOT, stdout=subprocess.PIPE, env=env, check=False)
            if r.returncode != 0:
                sys.exit(f"model-param: FAILED: etc/ModelParamCheck.lean exited {r.returncode} on "
                         f"{len(mods)} modules")
            f.write(r.stdout)
            if key:
                # the closure must still be what was keyed: nothing rebuilt during the run
                try:
                    same = ctx.key(argv, mods)[0] == key
                except NoCache:
                    same = False
                if same:
                    cache_put(cache_dir, key, r.stdout, {
                        "modules": len(mods), "closure": n, "selftest": st,
                        "head": proof_roots.git_head(), "root": ROOT,
                        "seconds": round(time.time() - t0), "date": time.strftime("%F %T")})
    if ctx is not None:
        ctx.hasher.save()
    os.replace(json_path + ".tmp", json_path)
    return hits, len(jobs)


import goose  # noqa: E402  (the projects' owned output paths)

OWNED = {((root or ""), o.replace(os.sep, "/")) for p in goose.PROJECTS
         for root, _, _, ow in goose.pieces(p) for o in ow}


def goose_owned(module):
    """Whether `module` (a `Code` module, or a part's) is under a path `etc/goose.py` owns, i.e.
    a translation `etc/goose.py --check` regenerates ([v6a] 4)."""
    parts = module.split(".")
    if parts[0] == "Code":
        root, rel = "", "/".join(parts[1:])
    elif len(parts) > 2 and parts[1] == "Code":
        root, rel = parts[0], "/".join(parts[2:])
    else:
        return False
    return any(r == root and (rel == o or rel.startswith(o + "/")) for r, o in OWNED)


def code_line_ok(module, name, cache={}):
    if not module.startswith("Perennial.") and not goose_owned(module):
        return False
    if module.startswith("Perennial."):
        path = os.path.join(proof_roots._perennial_dir(), *module.split(".")) + ".lean"
    else:
        path = proof_roots.path_of(module)
    if path not in cache:
        try:
            cache[path] = open(path, encoding="utf-8").read()
        except OSError:
            cache[path] = ""
    # the declaration is `axiom <short name>` inside the file's namespace
    short = name.split(".")
    for k in range(len(short)):
        # a component may be written `«…»` (a keyword or `_`)
        pat = r"\.".join(rf"(?:{re.escape(c)}|«{re.escape(c)}»)" for c in short[k:])
        if re.search(rf"^axiom {pat}[\s:\[]", cache[path], re.M):
            return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=os.path.join(ROOT, ".lake/model-param.jsonl"))
    ap.add_argument("--reuse", action="store_true")
    ap.add_argument("--no-cache", action="store_true",
                    help="run every Lean run afresh; neither read nor write the cache")
    ap.add_argument("--cache-dir", default=os.environ.get("MODEL_PARAM_CACHE",
                                                          "/shared/tmp/model-param-cache"))
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    cached = ""
    if not a.reuse:
        hits, n = run(a.json, None if a.no_cache else a.cache_dir)
        cached = "" if a.no_cache else f", {hits} of {n} Lean runs from the cache"
    objs = [json.loads(l) for l in open(a.json) if l.strip().startswith("{")]
    fails = set()
    regs, sats = {}, collections.defaultdict(set)
    axioms = set()
    selftests = []
    for o in objs:
        t = o["t"]
        if t == "axiom":
            axioms.add(o["name"])
        elif t == "hit" and not o["covered"]:
            fails.add(f"rule 1: {o['axiom']}: model binder {o['path']} ({o['type']}) has no registry premise")
        elif t == "atom":
            fails.add(f"rule 2: {o['axiom']}: a registry atom or registered record is received ({o['where']})")
        elif t == "reg":
            if "bad" in o:
                fails.add(f"registration {o['name']}: {o['bad']}")
            else:
                regs[o["name"]] = o
        elif t == "sat":
            if "bad" in o:
                fails.add(f"rule 7: {o['reg']}: {o['bad']}")
            elif "theorem" in o:
                sats[o["reg"]].add(o["theorem"])
        elif t == "satax":
            if o["axiom"] not in ("propext", "Classical.choice", "Quot.sound") and \
                    not code_line_ok(o["module"], o["axiom"]):
                fails.add(f"rule 7: {o['theorem']} rests on {o['axiom']}, not an axiom line of "
                          f"{o['module']}")
        elif t == "selftest":
            selftests.append(o)
    # each refusal must be for its intended reason (a substring of the refusing line)
    why = {"bare model": '"covered":false', "a stray positive": "not a constant",
           "a post yielding a registry atom": '"t":"atom"', "a post yielding a GrpcMethod": "binder m",
           "an axiom equating": "not a constant", "a theorem proved with sorry": '"t":"atom"',
           "a second registration": "a second registration", "a registration with an extra binder":
           "not a registry argument", "a registration with no Sat": "no theorem of type",
           "a Sat theorem resting on a hand-written zero_val": "Foo.zero_val",
           "a request registration keeping the default wireLen": "wireLen",
           "a vacuous Sat theorem": "no theorem of type", "a reversed wireLen witness": "wireLen",
           "an unbounded membership binder": '"t":"atom"',
           "a Sat theorem over an Empty binder": "no theorem of type",
           "a Sat theorem over a hand-written False Assumptions": "no theorem of type",
           "a wireLen witness of wireLen m - wireLen m": "wireLen"}
    for st in selftests:
        for k, w in why.items():
            if st["name"].startswith(k) and st.get("refused") and w not in st.get("by", ""):
                fails.add(f"selftest refused for another reason: {st['name']} ({st.get('by', '')[:200]})")
        if not st["ok"]:
            fails.add(f"selftest failed: {st['name']} ({st.get('why', st.get('by', ''))})")
    if len(selftests) == 0:
        fails.add("no selftest ran")
    if len(regs) != MIN_REGS:
        fails.add(f"count: {len(regs)} registrations, {MIN_REGS} expected (update MIN_REGS with a new instance)")
    for r in regs:
        if not sats.get(r):
            fails.add(f"rule 7: {r} has no Sat theorem")
    if a.v:
        for o in selftests:
            print(f"  selftest {'ok' if o['ok'] else 'FAILED'}: {o['name']}  [{o.get('by', '')[:160]}]")
    if fails:
        print(f"model-param: FAILED ({len(fails)})")
        for f in sorted(fails):
            print("  " + f)
        sys.exit(1)
    print(f"model-param: ok ({len(axioms)} trusted statements walked, {len(regs)} registrations "
          f"each with its Sat theorem, {len(selftests)} selftests{cached})")


if __name__ == "__main__":
    main()
