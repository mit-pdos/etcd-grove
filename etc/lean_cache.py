"""A cache of Lean runs' outputs, keyed by everything a run can depend on (shared by
`etc/model-param-check.py` and `etc/tcb-report.py`'s `etc/proof_roots.py`).

A run's key (`KeyContext.key`) is a SHA-256 of: its command line after the script (options and
modules, in order); the content of every built module it imports, transitively (the import
closure read off Lake's `.trace` files; for each module the SHA-256 of its `.olean`,
`.olean.server`, `.olean.private` and `.ilean`, missing ones recorded as missing, whichever
package it is in; a module of a package with no `.trace`, other than the toolchain's, refuses the
cache); the toolchain (`lean --version`, the `lean` binary, every `.olean` of its `lib/lean`); the
check's scripts, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, the manifest Lake reads
(`--packages=` in `$LAKE_OPTS`) and the Perennial checkout's `HEAD`; the environment variables of
the check's prefixes and `LEAN*` but `LEAN_PATH`. File hashes are memoized per worktree by path,
size, inode, mtime and ctime. An entry is written to a temporary file and renamed into place,
carries the SHA-256 of its body (checked on read), and a failed run is never cached.
"""
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402

CORE_ROOTS = ("Init", "Lean", "Std", "Lake")
OLEAN_EXTS = (".olean", ".olean.server", ".olean.private", ".ilean")


class NoCache(Exception):
    pass


class Hasher:
    """SHA-256 of files, memoized by (path, size, inode, mtime, ctime) in `.lake/`."""

    def __init__(self, path):
        self.path = path
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

    def __init__(self, env, version, scripts, env_prefixes, hashes_path):
        self.hasher = Hasher(hashes_path)

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
        files = [os.path.join(ROOT, "etc", f) for f in scripts]
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
            "version": version,
            "lean --version": out("lean", "--version"),
            "lean binary": hashes[os.path.realpath(lean_bin)],
            "core olean": _sha_text("\n".join(
                f"{os.path.relpath(p, self.core_lib)} {hashes[os.path.realpath(p)]}" for p in core)),
            "files": {os.path.relpath(f, ROOT) if f.startswith(ROOT) else f:
                      hashes[os.path.realpath(f)] for f in files},
            "perennial HEAD": perennial_head,
            # the check's own variables (`MPC_ONLY` filters model-param's walk); Lean's own (but
            # the per-worktree LEAN_PATH, whose modules are hashed) may change what it loads
            "env": {k: v for k, v in sorted(os.environ.items())
                    if k.startswith((*env_prefixes, "LEAN")) and k != "LEAN_PATH"},
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


def cache_get(cache_dir, key, tag):
    try:
        with open(os.path.join(cache_dir, key + ".jsonl"), "rb") as f:
            head, _, body = f.read().partition(b"\n")
    except OSError:
        return None
    if head != b"#" + tag.encode() + b" " + _sha_text(body).encode():
        return None  # damaged: run again
    try:
        os.utime(os.path.join(cache_dir, key + ".jsonl"))  # recently used (`prune`)
    except OSError:
        pass
    return body


def cache_put(cache_dir, key, body, meta, tag):
    try:
        os.makedirs(cache_dir, exist_ok=True)
        with tempfile.NamedTemporaryFile("wb", dir=cache_dir, prefix=".tmp-", delete=False) as f:
            f.write(b"#" + tag.encode() + b" " + _sha_text(body).encode() + b"\n" + body)
        os.replace(f.name, os.path.join(cache_dir, key + ".jsonl"))
        with tempfile.NamedTemporaryFile("w", dir=cache_dir, prefix=".tmp-", delete=False) as f:
            json.dump(meta, f)
        os.replace(f.name, os.path.join(cache_dir, key + ".meta.json"))
    except OSError as e:
        print(f"{tag}: could not write the cache ({e})", file=sys.stderr)




def prune(cache_dir, max_bytes):
    """Remove the least recently used entries until the cache holds at most `max_bytes` (an entry
    read from the cache is touched)."""
    try:
        ents = []
        for f in os.listdir(cache_dir):
            if f.endswith(".jsonl"):
                p = os.path.join(cache_dir, f)
                st = os.stat(p)
                ents.append((st.st_mtime, st.st_size, p))
        total = sum(e[1] for e in ents)
        for _, size, p in sorted(ents):
            if total <= max_bytes:
                break
            for q in (p, p[:-len(".jsonl")] + ".meta.json"):
                try:
                    os.remove(q)
                except OSError:
                    pass
            total -= size
    except OSError:
        pass
