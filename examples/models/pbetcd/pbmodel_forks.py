#!/usr/bin/env python3
"""pbgen's pbmodel mode on etcd's and raft's own message packages, in a scratch copy of the forks.

    examples/models/pbetcd/pbmodel_forks.py [--keep] [--scale X] [--no-race]

The same-package methods (models/protobuf/pbgen.py --pbmodel; models/protobuf/pbgen_core.py's doc,
"THE SAME-PACKAGE METHODS") are written into each message type's own package. This script never
writes into the forks: it copies the modules the examples' go.mod pins (etcd's api/v3 and
server/v3 at the fork's edc800c, raft at d2c16c5: etc/goose.py's pins, which `etc/goose.py --check`
keeps equal to examples/go.mod's) out of the module cache into a temporary directory, makes a
module whose go.mod is the examples' with `replace`s of the three by the copies (and the examples'
relative replaces made absolute), and there:

  1. checks that no Go file of the copies names a generated method (PbModelSize, ...) or the
     generated file's import names: the methods are the only code that may (#37, D1's condition 1);
  2. runs pbgen --pbmodel on this directory's protobuf.toml (the roots of the codec mode, plus the
     types etcd keeps in bbolt or the WAL that zeldovich's review named), which writes
     pbmodel_gen.go and pbmodel_gen_test.go into every package of the closure;
  3. runs `go test -tags pbmodel` on those packages (each package's generated tests against
     protobuf-go v1.36.12: Marshal, Unmarshal with mutations and unknown fields, Size, Clone, the
     size cache's interleavings), and their concurrent test again under -race.

Prints the per-package counts; exits 1 on any failure. `--keep` leaves the scratch directory.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
EXAMPLES = os.path.normpath(os.path.join(HERE, "..", ".."))
ROOT = os.path.normpath(os.path.join(EXAMPLES, ".."))
PBGEN = os.path.join(ROOT, "models", "protobuf", "pbgen.py")
MODULES = ["go.etcd.io/etcd/api/v3", "go.etcd.io/etcd/server/v3", "go.etcd.io/raft/v3"]
# the generated methods' names and the generated file's import names (etc/gates.sh checks the
# repository's Go code for the same)
PREFIX = re.compile(r"\bPbModel(Size|Append|Unmarshal|Decode|DecodeField|IsInit|MergeFrom|Clone|IsNil)\b|"
                    r"\bpbmodel(codec|atomic)\b")


def go(args, cwd, env, check=True):
    r = subprocess.run(["go"] + args, cwd=cwd, env=env, capture_output=True, text=True)
    if check and r.returncode != 0:
        sys.exit(f"go {' '.join(args)} (in {cwd}) failed:\n{r.stdout}{r.stderr}")
    return r


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--keep", action="store_true", help="keep the scratch directory")
    ap.add_argument("--scale", default="0.3", help="PBGEN_TEST_SCALE for the generated tests")
    ap.add_argument("--no-race", action="store_true", help="skip the -race run")
    a = ap.parse_args()
    env = dict(os.environ, GOWORK="off", GOFLAGS="-mod=mod")
    env.setdefault("GOPROXY", "off")
    tmp = tempfile.mkdtemp(prefix="pbmodel-forks-")
    ok = False
    try:
        # the pinned modules' directories (the module cache), copied, writable
        mods = {}
        for m in MODULES:
            j = json.loads(go(["list", "-m", "-json", m], EXAMPLES, env).stdout)
            d = (j.get("Replace") or j)["Dir"]
            dst = os.path.join(tmp, "src", m.replace("/", "_"))
            shutil.copytree(d, dst)
            for dp, dns, fns in os.walk(dst):
                os.chmod(dp, 0o755)
                for f in fns:
                    os.chmod(os.path.join(dp, f), 0o644)
            mods[m] = dst
        # 1. nothing but the generated methods names the prefix
        bad = []
        for m, d in mods.items():
            for dp, _, fns in os.walk(d):
                for f in fns:
                    if f.endswith(".go"):
                        p = os.path.join(dp, f)
                        for i, line in enumerate(open(p, encoding="utf-8", errors="replace"), 1):
                            if PREFIX.search(line):
                                bad.append(f"{os.path.relpath(p, d)}:{i}: {line.strip()}")
        if bad:
            sys.exit("pbmodel_forks: the forks name the generated methods' prefix:\n" + "\n".join(bad))
        # the scratch module: the examples' go.mod and go.sum, relative replaces made absolute, the
        # three modules replaced by the copies
        mod = os.path.join(tmp, "mod")
        os.makedirs(mod)
        shutil.copy(os.path.join(EXAMPLES, "go.mod"), mod)
        shutil.copy(os.path.join(EXAMPLES, "go.sum"), mod)
        j = json.loads(go(["mod", "edit", "-json"], mod, env).stdout)
        edits = []
        for r in j.get("Replace") or []:
            new = r["New"]
            if not new.get("Version") and new["Path"].startswith("."):
                old = r["Old"]["Path"] + ("@" + r["Old"]["Version"] if r["Old"].get("Version") else "")
                edits.append(f"-replace={old}={os.path.normpath(os.path.join(EXAMPLES, new['Path']))}")
        edits += [f"-replace={m}={d}" for m, d in mods.items()]
        go(["mod", "edit"] + edits, mod, env)
        # 2. the methods and their tests, written into the copies
        toml = os.path.join(HERE, "protobuf.toml")
        r = subprocess.run([sys.executable, PBGEN, toml, mod, "--pbmodel"], cwd=mod, env=env,
                           capture_output=True, text=True)
        print(r.stdout, end="")
        if r.returncode != 0:
            sys.exit(f"pbgen --pbmodel failed (exit {r.returncode}):\n{r.stderr}")
        pkgs = []
        for line in r.stdout.splitlines():
            if line.startswith("wrote ") and line.endswith("pbmodel_gen.go"):
                d = os.path.dirname(line[len("wrote "):])
                for m, md in mods.items():
                    if d.startswith(md + os.sep) or d == md:
                        pkgs.append(m + d[len(md):].replace(os.sep, "/"))
        # 3. the generated tests, and the concurrent one under -race
        tenv = dict(env, PBGEN_TEST_SCALE=a.scale)
        r = go(["test", "-count=1", "-v", "-tags", "pbmodel", "-timeout", "60m"] + pkgs, mod, tenv, check=False)
        for line in r.stdout.splitlines():
            if re.search(r"^(ok|FAIL|---)|encodings,|decoded,|comparisons|operations compared", line):
                print(line)
        if r.returncode != 0:
            print(r.stdout[-6000:] + r.stderr[-3000:])
            sys.exit("pbmodel_forks: the generated methods differ from protobuf-go")
        if not a.no_race:
            r = go(["test", "-count=1", "-race", "-tags", "pbmodel", "-run", "TestPbModelConcurrent|TestPbModelCache",
                    "-timeout", "60m"] + pkgs, mod, tenv, check=False)
            print(r.stdout, end="")
            if r.returncode != 0:
                print(r.stderr[-3000:])
                sys.exit("pbmodel_forks: the -race run failed")
        print(f"pbmodel_forks: ok ({len(pkgs)} packages: {', '.join(pkgs)})")
        ok = True
    finally:
        if a.keep:
            print(f"(kept {tmp})")
        else:
            shutil.rmtree(tmp, ignore_errors=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
