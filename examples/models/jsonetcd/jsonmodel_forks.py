#!/usr/bin/env python3
"""jsongen's same-package mode on etcd's, raft's and k8s's own packages, in a scratch copy of the modules.

    examples/models/jsonetcd/jsonmodel_forks.py [--keep] [--scale N] [ROOT...]

The same-package methods (models/json/jsongen.py; models/json/jsongen_core.py's doc, "THE
SAME-PACKAGE METHODS": JSONModelMarshal, JSONModelMarshalPtr, JSONModelUnmarshal, which the
encoding/json model calls by a value's method set) are written into each root type's own package
(mit-pdos/etcd-grove#24, J3). This script never writes into the forks: it copies the modules of the
roots that the examples' go.mod pins (etc/goose.py's pins, which `etc/goose.py --check` keeps equal
to examples/go.mod's) out of the module cache into a temporary directory, makes a module whose go.mod
is the examples' with `replace`s of those by the copies (and the examples' relative replaces made
absolute), and there:

  1. checks that no Go file of the copied modules, of models/ or of examples/ names a generated
     method (JSONModel...) outside a generated json_model_gen*.go and the encoding/json model's
     dispatch (models/encoding/json): the methods are the only code that may (the names are reserved; etc/gates.sh checks the repository's own Go code too);
  2. generates, per package of the roots, json_model_gen.go and json_model_gen_test.go (the
     methods' regression test: Marshal of random values, pointers and nil pointers, Unmarshal of
     the real encodings, their mutations and literals, the methods' results against the real
     encoding/json, called through the dispatch the model does), handed to go by -overlay (as
     etc/goose.py hands json_model_gen.go to goose);
  3. runs `go test -tags netmodel -overlay` on those packages, the generated tests only.

The roots are etc/goose.py's Project.jsonmodel_roots of every project (or the ROOTs given,
"import/path.Type"). Prints the per-package counts; exits 1 on any failure. `--keep` leaves the
scratch directory.
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
sys.path.insert(0, os.path.join(ROOT, "models", "json"))
sys.path.insert(0, os.path.join(ROOT, "etc"))
import jsongen  # noqa: E402

# a generated method's name, anywhere but in a generated file of the same-package mode
PREFIX = re.compile(r"\bJSONModel\w*")
GENERATED = re.compile(r"^json_model_gen(_test)?\.go$")
# the encoding/json model itself, which declares and calls them (its dispatch)
MODEL = os.path.join(ROOT, "models", "encoding", "json")


def go(args, cwd, env, check=True):
    r = subprocess.run(["go"] + args, cwd=cwd, env=env, capture_output=True, text=True)
    if check and r.returncode != 0:
        sys.exit(f"go {' '.join(args)} (in {cwd}) failed:\n{r.stdout}{r.stderr}")
    return r


def goose_roots(base):
    """The Project.jsonmodel_roots of etc/goose.py's projects built in the module at `base`
    (examples/'s module: every project whose source is the examples' pins; else the project whose
    `local` is `base`)."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("goose", os.path.join(ROOT, "etc", "goose.py"))
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    rel = os.path.relpath(base, ROOT)
    return [r for p in g.PROJECTS for r in (getattr(p, "jsonmodel_roots", None) or [])
            if (p.local == rel) or (base == EXAMPLES and not p.local)]


def scan(d, bad, rel):
    for dp, dns, fns in os.walk(d):
        dns[:] = [x for x in dns if not x.startswith(".")]
        if os.path.normpath(dp) == MODEL:
            continue
        for f in fns:
            if f.endswith(".go") and not GENERATED.match(f):
                p = os.path.join(dp, f)
                for i, line in enumerate(open(p, encoding="utf-8", errors="replace"), 1):
                    if PREFIX.search(line):
                        bad.append(f"{os.path.relpath(p, rel)}:{i}: {line.strip()}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--keep", action="store_true", help="keep the scratch directory")
    ap.add_argument("--scale", default="1", help="JSONGEN_TEST_SCALE for the generated tests")
    ap.add_argument("--module", default=EXAMPLES, help="the Go module the roots are built in (default: "
                    "examples/; k8s's: examples/k8s/etcd3)")
    ap.add_argument("roots", nargs="*", help="import/path.Type (default: etc/goose.py's)")
    a = ap.parse_args()
    base = os.path.abspath(a.module)
    roots = a.roots or goose_roots(base)
    if not roots:
        sys.exit("jsonmodel_forks: no roots")
    env = dict(os.environ, GOWORK="off", GOFLAGS="-mod=mod")
    env.setdefault("GOPROXY", "off")
    tmp = tempfile.mkdtemp(prefix="jsonmodel-forks-")
    ok = False
    try:
        # the roots' modules (the module cache), copied, writable
        mods = {}
        for r in roots:
            path = r.rpartition(".")[0]
            m = go(["list", "-f", "{{.Module.Path}}", path], base, env).stdout.strip()
            if m in mods:
                continue
            j = json.loads(go(["list", "-m", "-json", m], base, env).stdout)
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
            scan(d, bad, os.path.dirname(d))
        for d in ("models", "examples"):
            scan(os.path.join(ROOT, d), bad, ROOT)
        if bad:
            sys.exit("jsonmodel_forks: code other than the generated methods names JSONModel*:\n" + "\n".join(bad))
        # the scratch module: the examples' go.mod and go.sum, relative replaces made absolute, the
        # roots' modules replaced by the copies
        mod = os.path.join(tmp, "mod")
        os.makedirs(mod)
        shutil.copy(os.path.join(base, "go.mod"), mod)
        shutil.copy(os.path.join(base, "go.sum"), mod)
        j = json.loads(go(["mod", "edit", "-json"], mod, env).stdout)
        edits = []
        for r in j.get("Replace") or []:
            new = r["New"]
            if not new.get("Version") and new["Path"].startswith("."):
                old = r["Old"]["Path"] + ("@" + r["Old"]["Version"] if r["Old"].get("Version") else "")
                edits.append(f"-replace={old}={os.path.normpath(os.path.join(base, new['Path']))}")
        edits += [f"-replace={m}={d}" for m, d in mods.items()]
        if not any(r["Path"] == "models.lab" for r in j.get("Require") or []):
            # the generated code's jsoncodec and the dump's jsondesc
            edits += ["-require=models.lab@v0.0.0-00010101000000-000000000000",
                      f"-replace=models.lab={os.path.join(ROOT, 'models')}"]
        go(["mod", "edit"] + edits, mod, env)
        with open(os.path.join(mod, "main.go"), "w") as f:
            f.write("package main\n\nfunc main() {}\n")
        # 2. the methods and their tests, by -overlay
        header = "// Code generated by jsongen.py (jsonmodel_forks.py). DO NOT EDIT.\n\n"
        try:
            out = jsongen.pkgmodel_files(roots, mod, header, env)
        except jsongen.InputError as e:
            sys.exit(f"jsonmodel_forks: {e}")
        except jsongen.jsongen_core.JsonRefused as e:
            sys.exit("jsonmodel_forks: refused:\n  " + "\n  ".join(e.reasons))
        rep = {}
        for home, (pdir, fs) in out.items():
            for f, c in fs.items():
                p = os.path.join(tmp, "gen", home.replace("/", "_"), f)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, "w") as fh:
                    fh.write(c)
                rep[os.path.join(pdir, f)] = p
        ov = os.path.join(tmp, "overlay.json")
        with open(ov, "w") as fh:
            json.dump({"Replace": rep}, fh, indent=1, sort_keys=True)
        # 3. the generated tests
        pkgs = sorted(out)
        tenv = dict(env, JSONGEN_TEST_SCALE=a.scale)
        r = go(["test", "-count=1", "-v", "-tags", "netmodel", "-overlay", ov, "-run", "^TestJSON",
                "-timeout", "60m"] + pkgs, mod, tenv, check=False)
        for line in r.stdout.splitlines():
            if re.search(r"^(ok|FAIL|---)|JSONGEN-STATS", line):
                print(line.strip())
        if r.returncode != 0:
            print(r.stdout[-6000:] + r.stderr[-3000:])
            sys.exit("jsonmodel_forks: the generated methods differ from encoding/json")
        print(f"jsonmodel_forks: ok ({len(pkgs)} packages: {', '.join(pkgs)})")
        ok = True
    finally:
        if a.keep:
            print(f"(kept {tmp})")
        else:
            shutil.rmtree(tmp, ignore_errors=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
