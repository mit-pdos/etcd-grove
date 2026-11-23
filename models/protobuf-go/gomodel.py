#!/usr/bin/env python3
"""The protobuf model as a Go module: google.golang.org/protobuf v1.36.12 with this directory's
packages in place of its own.

    models/protobuf-go/gomodel.py assemble DIR       write the model module into DIR (new or empty)
    models/protobuf-go/gomodel.py run MODDIR GOARGS  run `go GOARGS` in the module MODDIR with
                                                     google.golang.org/protobuf replaced by the model
                                                     (e.g. `run models/internal/pbmodeltest test ./...`)

The model (models/README.md, "The protobuf model") changes two packages of protobuf-go, `proto`
(the codec's entry points dispatch to the methods pbgen's pbmodel mode emits: proto/model.go) and
`protoadapt` (MessageV2Of); they are kept here, first-class, as protobuf-go's files with the changes
marked `MODEL:` (`models/diff.py protobuf-go` computes the difference). Every other package of the
module is protobuf-go's, unchanged: rather than keeping a copy of the 16 MB module, `assemble`
takes it from the module cache (`go mod download`, offline: the version the models' go.sum has) and
replaces the files of each package this directory has (the upstream non-test Go files of that
package removed, this directory's copied in). `run` assembles into a temporary directory and runs
go with a -modfile (the module's go.mod plus the `replace`, as models/grpc/gomodel.py does: the
normal build never sees the model), GOFLAGS=-mod=mod and GOPROXY=off unless set.
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile

MODEL = os.path.dirname(os.path.abspath(__file__))
MODELS = os.path.dirname(MODEL)
PATH, VERSION = "google.golang.org/protobuf", "v1.36.12"


def env():
    e = dict(os.environ)
    e.setdefault("GOPROXY", "off")
    e.setdefault("GOFLAGS", "-mod=mod")
    e.setdefault("GOWORK", "off")
    return e


def upstream():
    r = subprocess.run(["go", "mod", "download", "-json", f"{PATH}@{VERSION}"], cwd=MODELS, env=env(),
                       capture_output=True, text=True, check=True)
    return json.loads(r.stdout)["Dir"]


def model_packages():
    """The package directories of the model (relative), each with its Go files."""
    out = {}
    for d, dns, fs in os.walk(MODEL):
        dns[:] = [x for x in dns if not x.startswith((".", "_"))]
        go = sorted(f for f in fs if f.endswith(".go"))
        if go:
            out[os.path.relpath(d, MODEL)] = go
    return out


def assemble(dst):
    if os.path.exists(dst) and os.listdir(dst):
        sys.exit(f"gomodel.py: {dst} is not empty")
    if os.path.exists(dst):
        os.rmdir(dst)
    shutil.copytree(upstream(), dst)
    for dp, dns, fs in os.walk(dst):
        os.chmod(dp, 0o755)
        for f in fs:
            os.chmod(os.path.join(dp, f), 0o644)
    for rel, files in model_packages().items():
        d = os.path.join(dst, rel)
        if not os.path.isdir(d):
            sys.exit(f"gomodel.py: {rel}: no such package in {PATH} {VERSION}")
        for f in os.listdir(d):
            if f.endswith(".go") and not f.endswith("_test.go"):
                os.remove(os.path.join(d, f))
        for f in files:
            shutil.copy(os.path.join(MODEL, rel, f), os.path.join(d, f))


def run(mod, args):
    mod = os.path.abspath(mod)
    tmp = tempfile.mkdtemp(prefix="pbgomodel-")
    try:
        assemble(os.path.join(tmp, "protobuf"))
        modfile = os.path.join(tmp, "go.model.mod")
        shutil.copy(os.path.join(mod, "go.mod"), modfile)
        if os.path.exists(os.path.join(mod, "go.sum")):
            shutil.copy(os.path.join(mod, "go.sum"), os.path.join(tmp, "go.model.sum"))
        e = env()
        j = json.loads(subprocess.run(["go", "mod", "edit", "-json", modfile], env=e, check=True,
                                      capture_output=True, text=True).stdout)
        edits = []
        for r in j.get("Replace") or []:
            new = r["New"]
            if not new.get("Version") and new["Path"].startswith("."):
                old = r["Old"]["Path"] + ("@" + r["Old"]["Version"] if r["Old"].get("Version") else "")
                edits.append(f"-replace={old}={os.path.normpath(os.path.join(mod, new['Path']))}")
        edits.append(f"-replace={PATH}={os.path.join(tmp, 'protobuf')}")
        subprocess.run(["go", "mod", "edit"] + edits + [modfile], env=e, check=True)
        return subprocess.run(["go", args[0], "-modfile=" + modfile] + args[1:], cwd=mod, env=e).returncode
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "assemble":
        assemble(os.path.abspath(sys.argv[2]))
        return 0
    if len(sys.argv) >= 4 and sys.argv[1] == "run":
        return run(sys.argv[2], sys.argv[3:])
    sys.exit(__doc__)


if __name__ == "__main__":
    sys.exit(main())
