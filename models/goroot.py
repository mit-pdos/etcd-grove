#!/usr/bin/env python3
"""goroot: build Go programs with the models of standard-library packages in place of the real ones.

A model of a standard-library package (`models/<import path>/`, e.g. `models/net/rpc/`; the
table STD_MODELS below) is the package's Go source, changed where the model replaces Go's code:
its `.go` files are the package (every `.go` file of the real package directory is replaced by
the model's file of the same name, or removed if the model has none; the model may add files).
The standard library cannot be replaced by a Go module (`replace` does not apply to it), so a
model build substitutes the files in the toolchain's source tree, in one of two ways:

    models/goroot.py overlay [OUT.json] [--pkg net/rpc ...]
        writes a `go build -overlay` file (default: .lake/models/overlay.json under the repository
        root) and prints its path: `go build -overlay $(models/goroot.py overlay) -tags netmodel ...`,
        `go test -overlay ...`. The go command applies the overlay to GOROOT's files too.
    models/goroot.py farm DIR [--pkg ...]
        makes DIR a GOROOT of symbolic links to the toolchain's, but for the modelled packages'
        directories, whose `.go` files are the model's; prints DIR. For tools that load packages
        with golang.org/x/tools/go/packages (goose): go/packages reads the files `go list` names
        from disk, so it sees the real files under an overlay passed in GOFLAGS (and cannot open
        the files an overlay adds); run them with GOROOT=DIR, GOTOOLCHAIN=local and DIR/bin first
        in PATH.

Both are the same substitution (`mapping`). The toolchain is `go env GOROOT`'s: it must be
go1.27.3 (etc/goose.py's GO_TOOLCHAIN), the version the models are of (the command refuses
another). The models' own modules are `models/net/go.mod`, `models/encoding/go.mod` and
`models/log/go.mod` (modules
nothing builds: they keep the files out of `models.lab`'s `./...`, since they compile only as
standard-library packages).
"""

import argparse
import json
import os
import subprocess
import sys

MODELS = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(MODELS)
GO_VERSION = "go1.27.3"

# The modelled standard-library packages: import path -> the model's directory under models/.
STD_MODELS = {
    "net/rpc": "net/rpc",
    "net/http": "net/http",
    "encoding/json": "encoding/json",
    "log/slog": "log/slog",
}


def goroot():
    env = dict(os.environ)
    env.setdefault("GOTOOLCHAIN", GO_VERSION)
    r = subprocess.run(["go", "env", "GOROOT", "GOVERSION"], capture_output=True, text=True,
                       env=env, check=True)
    root, version = r.stdout.split()
    if version != GO_VERSION:
        sys.exit(f"goroot.py: the toolchain is {version}; the models are of {GO_VERSION}")
    return root


def go_files(d):
    return sorted(f for f in os.listdir(d)
                  if f.endswith(".go") and not f.endswith("_test.go")
                  and os.path.isfile(os.path.join(d, f)))


def mapping(groot, pkgs):
    """{path of a real file under groot/src: the model's file, or "" (removed)}, per package."""
    out = {}
    for pkg in pkgs:
        real = os.path.join(groot, "src", pkg)
        model = os.path.join(MODELS, STD_MODELS[pkg])
        mf = go_files(model)
        for f in go_files(real):
            out[os.path.join(real, f)] = ""
        for f in mf:
            out[os.path.join(real, f)] = os.path.join(model, f)
    return out


def write_overlay(out, pkgs):
    m = mapping(goroot(), pkgs)
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    tmp = out + ".tmp"
    with open(tmp, "w") as fh:
        json.dump({"Replace": m}, fh, indent=1, sort_keys=True)
    os.replace(tmp, out)
    return out


def _link_dir(src, dst, keep, override):
    """dst: a directory of links to src's entries, but for the names in `override` (made by the
    caller) and only the entries `keep(name)` accepts."""
    os.makedirs(dst, exist_ok=True)
    for name in os.listdir(src):
        if name in override or not keep(name):
            continue
        os.symlink(os.path.join(src, name), os.path.join(dst, name))


def make_farm(d, pkgs):
    groot = goroot()
    if os.path.lexists(d):
        if not os.path.isfile(os.path.join(d, ".models-farm")):
            sys.exit(f"goroot.py: {d} exists and is not a farm this script made")
        subprocess.run(["rm", "-rf", d], check=True)
    os.makedirs(d)
    open(os.path.join(d, ".models-farm"), "w").close()
    # the directories on the way to a modelled package are made; everything else is a link
    made = {""}
    for pkg in pkgs:
        parts = pkg.split("/")
        for i in range(1, len(parts) + 1):
            made.add("/".join(parts[:i]))
    _link_dir(groot, d, lambda n: n != ".models-farm", {"src"})

    def build(rel):
        src = os.path.join(groot, "src", rel)
        dst = os.path.join(d, "src", rel)
        sub = {n for n in os.listdir(src) if (rel + "/" + n if rel else n) in made}
        if rel in pkgs:
            # the package directory: its subdirectories and non-Go files linked, its Go files
            # the model's
            model = os.path.join(MODELS, STD_MODELS[rel])
            real_go = set(go_files(src))
            _link_dir(src, dst, lambda n: n not in real_go, sub)
            for f in go_files(model):
                os.symlink(os.path.join(model, f), os.path.join(dst, f))
        else:
            _link_dir(src, dst, lambda n: True, sub)
        for n in sorted(sub):
            build(rel + "/" + n if rel else n)

    build("")
    return d


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    o = sub.add_parser("overlay")
    o.add_argument("out", nargs="?", default=os.path.join(ROOT, ".lake", "models", "overlay.json"))
    o.add_argument("--pkg", action="append", choices=sorted(STD_MODELS))
    f = sub.add_parser("farm")
    f.add_argument("dir")
    f.add_argument("--pkg", action="append", choices=sorted(STD_MODELS))
    a = ap.parse_args()
    pkgs = a.pkg or sorted(STD_MODELS)
    if a.cmd == "overlay":
        print(write_overlay(a.out, pkgs))
    else:
        print(make_farm(os.path.abspath(a.dir), pkgs))


if __name__ == "__main__":
    main()
