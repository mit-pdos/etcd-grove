#!/usr/bin/env python3
"""pbgen: a protobuf codec, plain Go code per message type, derived from the real schema.

A model of google.golang.org/protobuf replaces reflection by a codec the program registers: an
encoder and a decoder for exactly the message types a program uses, over the wire-format helpers
of `models.lab/pbcodec` (`models/`, translated into the part `Net/`). The generator is the
trusted artifact, not each output (`notes/decisions.md`, "Trusted generated code: the generator is
the trusted artifact"): what is trusted is that the emitted code behaves as protobuf-go v1.36.12's
proto.Marshal/Unmarshal for every schema it accepts. That claim, the subset, the refusals and the
encoding emitted per field kind (with citations) are the trusted core's, `models/protobuf/pbgen_core.py`
(its doc). This file (the command line, the input, the schema dump, writing and checking files)
and `models/protobuf/pbgen_testgen.py` (the regression test generated beside each codec) are untrusted.

Use:

    models/protobuf/pbgen.py SECTION.toml OUTDIR --pkg NAME [--register] [--no-test] [--check]
                 [--dump FILE] [--print-dump]

writes into the Go package directory OUTDIR (package NAME) `pb_gen.go` (the codec: `pbMarshal`,
`pbUnmarshal`) and `pb_gen_test.go` (its tests against the real module, `go test` in OUTDIR's
module, which requires google.golang.org/protobuf; not with `--no-test`); with `--register` also
`pb_model_gen.go`/`pb_real_gen.go` (`registerProto()`: the codec registered with the model of
google.golang.org/protobuf, `proto.SetCodec`, in a model build (tag `rpcmodel` or `goose`); nothing
in a real build). `--check` writes nothing and exits 1 if a file differs (or the schema is
refused). Exit status 2: the schema is outside the subset (every reason printed, naming message
and field; nothing written).

The input, a [protobuf] table in any toml file, names only the root message types:

    [protobuf]
    imports = { pb = "models.lab/internal/pbdifftest/pb" }   # Go package aliases
    roots = ["pb.Args", "pb.Reply"]                             # the root message types (Go types)

The codec covers the roots and every message and enum type their fields reach, with every
field, all derived from the descriptors protoc-gen-go registered for them (the ones the real
proto.Marshal runs on) and their Go structs: OUTDIR's Go module (the nearest go.mod above it) must
import the roots' packages and `models.lab/pbdesc`; pbgen writes a throwaway main package
there that imports them and runs `pbdesc.Main` (`go run`, GOWORK=off), whose JSON output is the
schema dump the core reads. `--dump FILE` reads a saved dump instead (no Go), `--print-dump`
prints the derived dump. A package the closure reaches that `imports` does not name gets its
package name as alias. Examples: `models/internal/pbdifftest/` (the field kinds) and
`examples/models/pbetcd/` (etcd's message types).

The evidence for the generator (untrusted): the differential test over random schemas,
`models/internal/pbgenrand` (`go test`; PBGEN_RAND_SCHEMAS, PBGEN_RAND_SEED), and the generated
regression tests.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pbgen_core  # noqa: E402
import pbgen_testgen  # noqa: E402


class InputError(Exception):
    pass


def read_input(path):
    """(aliases {alias: import path}, roots ["alias.T"]) of the toml's [protobuf] table."""
    with open(path, "rb") as fh:
        doc = tomllib.load(fh)
    pb = doc.get("protobuf")
    if not isinstance(pb, dict):
        raise InputError(f"{path}: no [protobuf] table")
    for k in pb:
        if k not in ("imports", "roots"):
            hint = " (fields are derived from the descriptors: name the root types in `roots`)" \
                if k in ("messages", "enums") else ""
            raise InputError(f"{path}: [protobuf]: unknown key {k!r}{hint}")
    aliases = pb.get("imports", {})
    roots = pb.get("roots", [])
    if not isinstance(aliases, dict) or not all(isinstance(v, str) and v for v in aliases.values()):
        raise InputError(f"{path}: [protobuf].imports: {{alias = \"import/path\"}}")
    if not isinstance(roots, list) or not roots:
        raise InputError(f"{path}: [protobuf].roots: a non-empty list of \"alias.GoType\"")
    for r in roots:
        if not isinstance(r, str) or r.count(".") != 1 or r.split(".")[0] not in aliases:
            raise InputError(f"{path}: root {r!r}: \"alias.GoType\", alias in [protobuf].imports")
    if len(set(roots)) != len(roots):
        raise InputError(f"{path}: a root twice")
    return aliases, roots


def module_root(d):
    d = os.path.abspath(d)
    while True:
        if os.path.exists(os.path.join(d, "go.mod")):
            return d
        up = os.path.dirname(d)
        if up == d:
            raise InputError(f"{d}: not in a Go module")
        d = up


def derive(aliases, roots, outdir):
    """The schema dump of the roots, by pbdesc run in OUTDIR's Go module."""
    mod = module_root(outdir if os.path.isdir(outdir) else os.path.dirname(os.path.abspath(outdir)))
    tmp = tempfile.mkdtemp(prefix="_pbgendump", dir=mod)
    try:
        paths = sorted({aliases[r.split(".")[0]] for r in roots})
        with open(os.path.join(tmp, "main.go"), "w") as fh:
            fh.write("package main\n\nimport (\n\t\"models.lab/pbdesc\"\n")
            for p in paths:
                fh.write(f"\t_ \"{p}\"\n")
            fh.write(")\n\nfunc main() { pbdesc.Main() }\n")
        args = [aliases[r.split(".")[0]] + "." + r.split(".")[1] for r in roots]
        env = dict(os.environ, GOWORK="off")
        r = subprocess.run(["go", "run", "./" + os.path.basename(tmp)] + args, cwd=mod, env=env,
                           capture_output=True, text=True)
        if r.returncode != 0:
            raise InputError(f"the schema dump failed (go run in {mod}):\n{r.stderr}")
        return json.loads(r.stdout)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def audit_line(S):
    nf = sum(len(fs) for fs in S.m.values())
    return (f"{len(S.names)} message types, {nf} fields, {len(S.enums)} enums "
            f"({', '.join(S.names + S.enums)})")


def package_dirs(paths, outdir):
    """{import path: (directory, package name)} of the Go packages `paths`, in OUTDIR's module
    (`go list`); a directory under the module cache or GOROOT is refused (pbmodel mode writes into
    the packages: give it a writable copy, e.g. a module with a `replace` of them)."""
    mod = module_root(outdir)
    env = dict(os.environ, GOWORK="off")
    r = subprocess.run(["go", "list", "-f", "{{.ImportPath}} {{.Dir}} {{.Name}}"] + sorted(paths), cwd=mod,
                       env=env, capture_output=True, text=True)
    if r.returncode != 0:
        raise InputError(f"go list in {mod} failed:\n{r.stderr}")
    env_r = subprocess.run(["go", "env", "GOMODCACHE", "GOROOT"], cwd=mod, env=env, capture_output=True,
                           text=True, check=True).stdout.split()
    out = {}
    for line in r.stdout.splitlines():
        p, d, name = line.split(" ")
        for root in env_r:
            if root and os.path.commonpath([os.path.abspath(d), os.path.abspath(root)]) == os.path.abspath(root):
                raise InputError(f"package {p} is in {d}, under {root}: pbmodel mode writes into the "
                                 "message packages (use a writable copy: a replace in the module)")
        out[p] = (d, name)
    return out


def pbmodel_files(S, header, outdir, test):
    """{path: contents} of pbmodel_gen.go (and pbmodel_gen_test.go) in every package of the closure."""
    dirs = package_dirs({S.pkg[n] for n in S.names}, outdir)
    out = {}
    for path, (d, name) in sorted(dirs.items()):
        out[os.path.join(d, "pbmodel_gen.go")] = pbgen_core.pbmodel_go(S, path, header, name)
        if test:
            out[os.path.join(d, "pbmodel_gen_test.go")] = pbgen_testgen.gen_pbmodel_test_go(S, path, header, name)
    return out


def files(S, header, go_name, register, test):
    out = {"pb_gen.go": pbgen_core.codec_go(S, header, go_name)}
    if register:
        out["pb_model_gen.go"] = pbgen_core.model_go(header, go_name)
        out["pb_real_gen.go"] = pbgen_core.real_go(header, go_name)
    if test:
        out["pb_gen_test.go"] = pbgen_testgen.gen_test_go(S, header, go_name)
    return out


def write_files(fs, outdir, check):
    """Write {file name: contents} into outdir (with `check`, compare only); False if a file
    differed under `check`."""
    ok = True
    for f, c in fs.items():
        p = os.path.join(outdir, f)
        cur = open(p).read() if os.path.exists(p) else None
        if cur == c:
            continue
        if check:
            print(f"not current: {p}", file=sys.stderr)
            ok = False
        else:
            os.makedirs(outdir, exist_ok=True)
            with open(p, "w") as fh:
                fh.write(c)
            print(f"wrote {p}")
    return ok


def main():
    ap = argparse.ArgumentParser(description="A protobuf codec for the root message types of a "
                                 "[protobuf] table, derived from their descriptors.")
    ap.add_argument("toml", help="a toml file holding a [protobuf] table")
    ap.add_argument("outdir", help="the Go package directory to write the files into")
    ap.add_argument("--pkg", help="the Go package name (codec mode)")
    ap.add_argument("--pbmodel", action="store_true",
                    help="the same-package methods instead of a codec: pbmodel_gen.go (and "
                    "pbmodel_gen_test.go) written into the directory of every Go package of the "
                    "closure, as `go list` in OUTDIR's module finds it (--pkg is not used)")
    ap.add_argument("--register", action="store_true",
                    help="also write registerProto (pb_model_gen.go, pb_real_gen.go)")
    ap.add_argument("--no-test", action="store_true", help="do not write pb_gen_test.go")
    ap.add_argument("--check", action="store_true", help="write nothing; exit 1 if a file differs")
    ap.add_argument("--dump", metavar="FILE", help="read the schema dump from FILE (no Go run)")
    ap.add_argument("--print-dump", action="store_true", help="print the derived schema dump")
    a = ap.parse_args()
    try:
        aliases, roots = read_input(a.toml)
        if a.dump:
            with open(a.dump) as fh:
                dump = json.load(fh)
        else:
            dump = derive(aliases, roots, a.outdir)
        if a.print_dump:
            json.dump(dump, sys.stdout, indent=1)
            print()
        S = pbgen_core.Schema(dump, aliases, pbmodel=a.pbmodel)
        header = f"// Code generated by pbgen.py from {os.path.basename(a.toml)}. DO NOT EDIT.\n\n"
        if a.pbmodel:
            fs = pbmodel_files(S, header, a.outdir, not a.no_test)
        elif not a.pkg:
            raise InputError("--pkg NAME is required (codec mode)")
        else:
            fs = files(S, header, a.pkg, a.register, not a.no_test)
    except InputError as e:
        print(f"pbgen: {e}", file=sys.stderr)
        return 1
    except pbgen_core.PbRefused as e:
        print(f"pbgen: refused, outside the subset ({a.toml}):", file=sys.stderr)
        for r in e.reasons:
            print(f"  {r}", file=sys.stderr)
        return 2
    if not write_files(fs, a.outdir, a.check):
        return 1
    if not a.check:
        print(f"{a.outdir}: {audit_line(S)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
