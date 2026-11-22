#!/usr/bin/env python3
"""rpcgen: the net/rpc model's codec for a program, derived from its real Go types and methods.

The model of net/rpc (models/net/rpc) replaces gob and reflection by a Codec the program
registers: gob's encoding and decoding for exactly the types the program's RPCs carry, and
reflection's view of its receivers (the methods net/rpc registers, and calling them). The generator
is the trusted artifact, not each output (`notes/decisions.md`, "Trusted generated code: the
generator is the trusted artifact"): the claim, the subset, the refusals, the encoding and gob's
decoding rules it reproduces are the trusted core's, `rpcgen_core.py` (its doc). This file (the
command line, the input, the dump, writing and checking files) and `rpcgen_testgen.py` (the
regression test generated beside each codec) are untrusted.

Use:

    models/net/rpc/rpcgen.py SECTION.toml OUTDIR --pkg NAME [--no-test] [--check]
                             [--dump FILE] [--print-dump]

writes into the Go package directory OUTDIR (package NAME): `rpc_gen.go` (the codec: rpcEncode,
rpcDecode), `rpc_model_gen.go` (Register, in a model build: tag netmodel or goose; the receivers'
table), `rpc_real_gen.go` (Register doing nothing, in a real build) and `rpc_gen_test.go` (its
test against real gob, `go test` in a real build; not with `--no-test`). The program calls
`Register()` before it uses net/rpc. `--check` writes nothing and exits 1 if a file differs;
exit status 2: the input is outside the subset (every reason printed; nothing written).

The input, an [rpc] table in any toml file, names only the receiver types and any extra types:

    [rpc]
    imports = { difftest = "models.lab/internal/rpcdifftest" }   # Go package aliases
    receivers = ["*difftest.Arith"]   # the types of the receivers the program registers
    types = ["string"]                # types a client passes that no listed receiver takes

Everything else (each receiver's methods, as net/rpc's suitableMethods finds them, and the
structure of every type the methods take) is derived by reflection: OUTDIR's Go module (the
nearest go.mod above it) must import the receivers' packages and `models.lab/rpcdesc`; rpcgen
writes a throwaway main package there that calls `rpcdesc.Main` with the roots (`go run`,
GOWORK=off), whose JSON output is the dump the core reads. `--dump FILE` reads a saved dump instead
(no Go), `--print-dump` prints the derived one. Example: `models/internal/rpcdifftest/`.

The evidence for the generator (untrusted): the generated regression tests, and the differential
test over random types, `models/internal/rpcgenrand` (`go test`; RPCGEN_RAND_TYPES,
RPCGEN_RAND_SEED).
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rpcgen_core  # noqa: E402
import rpcgen_testgen  # noqa: E402


class InputError(Exception):
    pass


TYPE_EXPR = re.compile(r"^[\w\.\[\]\*]+$")


def read_input(path):
    """(aliases, receivers, types) of the toml's [rpc] table."""
    with open(path, "rb") as fh:
        doc = tomllib.load(fh)
    rpc = doc.get("rpc")
    if not isinstance(rpc, dict):
        raise InputError(f"{path}: no [rpc] table")
    for k in rpc:
        if k not in ("imports", "receivers", "types"):
            raise InputError(f"{path}: [rpc]: unknown key {k!r} (methods and type structures are "
                             "derived: name the receiver types)")
    aliases = rpc.get("imports", {})
    receivers = rpc.get("receivers", [])
    types = rpc.get("types", [])
    if not isinstance(aliases, dict) or not all(isinstance(v, str) and v for v in aliases.values()):
        raise InputError(f"{path}: [rpc].imports: {{alias = \"import/path\"}}")
    for x in receivers + types:
        if not isinstance(x, str) or not TYPE_EXPR.match(x):
            raise InputError(f"{path}: {x!r}: a Go type expression over the imports' aliases")
        for a in re.findall(r"(\w+)\.", x):
            if a not in aliases:
                raise InputError(f"{path}: {x!r}: alias {a} is not in [rpc].imports")
    if not receivers and not types:
        raise InputError(f"{path}: [rpc]: no receivers and no types")
    if len(set(receivers)) != len(receivers) or len(set(types)) != len(types):
        raise InputError(f"{path}: a type listed twice")
    return aliases, receivers, types


def module_root(d):
    d = os.path.abspath(d)
    while True:
        if os.path.exists(os.path.join(d, "go.mod")):
            return d
        up = os.path.dirname(d)
        if up == d:
            raise InputError(f"{d}: not in a Go module")
        d = up


def derive(aliases, receivers, types, outdir):
    """The dump of the roots, by rpcdesc run in OUTDIR's Go module."""
    mod = module_root(outdir if os.path.isdir(outdir) else os.path.dirname(os.path.abspath(outdir)))
    tmp = tempfile.mkdtemp(prefix="_rpcgendump", dir=mod)
    try:
        used = sorted({a for x in receivers + types for a in re.findall(r"(\w+)\.", x)})
        with open(os.path.join(tmp, "main.go"), "w") as fh:
            fh.write("package main\n\nimport (\n\t\"reflect\"\n\n\t\"models.lab/rpcdesc\"\n")
            for a in used:
                fh.write(f"\t{a} \"{aliases[a]}\"\n")
            fh.write(")\n\nfunc main() {\n\trpcdesc.Main([]rpcdesc.Root{\n")
            for x in receivers:
                fh.write(f"\t\t{{Expr: {json.dumps(x)}, Type: reflect.TypeFor[{x}]()}},\n")
            fh.write("\t}, []rpcdesc.Root{\n")
            for x in types:
                fh.write(f"\t\t{{Expr: {json.dumps(x)}, Type: reflect.TypeFor[{x}]()}},\n")
            fh.write("\t})\n}\n")
        env = dict(os.environ, GOWORK="off")
        r = subprocess.run(["go", "run", "./" + os.path.basename(tmp)], cwd=mod, env=env,
                           capture_output=True, text=True)
        if r.returncode != 0:
            raise InputError(f"the dump failed (go run in {mod}):\n{r.stderr}")
        return json.loads(r.stdout)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def audit_line(S):
    nm = sum(len(ms) for _, ms in S.receivers)
    return (f"{len(S.closure)} types ({len(S.roots)} top-level), {len(S.receivers)} receivers, "
            f"{nm} methods")


def files(S, header, pkg, test):
    out = {"rpc_gen.go": rpcgen_core.codec_go(S, header, pkg),
           "rpc_model_gen.go": rpcgen_core.model_go(S, header, pkg),
           "rpc_real_gen.go": rpcgen_core.real_go(header, pkg)}
    if test:
        out["rpc_gen_test.go"] = rpcgen_testgen.gen_test_go(S, header, pkg)
    return out


def gofmt(src):
    r = subprocess.run(["gofmt"], input=src, capture_output=True, text=True)
    if r.returncode != 0:
        raise InputError(f"gofmt failed on the generated code (a generator bug):\n{r.stderr}")
    return r.stdout


def write_files(fs, outdir, check):
    ok = True
    for f, c in fs.items():
        c = gofmt(c)
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
    ap = argparse.ArgumentParser(description="The net/rpc model's codec for the receivers and types "
                                 "of an [rpc] table, derived by reflection.")
    ap.add_argument("toml", help="a toml file holding an [rpc] table")
    ap.add_argument("outdir", help="the Go package directory to write the files into")
    ap.add_argument("--pkg", required=True, help="the Go package name")
    ap.add_argument("--no-test", action="store_true", help="do not write rpc_gen_test.go")
    ap.add_argument("--check", action="store_true", help="write nothing; exit 1 if a file differs")
    ap.add_argument("--dump", metavar="FILE", help="read the dump from FILE (no Go run)")
    ap.add_argument("--print-dump", action="store_true", help="print the derived dump")
    a = ap.parse_args()
    try:
        aliases, receivers, types = read_input(a.toml)
        if a.dump:
            with open(a.dump) as fh:
                dump = json.load(fh)
        else:
            dump = derive(aliases, receivers, types, a.outdir)
        if a.print_dump:
            json.dump(dump, sys.stdout, indent=1)
            print()
        S = rpcgen_core.Schema(dump, aliases)
        header = f"// Code generated by rpcgen.py from {os.path.basename(a.toml)}. DO NOT EDIT.\n\n"
        if not write_files(files(S, header, a.pkg, not a.no_test), a.outdir, a.check):
            return 1
    except InputError as e:
        print(f"rpcgen: {e}", file=sys.stderr)
        return 1
    except rpcgen_core.RpcRefused as e:
        print(f"rpcgen: refused, outside the subset ({a.toml}):", file=sys.stderr)
        for r in e.reasons:
            print(f"  {r}", file=sys.stderr)
        return 2
    if not a.check:
        print(f"{a.outdir}: {audit_line(S)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
