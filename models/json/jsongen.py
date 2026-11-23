#!/usr/bin/env python3
"""jsongen: the encoding/json model's codec for a program, derived from its real Go types.

The model of encoding/json (`models/encoding/json`) replaces reflection by a codec the program
registers: an encoder and a decoder for exactly the program's types, and the JSON scanner
(`models.lab/jsoncodec.Scan`). The generator is the trusted artifact, not each output
(`notes/decisions.md`, "Trusted generated code: the generator is the trusted artifact"): the claim,
the subset, the refusals and the encoding and decoding rules it reproduces, cited to Go 1.27.3's
encoding/json, are the trusted core's, `jsongen_core.py` (its doc). This file (the command line, the
input, the dump, writing and checking files) and `jsongen_testgen.py` (the regression test
generated beside each codec) are untrusted.

Use:

    models/json/jsongen.py SECTION.toml OUTDIR --pkg NAME [--no-test] [--check]
                           [--dump FILE] [--print-dump]

writes into the Go package directory OUTDIR (package NAME): `json_gen.go` (the codec: jsonMarshal,
jsonUnmarshal, Goose-translatable), `json_extra_gen.go` (the code of unnamed root struct types,
outside Goose: build tag !goose; with `json_extra_goose_gen.go`, the stub Goose sees; without such
types, json_extra_gen.go is the stub), `json_model_gen.go` (RegisterJSON, in a model build: tag
netmodel or goose), `json_real_gen.go` (RegisterJSON doing nothing, in a real build) and
`json_gen_test.go` (its test against the real encoding/json, `go test` in a real build; not with
`--no-test`). With `package = "<import path>"` in the table (the same-package mode, jsongen_core.py's
THE SAME-PACKAGE METHODS), OUTDIR is that package's directory and the files are `json_model_gen.go`
(the roots' JSONModel* methods, tag goose or netmodel) and `json_model_gen_test.go` (`go test -tags
netmodel`: the methods against the real encoding/json); etc/goose.py writes them to a scratch
directory and hands them to goose by -overlay instead (Project.jsonmodel_roots). The program calls `RegisterJSON()` before it uses encoding/json. `--check` writes
nothing and exits 1 if a file differs; exit status 2: the input is outside the subset (every reason
printed; nothing written).

The input, a [json] table in any toml file, names only the root types:

    [json]
    imports = { events = "github.com/tangledbytes/go-vsr/pkg/events" }   # Go package aliases
    roots = ["events.Event", "events.Request", "[]events.Request",
             'struct { Type events.EventType "json:\\"@type\\""; Data json.RawMessage "json:\\"data\\"" }']

A root is a Go type expression over the imports' aliases (and `json` for encoding/json): every type
the program passes to Marshal, Unmarshal, an Encoder or a Decoder (the codec covers T and *T), or
stores in an `any` it marshals. Everything else (the structure of every type they reach) is derived
by reflection: OUTDIR's Go module (the nearest go.mod above it) must import the roots' packages and
`models.lab/jsondesc`; jsongen writes a throwaway main package there that calls `jsondesc.Main`
with the roots (`go run`, GOWORK=off), whose JSON output is the dump the core reads. `--dump FILE`
reads a saved dump instead (no Go), `--print-dump` prints the derived one. Examples:
`models/internal/jsondifftest/`, `models/internal/jsonvsr/`.

The evidence for the generator (untrusted): the generated regression tests, and the differential
test over random types, `models/internal/jsongenrand` (`go test`; JSONGEN_RAND_TYPES,
JSONGEN_RAND_SEED, JSONGEN_TEST_SCALE).
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
import jsongen_core  # noqa: E402
import jsongen_testgen  # noqa: E402


class InputError(Exception):
    pass


def read_input(path):
    """(aliases, roots, package) of the toml's [json] table (package: the same-package mode's import
    path, or None)."""
    with open(path, "rb") as fh:
        doc = tomllib.load(fh)
    js = doc.get("json")
    if not isinstance(js, dict):
        raise InputError(f"{path}: no [json] table")
    for k in js:
        if k not in ("imports", "roots", "package"):
            raise InputError(f"{path}: [json]: unknown key {k!r} (type structures are derived: "
                             "name the root types)")
    aliases = js.get("imports", {})
    roots = js.get("roots", [])
    if not isinstance(aliases, dict) or not all(isinstance(v, str) and v for v in aliases.values()):
        raise InputError(f"{path}: [json].imports: {{alias = \"import/path\"}}")
    if "json" in aliases:
        raise InputError(f"{path}: [json].imports: json is encoding/json (do not list it)")
    if not roots:
        raise InputError(f"{path}: [json]: no roots")
    if not all(isinstance(x, str) and x for x in roots) or len(set(roots)) != len(roots):
        raise InputError(f"{path}: [json].roots: distinct Go type expressions")
    for x in roots:
        for a in re.findall(r"\b([A-Za-z_]\w*)\.", x):
            if a not in aliases and a != "json":
                raise InputError(f"{path}: root {x!r}: alias {a} is not in [json].imports")
    home = js.get("package")
    if home is not None and (not isinstance(home, str) or not home):
        raise InputError(f"{path}: [json].package: an import path")
    return aliases, roots, home


def module_root(d):
    d = os.path.abspath(d)
    while True:
        if os.path.exists(os.path.join(d, "go.mod")):
            return d
        up = os.path.dirname(d)
        if up == d:
            raise InputError(f"{d}: not in a Go module")
        d = up


def derive(aliases, roots, outdir, env=None):
    """The dump of the roots, by jsondesc run in OUTDIR's Go module (`env`: the go command's
    environment; None: os.environ with GOWORK=off)."""
    mod = module_root(outdir if os.path.isdir(outdir) else os.path.dirname(os.path.abspath(outdir)))
    tmp = tempfile.mkdtemp(prefix="_jsongendump", dir=mod)
    try:
        used = sorted({a for x in roots for a in re.findall(r"\b([A-Za-z_]\w*)\.", x)})
        with open(os.path.join(tmp, "main.go"), "w") as fh:
            fh.write("package main\n\nimport (\n\t\"reflect\"\n\n\t\"models.lab/jsondesc\"\n")
            for a in used:
                fh.write(f"\t{a} \"{'encoding/json' if a == 'json' else aliases[a]}\"\n")
            fh.write(")\n\nfunc main() {\n\tjsondesc.Main([]jsondesc.Root{\n")
            for x in roots:
                fh.write(f"\t\t{{Expr: {json.dumps(x)}, Type: reflect.TypeFor[{x}]()}},\n")
            fh.write("\t})\n}\n")
        # the CLI: the module alone; a caller's env (etc/goose.py: its workspace) as it is
        env = dict(os.environ, GOWORK="off") if env is None else dict(env)
        r = subprocess.run(["go", "run", "./" + os.path.basename(tmp)], cwd=mod, env=env,
                           capture_output=True, text=True)
        if r.returncode != 0:
            raise InputError(f"the dump failed (go run in {mod}):\n{r.stderr}")
        return json.loads(r.stdout)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def derive_home(home, names, moddir, env=None):
    """The dump of the named types `names` of package `home` (unexported ones too), by jsondesc run
    in the Go module at `moddir`: an overlay adds to `home` a file returning the types
    (reflect.TypeFor), which a throwaway main package passes to jsondesc (`go run -overlay`)."""
    env = dict(os.environ if env is None else env)
    if all(n[0].isupper() for n in names):
        # exported: nameable from a main package (no overlay, which Go refuses in the module cache)
        return derive({"h": home}, ["h." + n for n in names], moddir, env)
    r = subprocess.run(["go", "list", "-f", "{{.Dir}} {{.Name}}", home], cwd=moddir, env=env,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise InputError(f"go list {home} (in {moddir}) failed:\n{r.stderr}")
    pdir, pname = r.stdout.split()
    tmp = tempfile.mkdtemp(prefix="_jsongendump", dir=moddir)
    try:
        roots_go = os.path.join(tmp, "roots.go")
        with open(roots_go, "w") as fh:
            fh.write(f"package {pname}\n\nimport \"reflect\"\n\n"
                     "func JSONModelDescRoots() []reflect.Type {\n\treturn []reflect.Type{\n")
            for n in names:
                fh.write(f"\t\treflect.TypeFor[{n}](),\n")
            fh.write("\t}\n}\n")
        ov = os.path.join(tmp, "overlay.json")
        with open(ov, "w") as fh:
            json.dump({"Replace": {os.path.join(pdir, "zz_jsonmodel_desc_roots.go"): roots_go}}, fh)
        main = os.path.join(tmp, "main")
        os.makedirs(main)
        with open(os.path.join(main, "main.go"), "w") as fh:
            fh.write("package main\n\nimport (\n\t\"models.lab/jsondesc\"\n\n"
                     f"\th {json.dumps(home)}\n)\n\nfunc main() {{\n\tts := h.JSONModelDescRoots()\n"
                     "\tjsondesc.Main([]jsondesc.Root{\n")
            for k, n in enumerate(names):
                fh.write(f"\t\t{{Expr: {json.dumps('h.' + n)}, Type: ts[{k}]}},\n")
            fh.write("\t})\n}\n")
        r = subprocess.run(["go", "run", "-overlay", ov, "./" + os.path.relpath(main, moddir)], cwd=moddir,
                           env=env, capture_output=True, text=True)
        if r.returncode != 0:
            raise InputError(f"the dump of {home} failed (go run in {moddir}):\n{r.stderr}")
        return json.loads(r.stdout)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def pkgmodel_files(roots, moddir, header, env=None, test=True):
    """The same-package mode for the roots "import/path.Type" (grouped by package): {import path:
    (package directory, {file name: contents})}, the files gofmt'ed; the dumps are derived in the Go
    module at `moddir` (derive_home). Raises InputError, jsongen_core.JsonRefused."""
    by = {}
    for r in roots:
        path, _, ty = r.rpartition(".")
        if not path or not is_ident(ty):
            raise InputError(f"jsonmodel root {r!r}: not import/path.Type")
        by.setdefault(path, []).append(ty)
    out = {}
    for home, names in sorted(by.items()):
        dump = derive_home(home, names, moddir, env)
        S = jsongen_core.Schema(dump, {"h": home}, home=home)
        r = subprocess.run(["go", "list", "-f", "{{.Dir}} {{.Name}}", home], cwd=moddir, env=env,
                           capture_output=True, text=True)
        pdir, pname = r.stdout.split()
        fs = files(S, header, pname, test)
        out[home] = (pdir, {f: gofmt(c, f) for f, c in fs.items()})
    return out


def is_ident(s):
    return re.fullmatch(r"[A-Za-z_]\w*", s) is not None


def audit_line(S):
    named = sum(1 for i in S.closure if S.goose(i))
    return f"{len(S.closure)} types ({len(S.roots)} roots, {len(S.closure) - named} unnamed)"


def files(S, header, pkg, test):
    if S.home is not None:
        # the same-package mode: one file in the package (and its test, a netmodel build's)
        out = {"json_model_gen.go": jsongen_core.pkgmodel_go(S, header, pkg)}
        if test:
            out["json_model_gen_test.go"] = jsongen_testgen.gen_test_go(S, header, pkg)
        return out
    out = {"json_gen.go": jsongen_core.codec_go(S, header, pkg)}
    out.update(jsongen_core.extra_go(S, header, pkg))
    out["json_model_gen.go"] = jsongen_core.model_go(header, pkg)
    out["json_real_gen.go"] = jsongen_core.real_go(header, pkg)
    if test:
        out["json_gen_test.go"] = jsongen_testgen.gen_test_go(S, header, pkg)
    return out


def gofmt(src, name):
    r = subprocess.run(["gofmt"], input=src, capture_output=True, text=True)
    if r.returncode != 0:
        raise InputError(f"gofmt failed on the generated {name} (a generator bug):\n{r.stderr}")
    return r.stdout


def write_files(fs, outdir, check):
    ok = True
    stale = [f for f in os.listdir(outdir) if f.startswith("json_") and f.endswith("_gen.go" if "json_model_gen.go" in fs else ".go")
             and f.endswith(".go") and f not in fs] if os.path.isdir(outdir) else []
    for f, c in fs.items():
        c = gofmt(c, f)
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
    for f in stale:
        p = os.path.join(outdir, f)
        if check:
            print(f"not generated (remove it): {p}", file=sys.stderr)
            ok = False
        else:
            os.remove(p)
            print(f"removed {p}")
    return ok


def main():
    ap = argparse.ArgumentParser(description="The encoding/json model's codec for the root types of "
                                 "a [json] table, derived by reflection.")
    ap.add_argument("toml", help="a toml file holding a [json] table")
    ap.add_argument("outdir", help="the Go package directory to write the files into")
    ap.add_argument("--pkg", required=True, help="the Go package name")
    ap.add_argument("--no-test", action="store_true", help="do not write json_gen_test.go")
    ap.add_argument("--check", action="store_true", help="write nothing; exit 1 if a file differs")
    ap.add_argument("--dump", metavar="FILE", help="read the dump from FILE (no Go run)")
    ap.add_argument("--print-dump", action="store_true", help="print the derived dump")
    a = ap.parse_args()
    try:
        aliases, roots, home = read_input(a.toml)
        if a.dump:
            with open(a.dump) as fh:
                dump = json.load(fh)
        elif home is not None:
            # the same-package mode: the roots are home's named types (alias.Name), unexported too
            names = []
            for x in roots:
                al, _, n = x.rpartition(".")
                if aliases.get(al) != home or not is_ident(n):
                    raise InputError(f"{a.toml}: root {x!r}: the same-package mode's roots are named "
                                     f"types of {home} (alias.Name)")
                names.append(n)
            dump = derive_home(home, names, module_root(a.outdir))
        else:
            dump = derive(aliases, roots, a.outdir)
        if a.print_dump:
            json.dump(dump, sys.stdout, indent=1)
            print()
        S = jsongen_core.Schema(dump, aliases, home=home)
        header = f"// Code generated by jsongen.py from {os.path.basename(a.toml)}. DO NOT EDIT.\n\n"
        if not write_files(files(S, header, a.pkg, not a.no_test), a.outdir, a.check):
            return 1
    except InputError as e:
        print(f"jsongen: {e}", file=sys.stderr)
        return 1
    except jsongen_core.JsonRefused as e:
        print(f"jsongen: refused, outside the subset ({a.toml}):", file=sys.stderr)
        for r in e.reasons:
            print(f"  {r}", file=sys.stderr)
        return 2
    if not a.check:
        print(f"{a.outdir}: {audit_line(S)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
