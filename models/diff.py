#!/usr/bin/env python3
"""diff: a model's difference from the library it models, computed from the two sources.

A model of a library (models/README.md) is a Go package (or tree of packages) in this directory,
the first-class artifact: we write, test and verify it. Its difference from the real library is not
kept anywhere; this script computes it, for review:

    models/diff.py MODEL [--stat]

MODEL is the model's directory under models/ (`grpc`). Prints the unified diff from the pinned
upstream source to the model (`--stat`: per file, lines added and removed, the totals, and the
upstream packages the model does not have). For each directory of the model holding Go files, the
upstream directory of the same package is compared: a file in both is diffed, a file only in the
model is added, an upstream Go file (not a test) missing from the model is removed. Non-Go files
(scripts, notes) are not part of the comparison.

MINIMAL VERSION (branch models-grpc, 2026-11-20): module models only. Branch models-rpc-http has the
full script (the same command line, the standard-library models through models/goroot.py, and this
same MODULE_MODELS table, empty there); when both land, keep that one and add the grpc entry below.
"""

import argparse
import difflib
import json
import os
import subprocess
import sys

MODELS = os.path.dirname(os.path.abspath(__file__))

# Models of Go modules: the model's directory under models/ -> (module path, version). The model's
# tree mirrors the module's (a package at <dir>/<sub> models the module's <path>/<sub>).
MODULE_MODELS = {
    "grpc": ("google.golang.org/grpc", "v1.84.0"),
}


def go_files(d):
    if not os.path.isdir(d):
        return set()
    return {f for f in os.listdir(d) if f.endswith(".go") and not f.endswith("_test.go")
            and os.path.isfile(os.path.join(d, f))}


def upstream_root(model):
    if model not in MODULE_MODELS:
        sys.exit(f"diff.py: {model}: not a known model ({', '.join(sorted(MODULE_MODELS))})")
    path, version = MODULE_MODELS[model]
    env = dict(os.environ, GOWORK="off", GOFLAGS="-mod=mod")
    env.setdefault("GOPROXY", "off")
    r = subprocess.run(["go", "mod", "download", "-json", f"{path}@{version}"],
                       capture_output=True, text=True, check=True, cwd=MODELS, env=env)
    return json.loads(r.stdout)["Dir"]


def model_dirs(model, up):
    """[(model directory, upstream directory)] of the model's Go package directories."""
    base = os.path.join(MODELS, model)
    out = []
    for d, _, fs in os.walk(base):
        if any(f.endswith(".go") for f in fs):
            out.append((d, os.path.join(up, os.path.relpath(d, base))))
    return sorted(out)


def dropped_packages(model, up):
    """The upstream package directories (but tests', examples' and testdata) the model lacks."""
    base = os.path.join(MODELS, model)
    out = []
    for d, dirs, fs in os.walk(up):
        rel = os.path.relpath(d, up)
        if go_files(d) and not os.path.isdir(os.path.join(base, rel)):
            out.append(rel)
    return sorted(out)


def read(p):
    with open(p, encoding="utf-8", errors="surrogateescape") as fh:
        return fh.read().splitlines(keepends=True)


def diffs(model, up):
    out = []
    for md, ud in model_dirs(model, up):
        rel = os.path.relpath(md, MODELS)
        for f in sorted(go_files(md) | go_files(ud)):
            a = read(os.path.join(ud, f)) if f in go_files(ud) else []
            b = read(os.path.join(md, f)) if f in go_files(md) else []
            if a != b:
                out.append((os.path.join(rel, f), a, b, f in go_files(ud), f in go_files(md)))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("model")
    ap.add_argument("--stat", action="store_true")
    a = ap.parse_args()
    model = a.model.strip("/")
    up = upstream_root(model)
    tot_add = tot_del = 0
    rows = []
    for rel, old, new, in_up, in_model in diffs(model, up):
        lines = list(difflib.unified_diff(old, new, "upstream/" + rel if in_up else "/dev/null",
                                          "model/" + rel if in_model else "/dev/null"))
        add = sum(1 for l in lines if l.startswith("+") and not l.startswith("+++"))
        dele = sum(1 for l in lines if l.startswith("-") and not l.startswith("---"))
        tot_add, tot_del = tot_add + add, tot_del + dele
        kind = "added" if not in_up else "removed" if not in_model else "changed"
        rows.append((rel, kind, add, dele))
        if not a.stat:
            sys.stdout.writelines(l if l.endswith("\n") else l + "\n" for l in lines)
    if a.stat:
        w = max([len(r[0]) for r in rows] + [10])
        for rel, kind, add, dele in rows:
            print(f"{rel:<{w}}  {kind:<7}  +{add:<6} -{dele}")
        print(f"{len(rows)} files differ: +{tot_add} -{tot_del} lines")
        dropped = dropped_packages(model, up)
        print(f"{len(dropped)} upstream package directories are not in the model (the packages no "
              f"program here reaches, or no longer reaches through the model)")


if __name__ == "__main__":
    main()
