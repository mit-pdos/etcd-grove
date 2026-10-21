#!/usr/bin/env python3
"""This repository's declarations no result uses (needs an up-to-date `lake build`).

Runs `etc/dead-decls.lean` on the root modules (every `Link.lean` and `Results.lean`, in
the groups `etc/tcb-report.py` uses) and reports, per file of `Spec/` and `Proof/` (and a
part's), the declarations no root reaches: dead unless kept for a reason (a result stated
for readers, a definition meant for a later proof).  `--results-only` also lists those that
only `Results` roots reach (a linked result does not).  Modules no root imports are listed
whole.  `--json FILE` writes the merged data.  Never builds; don't commit its output.
"""

import argparse
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import proof_roots as pr  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--results-only", action="store_true",
                    help="also list declarations only Results roots reach")
    ap.add_argument("--prefix", default="", help="only files below this path")
    ap.add_argument("--json", help="write the merged data to this file")
    ap.add_argument("--reuse", help="read the merged data from this file instead of running Lean")
    ap.add_argument("--assume-built", action="store_true",
                    help="skip the up-to-date check (read the .olean files as they are)")
    a = ap.parse_args()
    prog = "etc/dead-decls.py"
    if a.reuse:
        with open(a.reuse) as f:
            decls = json.load(f)
    else:
        env = dict(os.environ)
        env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
        if not a.assume_built:
            pr.check_built(prog, env)
        decls = {}
        for mods in pr.lean_runs():
            r = subprocess.run(pr.lake("env", "lean", "--run", "etc/dead-decls.lean",
                                       *pr.lean_args(), *mods),
                               cwd=pr.ROOT, env=env, capture_output=True, text=True)
            if r.returncode != 0:
                sys.exit(f"{prog}: etc/dead-decls.lean failed:\n{r.stderr[-2000:]}")
            for line in r.stdout.splitlines():
                o = json.loads(line)
                k = o["module"] + " " + o["name"]
                p = decls.get(k)
                if p:
                    o["link"] = o["link"] or p["link"]
                    o["results"] = o["results"] or p["results"]
                decls[k] = o
        if a.json:
            with open(a.json, "w") as f:
                json.dump(decls, f)
    seen_mods = {o["module"] for o in decls.values()}
    files = {}
    for o in decls.values():
        if o["kind"] in ("meta", "ctor", "rec") or o["link"]:
            continue
        if o["results"] and not a.results_only:
            continue
        files.setdefault(pr.mod_path(o["module"]), []).append(o)
    total = 0
    for path in sorted(files):
        if not path.startswith(a.prefix):
            continue
        ds = sorted(files[path], key=lambda o: o["line"])
        n = sum(o["endLine"] - o["line"] + 1 for o in ds)
        total += n
        print(f"{path}: {len(ds)} declarations, {n} lines")
        for o in ds:
            tag = " (Results)" if o["results"] else ""
            print(f"  {o['line']}-{o['endLine']} {o['kind']} {o['name']}{tag}")
    unimported = []
    for d in pr.PROJECT_DIRS:
        for dp, _, fs in os.walk(os.path.join(pr.ROOT, d)):
            for f in fs:
                if f.endswith(".lean"):
                    m = pr.module_of(os.path.join(dp, f))
                    if pr.is_project(m) and m not in seen_mods and pr.mod_path(m).startswith(a.prefix):
                        unimported.append(pr.mod_path(m))
    if unimported:
        print(f"\nModules no root imports ({len(unimported)}):")
        for p in sorted(unimported):
            print(f"  {p}")
    print(f"\n{total} lines in unused declarations")


if __name__ == "__main__":
    main()
