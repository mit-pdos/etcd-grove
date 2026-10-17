#!/usr/bin/env python3
"""List the functions whose Goose translation differs between `lean` and this branch.

Run from the worktree of pr-verify/raft-292:  python3 -I notes/pr-verify/raft-292/changed-impls.py
Compares Code/go_etcd_io/raft/v3.lean at the given base revision (default `lean`) with the working
tree, ignoring the `go: log.go:L:C` position comments the PR's line shifts change.
"""
import re, subprocess, sys
base = sys.argv[1] if len(sys.argv) > 1 else "lean"
PATH = "Code/go_etcd_io/raft/v3.lean"

def impls(txt):
    d, cur, buf = {}, None, []
    for line in txt.splitlines():
        m = re.match(r"noncomputable def (\S+)\.impl", line)
        if m:
            if cur: d[cur] = "\n".join(buf)
            cur, buf = m.group(1), []
        elif cur:
            buf.append(line)
    if cur: d[cur] = "\n".join(buf)
    return d

old = impls(subprocess.run(["git", "show", f"{base}:{PATH}"], capture_output=True, text=True, check=True).stdout)
new = impls(open(PATH).read())
strip = lambda s: re.sub(r"go: log\.go:\d+:\d+", "", s)
changed = sorted(k for k in new if k in old and strip(old[k]) != strip(new[k]))
print(len(changed)); print("\n".join(changed))
print("added/removed:", sorted(set(old) ^ set(new)))
