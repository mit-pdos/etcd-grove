#!/bin/bash
# extract.sh OUT: the trusted files at the merge's two parents (p1 = fs-bytes side, p2 = lean side),
# their merge base, and fs-lean. Run from the worktree root.
set -e
OUT=$1; mkdir -p "$OUT"
M=c7599df2e9
B=$(git merge-base $M^1 $M^2); echo "base $B"
for f in TrustedCode/os.lean TrustedCode/syscall.lean Code/os.toml Code/syscall.toml; do
  b=$(basename $f)
  git show $M^1:$f > "$OUT/p1.$b" || true
  git show $M^2:$f > "$OUT/p2.$b" || true
  git show $B:$f > "$OUT/base.$b" || true
  git show fs-lean:$f > "$OUT/m.$b"
done
