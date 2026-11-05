#!/usr/bin/env bash
# Land the current branch on `lean`: the gates, then the fast-forward, under one lock, so that no
# other landing moves `lean` between them (notes/spec-first-plan.md, "Landing takes a lock").
#
#   etc/land.sh            from the branch's worktree; LAKE_PACKAGES / PERENNIAL_CHECKOUT as for
#                          etc/gates.sh
#
# Under `flock $ETCD_GROVE_LAND_LOCK` (default /shared/tmp/etcd-grove-land.lock), held from the check
# through the fast-forward:
# 1. `lean` must be an ancestor of HEAD (else: merge `lean` first, outside the lock, and rerun);
# 2. if the branch changes only files under notes/ and top-level *.md files (against `lean`; none
#    of them is read by a gate), the gates are skipped;
#    otherwise etc/gates.sh runs under the full-build lock (`flock $ETCD_GROVE_BUILD_LOCK`, default
#    /shared/tmp/etcd-grove-full-build.lock);
# 3. `git merge --ff-only` of the branch in the checkout that has `lean` checked out.
# Waits for the locks (a message says so); never pushes. Do not wrap it in `flock` of the build
# lock yourself: it takes that lock itself, and a second holder would wait on the first forever.
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
land_lock=${ETCD_GROVE_LAND_LOCK:-/shared/tmp/etcd-grove-land.lock}
build_lock=${ETCD_GROVE_BUILD_LOCK:-/shared/tmp/etcd-grove-full-build.lock}
branch=$(git symbolic-ref --short HEAD) || { echo "land: not on a branch"; exit 1; }
[ "$branch" = lean ] && { echo "land: run from the branch's worktree, not lean"; exit 1; }
main=$(git worktree list --porcelain | awk '/^worktree /{w=$2} /^branch refs\/heads\/lean$/{print w}')
[ -n "$main" ] || { echo "land: no worktree has lean checked out"; exit 1; }
[ -z "$(git status --porcelain --untracked-files=no)" ] || { echo "land: uncommitted changes"; exit 1; }

exec 9>>"$land_lock"
if ! flock -n 9; then echo "land: another landing holds $land_lock; waiting"; flock 9; fi
if ! git merge-base --is-ancestor lean HEAD; then
  echo "land: lean ($(git rev-parse --short lean)) is not in $branch: merge lean, then rerun"; exit 1
fi
if [ -z "$(git diff --name-only lean HEAD -- . ':!notes' ':(exclude,top,glob)*.md')" ]; then
  echo "land: notes and top-level docs only, gates skipped"
else
  exec 8>>"$build_lock"
  if ! flock -n 8; then echo "land: a full build holds $build_lock; waiting"; flock 8; fi
  etc/gates.sh || { echo "land: gates failed; lean unchanged"; exit 1; }
  flock -u 8
fi
git -C "$main" merge --ff-only -q "$branch" || { echo "land: fast-forward failed"; exit 1; }
echo "land: lean is now $(git rev-parse --short lean) ($branch)"
