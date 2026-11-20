#!/usr/bin/env bash
# Configure this clone's merge drivers for notes/STATUS.md and notes/status-history.md
# (etc/merge-status.py; .gitattributes names them), and the post-merge hook that amends a merge
# commit with the "Last updated" entries the STATUS driver evicted into the working tree's
# status-history.md (when the merge keeps ours' history: git runs no history driver then).
# Idempotent; the configuration and the hook are shared by every worktree of the clone. A clone
# without them merges the two files as git always does.
#
#   etc/setup-merge-drivers.sh
set -eu
cd "$(dirname "$0")/.."
# a branch whose tree predates the driver merges as git always does
drv() {
  printf 'if test -f etc/merge-status.py; then python3 etc/merge-status.py %s %%O %%A %%B %%P; else git merge-file -L ours -L base -L theirs %%A %%O %%B; fi' "$1"
}
git config merge.etcd-status.name "etcd-grove notes/STATUS.md (etc/merge-status.py)"
git config merge.etcd-status.driver "$(drv status)"
git config merge.etcd-history.name "etcd-grove notes/status-history.md, append-only (etc/merge-status.py)"
git config merge.etcd-history.driver "$(drv history)"
hooks=$(git rev-parse --path-format=absolute --git-path hooks)
hook=$hooks/post-merge
marker="# etcd-grove merge-status post-merge hook"
if [ -e "$hook" ] && ! grep -q "$marker" "$hook"; then
  echo "setup-merge-drivers: $hook exists and is not ours; add this line to it:"
  echo "  test -f etc/merge-status.py && python3 etc/merge-status.py --post-merge"
else
  mkdir -p "$hooks"
  printf '#!/bin/sh\n%s\ntest -f etc/merge-status.py && python3 etc/merge-status.py --post-merge\nexit 0\n' \
    "$marker" > "$hook"
  chmod +x "$hook"
fi
echo "setup-merge-drivers: merge.etcd-status and merge.etcd-history configured; post-merge hook in $hook"
