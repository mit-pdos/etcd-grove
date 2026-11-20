#!/usr/bin/env bash
# Configure this clone's merge drivers for notes/STATUS.md and notes/status-history.md
# (etc/merge-status.py; .gitattributes names them). Idempotent; the configuration is shared by every
# worktree of the clone. A clone without it merges the two files as git always does.
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
# an earlier version of this script installed a post-merge hook: remove that one only
hook=$(git rev-parse --path-format=absolute --git-path hooks)/post-merge
if [ -f "$hook" ] && grep -q "^# etcd-grove merge-status post-merge hook$" "$hook"; then
  rm -f "$hook"
  echo "setup-merge-drivers: removed the earlier post-merge hook $hook"
fi
echo "setup-merge-drivers: merge.etcd-status and merge.etcd-history configured"
