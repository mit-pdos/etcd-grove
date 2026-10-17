#!/bin/bash
# lake build with the shared cache; print errors only (with context) and the summary
cd "${WORKTREE:-/shared/etcd-grove-pr/raft-140}"
LOG="${LOG:-$(mktemp)}"
LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true timeout 5400 lake build "$@" > "$LOG" 2>&1
st=$?
grep -n -A25 "^error" "$LOG" | head -${LINES_MAX:-150}
grep "^✖\|Build completed\|error: build failed\|Some required" "$LOG" | head -20
echo "exit $st"
