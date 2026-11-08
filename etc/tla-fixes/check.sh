#!/bin/sh
# check.sh RAFT_CHECKOUT WORKDIR: copies RAFT_CHECKOUT (etcd-io/raft at c51f010) to WORKDIR,
# applies the series (patches/), copies in the issue tests and the random driver, and runs
#   1. the trace tests of issues/raft-tla-*: all pass with the series (the model-replay tests
#      TestTLAModel{StaleLeaderCompleteness,MoreUpToDateCutBatches} fail: with the invariant
#      repaired or dropped there is no counterexample to replay; TestTLATraceRestartWithoutSnapshot
#      fails: issues/raft-tla-restart-config-from-storage.md is not fixed);
#   2. TestTLARandom (TLA_SEEDS, default 20) and the TestTLATargeted schedules: nothing rejected;
#   3. raft's own tests.
# Needs TLA_TOOLS (tla2tools.jar, CommunityModules-deps.jar), go and java.
set -e
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
src=$1; work=$2
[ -n "$TLA_TOOLS" ] || { echo "TLA_TOOLS not set" >&2; exit 2; }
git -C "$src" rev-parse HEAD | grep -q '^c51f010c851e' || echo "warning: $src is not at c51f010" >&2
cp -r "$src" "$work"
cd "$work"
git apply "$here"/patches/*.patch
cp "$repo"/issues/raft-tla-*/tla_*_test.go .
cp "$here"/raft/tla_*_test.go .
go vet -tags with_tla .
go test -tags with_tla . -run '^TestTLATrace' -count=1 -v 2>&1 | grep -E '^(--- |ok|FAIL)' || true
go test -tags with_tla . -run '^TestTLA(Random|Targeted)' -count=1 -v -timeout 120m 2>&1 | grep -E 'rejected|panicked|seeds failed|^(--- |ok|FAIL)'
go test . 2>&1 | tail -1
