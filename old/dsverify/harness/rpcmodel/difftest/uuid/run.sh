#!/bin/bash
# The uuid model (harness/rpcmodel/uuid) against the real github.com/google/uuid v1.3.1: the same
# tests (uuid_test.go) build against each (go.mod: the real module; go.model.mod: the model, as a
# kit's replace substitutes it), both must pass, and what TestSameBytes writes must be the same.
# The real module is not in the lab's offline cache: it comes from a module cache of the test's
# own (UUID_MODCACHE, default cache/uuid-difftest-modcache), filled once from the public proxy:
#   GOMODCACHE=$UUID_MODCACHE GOPROXY=https://proxy.golang.org GOFLAGS=-modcacherw \
#     go mod download github.com/google/uuid@v1.3.1
# Usage: ./run.sh [go test flags]     (e.g. ./run.sh -race -count=3)
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
cd "$D"
C=${UUID_MODCACHE:-$(cd "$D/../../../.." && pwd)/cache/uuid-difftest-modcache}
[ -d "$C/github.com/google/uuid@v1.3.1" ] || {
  echo "run.sh: no github.com/google/uuid@v1.3.1 in $C (see the header)" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
export GOPROXY=off GOFLAGS=-mod=mod
echo "== real github.com/google/uuid v1.3.1"
GOMODCACHE=$C UUID_DIFF_OUT=$T/real.txt go test "$@" .
echo "== the model (harness/rpcmodel/uuid)"
UUID_DIFF_OUT=$T/model.txt go test -modfile=go.model.mod "$@" .
diff "$T/real.txt" "$T/model.txt"
echo "== same ID, Time, Version, Variant and String on $(($(wc -l < "$T/real.txt") - 2)) UUIDs"
