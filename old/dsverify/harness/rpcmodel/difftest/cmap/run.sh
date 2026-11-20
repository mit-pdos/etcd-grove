#!/bin/bash
# The concurrent-map model (harness/rpcmodel/cmap) against the real
# github.com/orcaman/concurrent-map v1.0.0: the same tests (cmap_test.go) build against each
# (go.mod: the real module; go.model.mod: the model, as a kit's replace substitutes it), and both
# must pass. The real module is not in the lab's offline cache: it comes from a module cache of
# the test's own (CMAP_MODCACHE, default cache/cmap-difftest-modcache), filled once from the
# public proxy:
#   GOMODCACHE=$CMAP_MODCACHE GOPROXY=https://proxy.golang.org GOFLAGS=-modcacherw \
#     go mod download github.com/orcaman/concurrent-map@v1.0.0
# Usage: ./run.sh [go test flags]     (e.g. ./run.sh -race -count=3)
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
cd "$D"
C=${CMAP_MODCACHE:-$(cd "$D/../../../.." && pwd)/cache/cmap-difftest-modcache}
[ -d "$C/cache/download/github.com/orcaman/concurrent-map/@v" ] || {
  echo "run.sh: no github.com/orcaman/concurrent-map@v1.0.0 in $C (see the header)" >&2; exit 1; }
export GOPROXY=off GOFLAGS=-mod=mod GOSUMDB=off
echo "== real github.com/orcaman/concurrent-map v1.0.0"
GOMODCACHE=$C go test "$@" .
echo "== the model (harness/rpcmodel/cmap)"
go test -modfile=go.model.mod "$@" .
