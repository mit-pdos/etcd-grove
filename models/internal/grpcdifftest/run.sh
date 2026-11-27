#!/bin/bash
# The grpc model's evidence (models/grpc, models/README.md): the differential test (grpc_test.go,
# faults_test.go) against the real grpc-go v1.84.0 (this module's go.mod) and against the model
# (models/grpc/gomodel.py: the same module with grpc replaced by the model, tag grpcmodel); the
# invariants every behavior of the model keeps (TestAtMostOnce) with the model's choices random
# (GRPC_MODEL_CHOOSE=random: refusals, idleness, fail-fast failures, any transport failure code,
# any reported address); and the build of examples/ (etcd, its dependencies, the kits) against
# the model. Both modes must pass.
#   --etcd   also run etcd's examples that serve and call over gRPC (putget, watch, lease, auth,
#            putget3, ...) against the model (minutes)
# Usage: models/internal/grpcdifftest/run.sh [--etcd] [go test flags]
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$D/../../.." && pwd)
GM="$ROOT/models/grpc/gomodel.py"
export GOPROXY=off GOFLAGS=-mod=mod GOTOOLCHAIN=${GOTOOLCHAIN:-local} GOWORK=off
etcd=0
if [ "${1:-}" = --etcd ]; then etcd=1; shift; fi
cd "$D"
echo "== real grpc-go"
go vet ./...
go test -count=1 "$@" ./...
echo "== the model (models/grpc)"
"$GM" "$D" vet -tags grpcmodel ./...
"$GM" "$D" test -count=1 -tags grpcmodel "$@" ./...
echo "== the model's rewrites against the library (models/grpc, in-package tests)"
(cd "$ROOT/models/grpc" && go test -count=1 ./internal/mem/)
echo "== the model, its choices random (the invariants)"
GRPC_MODEL_CHOOSE=random "$GM" "$D" test -count=3 -tags grpcmodel -run 'TestAtMostOnce' "$@" ./
echo "== examples/ against the model"
"$GM" "$ROOT/examples" build ./...
"$GM" "$ROOT/examples" vet google.golang.org/grpc google.golang.org/grpc/status google.golang.org/grpc/metadata
if [ $etcd = 1 ]; then
  echo "== etcd's examples against the model"
  "$GM" "$ROOT/examples" test -count=1 -timeout 1200s ./etcd/putget/ ./etcd/watch/ ./etcd/lease/ \
    ./etcd/auth/ ./etcd/putget3/ ./etcd/leasegrant/ ./etcd/compactwatch/ ./etcd/cache/
fi
echo "grpcdifftest: ok"
