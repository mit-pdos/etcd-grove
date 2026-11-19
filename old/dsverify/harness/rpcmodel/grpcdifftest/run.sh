#!/bin/bash
# The grpc and protobuf models' difftest: the same tests (grpc_test.go: calls, errors, deadlines,
# cancellation, reconnection, size limits, status; codec/pb_gen_test.go runs in the real build
# only, against real protobuf) against the real google.golang.org/grpc v1.84.0 and
# google.golang.org/protobuf v1.36.12 (go.mod, the lab's offline module cache) and against the
# models (go.model.mod: ../grpc and ../protobuf substituted; tag rpcmodel). Both must pass.
# Also pbcodec's tests against the real protowire (tag protowire, from this module).
# Usage: ./run.sh [go test flags]     (e.g. ./run.sh -race -count=3)
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
cd "$D"
export GOPROXY=off GOFLAGS=-mod=mod
./gen.py --check
echo "== real grpc and protobuf"
go vet ./...
go test -count=1 "$@" ./...
go test -count=1 -tags protowire "$@" dsverify.lab/harness/pbcodec
echo "== the models (harness/rpcmodel/grpc, harness/rpcmodel/protobuf)"
go vet -modfile=go.model.mod -tags rpcmodel ./...
go test -count=1 -modfile=go.model.mod -tags rpcmodel "$@" ./...
