#!/bin/bash
# The same tests against the real net/rpc and net/http and against the models: both must pass.
# Usage: ./run.sh [go test flags]
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
cd "$D"
./gen.py --check
G=$(mktemp -d)/goroot; trap 'rm -rf "$(dirname "$G")"' EXIT
echo "== real net/rpc"
go test -count=1 "$@" ./...
echo "== the model (harness/rpcmodel)"
"$D/../goroot.sh" "$G" >/dev/null
GOROOT=$G GOFLAGS="${GOFLAGS:-} -tags=rpcmodel" go test -count=1 "$@" ./...
