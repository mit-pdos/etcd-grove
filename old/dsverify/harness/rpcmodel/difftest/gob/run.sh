#!/bin/bash
# The encoding/gob model's tests against Go's encoding/gob and against the model (goroot.sh OUT
# gob, tag rpcmodel): both must pass. Usage: ./run.sh [go test flags]
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
cd "$D"
G=$(mktemp -d)/goroot; trap 'rm -rf "$(dirname "$G")"' EXIT
echo "== real encoding/gob"
go test -count=1 "$@" ./...
echo "== the model (harness/rpcmodel/src/encoding/gob)"
"$D/../../goroot.sh" "$G" gob >/dev/null
GOROOT=$G GOFLAGS="${GOFLAGS:-} -tags=rpcmodel" go test -count=1 "$@" ./...
