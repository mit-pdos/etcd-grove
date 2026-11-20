#!/bin/bash
# The differential tests of the net/rpc and net/http models: the same tests against Go's real
# packages and against the models (an overlay of the toolchain's source, models/goroot.py; tag
# netmodel); both must pass. Usage: models/internal/rpcdifftest/run.sh [go test flags]
set -euo pipefail
M=$(cd "$(dirname "$0")/../.." && pwd)
cd "$M"
export GOWORK=off GOTOOLCHAIN=${GOTOOLCHAIN:-go1.27.3}
python3 net/rpc/rpcgen.py internal/rpcdifftest/rpc.toml internal/rpcdifftest/codec --pkg codec --check
ov=$(python3 goroot.py overlay)
echo "== real net/rpc, net/http"
go test -count=1 "$@" ./internal/rpcdifftest/... ./internal/httpdifftest/...
echo "== the models (models/net/rpc, models/net/http)"
go vet -overlay "$ov" -tags netmodel ./internal/rpcdifftest/... ./internal/httpdifftest/...
go test -count=1 -overlay "$ov" -tags netmodel "$@" ./internal/rpcdifftest/... ./internal/httpdifftest/...
