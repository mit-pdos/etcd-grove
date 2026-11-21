#!/bin/bash
# The differential tests of the net/rpc and net/http models: the same tests against Go's real
# packages and against the models (a GOROOT of links with the models' files, models/goroot.py farm;
# tag netmodel); both must pass. Always go1.27.3 (etc/goose.py's GO_TOOLCHAIN), the models' release
# (net/http's golden transcripts are its). Usage: models/internal/rpcdifftest/run.sh [go test flags]
set -euo pipefail
M=$(cd "$(dirname "$0")/../.." && pwd)
cd "$M"
export GOWORK=off GOTOOLCHAIN=go1.27.3
python3 net/rpc/rpcgen.py internal/rpcdifftest/rpc.toml internal/rpcdifftest/codec --pkg codec --check
echo "== real net/rpc, net/http"
go test -count=1 "$@" ./internal/rpcdifftest/... ./internal/httpdifftest/...
echo "== the models (models/net/rpc, models/net/http)"
# A GOROOT of links (goroot.py farm), not an overlay: GOTOOLCHAIN fetches go1.27.3 into GOMODCACHE,
# and `go build -overlay` refuses to replace files beneath GOMODCACHE.
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
python3 goroot.py farm "$tmp/goroot" > /dev/null
(export GOROOT="$tmp/goroot" GOTOOLCHAIN=local PATH="$tmp/goroot/bin:$PATH"
 go vet -tags netmodel ./internal/rpcdifftest/... ./internal/httpdifftest/...
 go test -count=1 -tags netmodel "$@" ./internal/rpcdifftest/... ./internal/httpdifftest/...)
