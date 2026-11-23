#!/bin/bash
# The differential tests of the encoding/json model: the same stream tests against Go's real
# encoding/json and against the model (an overlay of the toolchain's source, models/goroot.py; tag
# netmodel); both must reproduce the golden transcripts the real build wrote (go test -update).
# The overlay needs a go1.27.3 toolchain outside the module cache (go refuses to overlay files under
# GOMODCACHE, where GOTOOLCHAIN=go1.27.3 puts it): GO127 (default ~/sdk/go1.27.3, golang.org/dl's
# place), else a copy of the module cache's in .lake/go1.27.3 (made once).
# Usage: models/internal/jsonstreamtest/run.sh [go test flags]
set -euo pipefail
M=$(cd "$(dirname "$0")/../.." && pwd)
cd "$M"
GO127=${GO127:-$HOME/sdk/go1.27.3}
if ! [ -x "$GO127/bin/go" ]; then
  GO127="$M/../.lake/go1.27.3"
  if ! [ -x "$GO127/bin/go" ]; then
    src=$(GOTOOLCHAIN=go1.27.3 go env GOROOT)
    mkdir -p "$M/../.lake"
    cp -r "$src" "$GO127.tmp" && chmod -R u+w "$GO127.tmp" && mv "$GO127.tmp" "$GO127"
  fi
fi
export PATH="$GO127/bin:$PATH" GOWORK=off GOTOOLCHAIN=local
[ "$(go env GOVERSION)" = go1.27.3 ] || { echo "run.sh: go1.27.3 is needed (GO127)"; exit 1; }
python3 json/jsongen.py internal/jsonvsr/json.toml internal/jsonvsr/codec --pkg codec --check
ov=$(python3 goroot.py overlay "$M/../.lake/models/overlay-json.json" --pkg encoding/json)
echo "== real encoding/json"
go test -count=1 "$@" ./internal/jsonstreamtest/ ./internal/jsonvsr/... ./internal/jsonpkgtest/
echo "== the model (models/encoding/json)"
go vet -overlay "$ov" -tags netmodel ./internal/jsonstreamtest/ ./internal/jsonvsr/... ./internal/jsondifftest/... ./internal/jsonpkgtest/
go test -count=1 -overlay "$ov" -tags netmodel "$@" ./internal/jsonstreamtest/
# jsongen's same-package mode under the model's dispatch (its generated json_model_gen_test.go compares
# the methods with the real encoding/json, so it runs in the real build's netmodel test only: the
# gates' `go test -tags netmodel` of the package)
go test -count=1 -overlay "$ov" -tags netmodel -run '^TestDispatch' "$@" ./internal/jsonpkgtest/
