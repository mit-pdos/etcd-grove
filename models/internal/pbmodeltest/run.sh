#!/bin/bash
# The protobuf model's evidence (models/protobuf-go; models/README.md, "The protobuf model"): the same
# tests against the real google.golang.org/protobuf v1.36.12 (this module's go.mod) and against the
# model (models/protobuf-go/gomodel.py: the module assembled with the model's packages, tag
# protomodel); both with tag pbmodel (pbdifftest's messages with their generated methods). Each
# build writes its transcripts; the two builds' transcripts must be equal. And the model's
# NotModelled cases: a panic in the model, protobuf-go's behavior otherwise.
# Usage: models/internal/pbmodeltest/run.sh [go test flags]
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
M=$(cd "$D/../.." && pwd)
export GOPROXY=off GOFLAGS=-mod=mod GOTOOLCHAIN=${GOTOOLCHAIN:-local} GOWORK=off
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/real" "$tmp/model"
cd "$D"
echo "== protobuf-go v1.36.12"
go vet -tags pbmodel ./...
PBMODEL_OUT="$tmp/real" go test -count=1 -tags pbmodel "$@" ./...
echo "== the model"
python3 "$M/protobuf-go/gomodel.py" run "$D" vet -tags pbmodel,protomodel ./...
PBMODEL_OUT="$tmp/model" python3 "$M/protobuf-go/gomodel.py" run "$D" test -count=1 -tags pbmodel,protomodel "$@" ./...
echo "== the transcripts"
for f in "$tmp/real"/*.txt; do
  b=$(basename "$f")
  if cmp -s "$f" "$tmp/model/$b"; then
    echo "$b: equal ($(wc -l < "$f") lines)"
  else
    echo "$b: DIFFERS"; diff "$f" "$tmp/model/$b" | head -20; exit 1
  fi
done
[ "$(ls "$tmp/real" | wc -l)" = "$(ls "$tmp/model" | wc -l)" ] || { echo "transcript sets differ"; exit 1; }
echo "pbmodeltest: ok"
