#!/bin/bash
# The third-party library models' evidence (models/gods, models/uuid, models/concurrent-map;
# models/README.md): the same tests against the real modules (this module's go.mod: gods v1.18.1,
# uuid v1.3.1, concurrent-map v1.0.0) and against the models (a temporary -modfile: this go.mod
# with the three replaced by the models' directories, tag tpmodel). Each build checks the
# libraries against the tests' references and writes its transcripts (what it observed); the two
# builds' transcripts must be equal.
# Usage: models/internal/tpdifftest/run.sh [go test flags]
set -euo pipefail
D=$(cd "$(dirname "$0")" && pwd)
M=$(cd "$D/../.." && pwd)
export GOPROXY=off GOFLAGS=-mod=mod GOTOOLCHAIN=${GOTOOLCHAIN:-local} GOWORK=off
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/real" "$tmp/model"
cp "$D/go.mod" "$tmp/go.model.mod"
cp "$D/go.sum" "$tmp/go.model.sum"
go mod edit -replace=github.com/emirpasic/gods="$M/gods" \
  -replace=github.com/google/uuid="$M/uuid" \
  -replace=github.com/orcaman/concurrent-map="$M/concurrent-map" "$tmp/go.model.mod"
# the uuid model requires goose's primitive (its go.mod); the sums are the model's
cat "$M/uuid/go.sum" >> "$tmp/go.model.sum"
cd "$D"
echo "== the real modules"
go vet ./...
TPDIFF_OUT="$tmp/real" go test -count=1 "$@" ./...
echo "== the models"
go vet -modfile="$tmp/go.model.mod" -tags tpmodel ./...
TPDIFF_OUT="$tmp/model" go test -modfile="$tmp/go.model.mod" -count=1 -tags tpmodel "$@" ./...
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
echo "tpdifftest: ok"
