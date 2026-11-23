#!/bin/bash
# The third-party library models' evidence (models/gods, models/uuid, models/concurrent-map;
# models/README.md): the same tests against the real modules (this module's go.mod: gods v1.18.1,
# uuid v1.3.1, concurrent-map v1.0.0) and against the models (a temporary -modfile: this go.mod
# with the three replaced by the models' directories, tag tpmodel). Each build checks the
# libraries against the tests' references and writes its transcripts (what it observed); the two
# builds' transcripts must be equal.
# The pinned modules are fetched first if the module cache lacks them (GOPROXY=off otherwise):
# from $TPDIFF_GOPROXY, default proxy.golang.org.
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
# the pinned modules (and goose's primitive, the uuid model's) in the module cache
fetch() {
  (cd "$1" && { go mod download "${@:2}" 2>/dev/null ||
    GOPROXY=${TPDIFF_GOPROXY:-https://proxy.golang.org} GOFLAGS=-mod=mod go mod download "${@:2}"; })
}
fetch "$D" github.com/emirpasic/gods github.com/google/uuid github.com/orcaman/concurrent-map
fetch "$M/uuid" github.com/goose-lang/primitive
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
# outside the uuid model's premise: a package initialized before uuid assigns crypto/rand.Reader
echo "== randprobe (outside the claim: crypto/rand.Reader assigned before uuid's initialization)"
R="$D/testdata/randprobe"
cp "$R/go.mod" "$tmp/rp.mod"; cp "$R/go.sum" "$tmp/rp.sum"; cat "$M/uuid/go.sum" >> "$tmp/rp.sum"
go mod edit -replace=github.com/google/uuid="$M/uuid" "$tmp/rp.mod"
real=$(cd "$R" && go run .); model=$(cd "$R" && go run -modfile="$tmp/rp.mod" .)
echo "v1.3.1: $real" | tr '\n' ' '; echo; echo "model: $model" | tr '\n' ' '; echo
[ "$real" = $'NewRandom error: no randomness\nNew panicked: true' ] || { echo "randprobe: v1.3.1 unexpected"; exit 1; }
[ "$model" = $'NewRandom error: <nil>\nNew panicked: false' ] || { echo "randprobe: model unexpected"; exit 1; }
echo "tpdifftest: ok"
