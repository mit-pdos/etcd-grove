#!/bin/bash
# The differential tests of the log/slog model (models/log/slog; models/README.md): the same tests
# against Go 1.27.3's log/slog and against the model (an overlay of the toolchain's source,
# models/goroot.py; tag netmodel); each build checks its own claims (no argument method called,
# nothing written, the outside-the-model panics in the model) and writes its transcripts (returns,
# panics), and the two builds' transcripts must be equal.
# The overlay needs a go1.27.3 toolchain outside the module cache (as internal/jsonstreamtest/run.sh):
# GO127 (default ~/sdk/go1.27.3), else a copy of the module cache's in .lake/go1.27.3 (made once).
# Usage: models/internal/slogdifftest/run.sh [go test flags]
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
ov=$(python3 goroot.py overlay "$M/../.lake/models/overlay-slog.json" --pkg log/slog)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/real" "$tmp/model"
echo "== Go's log/slog"
go vet ./internal/slogdifftest/
SLOGDIFF_OUT="$tmp/real" go test -count=1 "$@" ./internal/slogdifftest/
echo "== the model (models/log/slog)"
go vet -overlay "$ov" -tags netmodel ./internal/slogdifftest/
SLOGDIFF_OUT="$tmp/model" go test -count=1 -overlay "$ov" -tags netmodel "$@" ./internal/slogdifftest/
echo "== the transcripts"
[ "$(ls "$tmp/real")" = "$(ls "$tmp/model")" ] || { echo "transcript sets differ"; exit 1; }
for f in "$tmp/real"/*.txt; do
  b=$(basename "$f")
  if cmp -s "$f" "$tmp/model/$b"; then echo "$b: equal ($(wc -l < "$f") lines)"
  else echo "$b: DIFFERS"; diff "$f" "$tmp/model/$b" | head -20; exit 1; fi
done
echo "slogdifftest: ok"
