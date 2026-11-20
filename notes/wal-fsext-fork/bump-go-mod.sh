#!/bin/bash
# The examples' go.mod/go.sum moved to the fork commit etc/goose.py pins (fix 0009, d3feef9bc,
# branch goose-lean-walfs3-fp9, pushed 2026-11-19; before: 0007-0008, 34dea163a, goose-lean-walfs3-fp). Run from the worktree root (never in the main
# checkout). Each go.mod replace line and each go.sum line of the old pseudo-version is rewritten to
# the new one, with the hashes `go mod download -json` reports; nothing else changes.
set -e
OLD=v3.0.0-20261118203246-34dea163a76c
NEW=v3.0.0-20261119013048-d3feef9bcddd
cd "$(git rev-parse --show-toplevel)"
export GOWORK=off GOTOOLCHAIN=go1.27.3 GOFLAGS=-mod=mod PATH=/usr/local/go/bin:$PATH
tmp=$(mktemp -d)
for f in $(grep -rl --include=go.mod --include=go.sum "$OLD" examples); do
  for m in $(grep -o "github.com/upamanyus/etcd/[a-z0-9/]* $OLD" "$f" | awk '{print $1}' | sort -u); do
    [ -s "$tmp/$(echo $m | tr / _)" ] || (cd "$tmp" && go mod download -json "$m@$NEW" > "$tmp/$(echo $m | tr / _)")
    j="$tmp/$(echo $m | tr / _)"
    sum=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["Sum"])' "$j")
    gms=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["GoModSum"])' "$j")
    case "$f" in
      *go.sum)
        sed -i "s|^$m $OLD h1:.*|$m $NEW $sum|; s|^$m $OLD/go.mod h1:.*|$m $NEW/go.mod $gms|" "$f" ;;
      *go.mod)
        sed -i "s|$m $OLD|$m $NEW|g" "$f" ;;
    esac
  done
done
rm -rf "$tmp"
grep -rn --include=go.mod --include=go.sum "$OLD" examples || echo "no $OLD left"
