#!/bin/bash
# run.sh RAFT [COUNT] [SLUG...]: run the hraft-* issues' tests against the hashicorp/raft tree RAFT
# (README.md). Needs Go (and the network or a module cache with hashicorp/raft's dependencies).
set -u
H=$(cd "$(dirname "$0")" && pwd); I=$(dirname "$H")
R=$(cd "${1:?usage: run.sh RAFT [COUNT] [SLUG...]}" && pwd); N=${2:-5}; shift; [ $# -gt 0 ] && shift
S=${*:-$(cd "$I" && ls -d hraft-*/ | tr -d / | grep -v '^hraft-harness$')}
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
cp -r "$H/inproc" "$H/snapstore" "$W/"
for s in $S; do mkdir "$W/$s"; cp "$I/$s"/*_test.go "$W/$s/"; done
printf 'module hraftissue\n\ngo 1.25.0\n\nrequire github.com/hashicorp/raft v1.8.0\n\nreplace github.com/hashicorp/raft => %s\n' "$R" > "$W/go.mod"
(cd "$W" && GOFLAGS=-mod=mod go mod tidy >/dev/null 2>&1) || { echo "run.sh: go mod tidy failed"; exit 2; }
for s in $S; do
  out=$(cd "$W" && go test -count="$N" -timeout 30m "./$s/" -v 2>&1)
  echo "$s: $(echo "$out" | grep -c -- '^--- FAIL') failed, $(echo "$out" | grep -c -- '^--- PASS') passed"
  echo "$out" | grep -m1 -E '^\s+\S+_test.go:[0-9]+: .*(violated|not linearizable|stale read)' | cut -c1-200
done
