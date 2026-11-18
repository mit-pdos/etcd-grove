#!/bin/bash
# The examples' go.mod/go.sum moved to the fork commit etc/goose.py pins (fixes 0007-0008, 34dea163a,
# branch goose-lean-walfs3-fp), once the user has pushed it. Run from the worktree root (never in the
# main checkout). Then `etc/goose.py --check` passes for the etcd project.
set -e
OLD=v3.0.0-20261115085855-8c28a4296f16
NEW=v3.0.0-20261118203246-34dea163a76c
cd "$(git rev-parse --show-toplevel)"
export GOWORK=off GOTOOLCHAIN=go1.27.3 GOFLAGS=-mod=mod PATH=/usr/local/go/bin:$PATH
for m in $(grep -rl -- "$OLD" --include=go.mod examples); do
  d=$(dirname "$m")
  sed -i "s/$OLD/$NEW/g" "$m"
  mods=$(grep -o "github.com/upamanyus/etcd/[a-z0-9/]* $NEW" "$m" | sed 's/ /@/' | sort -u)
  (cd "$d" && go mod download $mods && go list -m all > /dev/null)
  sed -i "/$OLD/d" "$d/go.sum"
done
grep -rn -- "$OLD" --include=go.mod --include=go.sum examples || true
