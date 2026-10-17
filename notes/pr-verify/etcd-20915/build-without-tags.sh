#!/usr/bin/env bash
# Build etcd with the PR's scripts/build.sh from a checkout without reachable `v*` tags
# (a source tarball: no .git; a shallow clone: no tags) and start it once.
# Usage: build-without-tags.sh ETCD_CLONE BRANCH OUTDIR
# (BRANCH: a branch at the PR head b7e2d97fc, e.g. pr-etcd-20915, or one at its base b1d3e04be
# for the contrast run.)
set -u
clone=$1 rev=$2 out=$3
mkdir -p "$out"
run() { # $1: name, $2: source dir
  (cd "$2" && ./scripts/build.sh > "$out/$1-build.log" 2>&1; echo "$1: build exit $?"
   ./bin/etcd --version | head -2
   timeout 20 ./bin/etcd --data-dir "$out/$1-data" --listen-client-urls http://127.0.0.1:0 \
     --advertise-client-urls http://127.0.0.1:2379 --listen-peer-urls http://127.0.0.1:0 \
     > "$out/$1-run.log" 2>&1
   echo "$1: run exit $? (124: still serving at the 20 s timeout)"
   grep -A10 -m1 '^panic' "$out/$1-run.log")
}
mkdir -p "$out/tarball" && git -C "$clone" archive "$rev" | tar -x -C "$out/tarball"
run tarball "$out/tarball"
git clone -q --depth 1 --no-tags -b "$rev" "file://$(cd "$clone" && pwd)" "$out/shallow"
run shallow "$out/shallow"
