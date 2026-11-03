#!/bin/sh
# Runs spec_test.go inside etcd's `etcdserver` package at the pinned revision (README.md).
# ETCD_SRC=DIR: a checkout of the etcd fork to take the pinned revision from (default
# .lake/go-src/etcd, fetched if the revision is missing). SPEC_TABLE=FILE writes the table there.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
pin=$(python3 -c "import re,sys; s=open('$root/etc/goose.py').read(); i=s.index('name=\"etcd\"'); print(re.search(r'rev=\"([0-9a-f]+)\"', s[i:]).group(1))")
toolchain=$(sed -n 's/^GO_TOOLCHAIN = "\(.*\)"/\1/p' "$root/etc/goose.py")
repo=${ETCD_SRC:-$root/.lake/go-src/etcd}
src="$root/.lake/spec-test/bootstrap-$pin"
if [ ! -d "$src" ]; then
  git -C "$repo" cat-file -e "$pin^{commit}" 2>/dev/null ||
    git -C "$repo" fetch -q https://github.com/upamanyus/etcd "$pin"
  mkdir -p "$src"
  git -C "$repo" archive "$pin" server api client pkg | tar -x -C "$src"
  find "$src" -xtype l -delete   # client/v3's example tests link into tests/, not extracted
fi
cp "$here/spec_test.go" "$src/server/etcdserver/zz_bootok_spec_test.go"
# the WAL preallocates 64 MiB segments: the test's directories under `.lake`, not a small `/tmp`
export TMPDIR="${TMPDIR_SPEC:-$root/.lake/spec-test/tmp}"
mkdir -p "$TMPDIR"
cd "$src/server"
GOTOOLCHAIN="$toolchain" go test ./etcdserver -run "TestSpecBootstrap.*" -count=1 -v "$@"
