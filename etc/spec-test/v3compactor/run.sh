#!/bin/sh
# Runs spec_test.go inside etcd's `v3compactor` package at the pinned revision (README.md).
# Arguments go to the test: run.sh -spec-runs 500 -spec-mutant no-first
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
pin=$(python3 -c "import re,sys; s=open('$root/etc/goose.py').read(); i=s.index('name=\"etcd\"'); print(re.search(r'rev=\"([0-9a-f]+)\"', s[i:]).group(1))")
toolchain=$(sed -n 's/^GO_TOOLCHAIN = "\(.*\)"/\1/p' "$root/etc/goose.py")
src="$root/.lake/spec-test/v3compactor-$pin"
if [ ! -d "$src" ]; then
  mkdir -p "$src"
  git -C "$root/.lake/go-src/etcd" cat-file -e "$pin^{commit}" 2>/dev/null ||
    git -C "$root/.lake/go-src/etcd" fetch -q origin "$pin"
  git -C "$root/.lake/go-src/etcd" archive "$pin" server api client pkg | tar -x -C "$src"
  find "$src" -xtype l -delete   # client/v3's example tests link into tests/, not extracted
fi
cp "$here/spec_test.go" "$src/server/etcdserver/api/v3compactor/zz_spec_test.go"
cd "$src/server"
GOTOOLCHAIN="$toolchain" go test ./etcdserver/api/v3compactor -run "TestSpec.*" -count=1 -v -args "$@"
