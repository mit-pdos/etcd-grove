#!/bin/sh
# Shows that no Go code in any etcd module names RangeOptions.Key (nor builds an unkeyed
# mvcc.RangeOptions literal): rename the field and type-check every workspace module.
# Usage: no-reader-check.sh <fork checkout at pr-etcd-21612-goose-lean> <scratch dir>
set -e
src=$2/src; rm -rf "$src"; mkdir -p "$src"
git -C "$1" archive HEAD | tar -x -C "$src"
sed -i 's/^\tKey            bool$/\tKeyZZZ_unused  bool/' "$src/server/storage/mvcc/kv.go"
grep -q KeyZZZ_unused "$src/server/storage/mvcc/kv.go"
cd "$src"
for m in $(go list -m -f '{{.Dir}}'); do
  (cd "$m" && for tags in "" cluster_proxy e2e integration cgo; do GOTOOLCHAIN=go1.27.1 go vet -tags "$tags" -composites ./...; done)
done
echo "no reader of RangeOptions.Key"
