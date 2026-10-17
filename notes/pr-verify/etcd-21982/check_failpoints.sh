#!/bin/sh
# Lists the gofail points the robustness suite names for compaction and whether the server
# code still declares each. Run from the root of an etcd checkout.
for fp in $(grep -o 'goPanicFailpoint{"compact[A-Za-z]*"' tests/robustness/failpoint/gofail.go | sed 's/.*{"//; s/"//'); do
  if grep -rq "gofail: var $fp " server/; then echo "$fp: declared"; else echo "$fp: MISSING"; fi
done
