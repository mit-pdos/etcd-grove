#!/bin/sh
# Builds server/storage/mvcc with failpoints enabled (what `make gofail-enable` does for the
# e2e and robustness tests), in an etcd checkout given as $1 (default: .).
# At the PR head (6a7dbdf3f) it fails: kvstore_compaction.go declares the failpoints
# compactAfterAcquiredBatchTxLock, compactBeforeCommitBatch, compactAfterCommitBatch,
# compactBeforeSetFinishedCompact and compactAfterSetFinishedCompact more than once.
# At the base (e9b62f804) it builds.
set -e
cd "${1:-.}"
(cd tools/mod && go run go.etcd.io/gofail enable ../../server/storage/mvcc)
(cd server && go build ./storage/mvcc/) && echo "build with failpoints: OK"
