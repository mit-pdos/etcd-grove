# Files for the verification of etcd-io/etcd#22096

The report is `notes/pr-verify/etcd-22096.md`. Revisions: the PR head is `811687dc57b38a17350bce1a11012361bc0172b2`,
the upstream merge base `3bc83eea262f086274b47f030b7901d0400e3f78`. The verified fork commit is `995f783a1`
(`mit-pdos/etcd-grove` branch `pr-etcd-22096-goose-lean`): the PR applied to the fork's `goose-lean` `09669450f`.
Go: `GOTOOLCHAIN=go1.27.1`. Each test is in package `mvcc`: `cp <file> <etcd>/server/storage/mvcc/ && cd <etcd>/server && go test ./storage/mvcc/ -run <Name> -v`.

| File | What it shows | Runs against | Command (after the `cp`) |
|---|---|---|---|
| `kvstore_logical_bytes_386_test.go` | `TestLogicalBytesAlignment`: on `GOARCH=386`, `store.logicalBytes` is at offset 116 (not 8-byte aligned) and the PR's `atomic` calls panic (`unaligned 64-bit atomic operation`) in `NewStore`. On amd64 it passes. | PR head: fails on 386, passes on amd64 | `GOARCH=386 go test ./storage/mvcc/ -run TestLogicalBytesAlignment -v` |
| `kvstore_logical_bytes_386_test.pr.log` | the 386 run (panic) then the amd64 run (pass) | PR head | as above |
| `pr-own-tests-386.pr.log` | the PR's own `TestStoreLogicalBytes` and the existing `TestKVRestore` panic on 386 | PR head | `GOARCH=386 go test ./storage/mvcc/ -run 'TestStoreLogicalBytes$\|TestKVRestore$'` (no `cp`) |
| `mvcc-386.base.log` | the whole mvcc package passes on 386 at the merge base | merge base | `GOARCH=386 go test ./storage/mvcc/` (no `cp`) |
| `kvstore_logical_bytes_random_test.go` | `TestLogicalBytesRandomized` (adapted from etcd#22475's verification): 40 random histories (puts incl. empty values, deletes, range deletes, multi-op txns, compactions, restarts, `Restore`) with `restoreChunkKeys = 7`; after each step `LogicalBytes()` equals the sum of `len(key)+len(value)` of a full `Range`. Covers the untranslated restore path. | PR head and fork branch: pass | `go test ./storage/mvcc/ -run TestLogicalBytesRandomized` |
| `kvstore_logical_bytes_random_test.pr.log` | the run above | PR head | as above |
| `logical_bytes_review_test.go` (reviewer) | `TestReviewLogicalBytesMidTxn`: within a txn the counter shows uncommitted changes (0 after a delete, before the re-put and `End`); `TestReviewLogicalBytesGlobalGauge`: the gauge reports the last store set up; `TestReviewLogicalBytesConcurrent`: 4 writers + compaction + 4 lock-free readers, then `Restore`s, under `-race`. All pass (they log the values). | PR head | `go test -race -count=1 -v -run 'TestReview\|TestLogicalBytesRandomized\|TestStoreLogicalBytes' ./storage/mvcc/` |
| `logical_bytes_review_test.pr.log` | the reviewer's run above (with the random test and the PR's tests) | PR head | as above |
