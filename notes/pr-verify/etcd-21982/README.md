# etcd#21982: tests, probes and logs

The report is `notes/pr-verify/etcd-21982.md`. Revisions:

- PR head: etcd-io/etcd `9f62dc886b4a5ef248ee993e3a9ef87ed474342a` (base `61d518f55effaf5edcedcb2a696504795b4fa7bd`).
  Its `go.mod` asks for Go 1.26 (`toolchain go1.26.4`); with Go 1.27 its grpc dependency does not build.
- Fork branch: `mit-pdos/etcd-grove` branch `pr-etcd-21982-goose-lean` (`6a282d4fa`), the PR on the etcd pin
  `09669450f`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `compaction_delete_visibility_test.go` (package `backend_test`, `server/storage/backend/`) | After `UnsafeDeleteForCompaction` and `Unlock`, the write tx no longer sees the key but `ReadTx` and `ConcurrentReadTx` still do, until the next commit; `UnsafeDelete` is visible at `Unlock`. Passes (it asserts the PR's behaviour). | PR head (also the fork branch) | `cp compaction_delete_visibility_test.go <checkout>/server/storage/backend/ && cd <checkout>/server && GOTOOLCHAIN=go1.26.4 go test -v -run TestCompactionDeleteVisibleUntilCommit ./storage/backend/` |
| `visibility-pr-head.log` | That test's output at the PR head. | PR head | as above |
| `vet-mvcc-pr-head.log` | `go vet ./storage/mvcc/` fails at the PR head: `fakeBatchTx` in `kvstore_test.go` does not implement the new `BatchTx` method, so mvcc's tests do not compile. | PR head | `cd <checkout>/server && GOTOOLCHAIN=go1.26.4 go vet ./storage/mvcc/` |
| `check_failpoints.sh` | For each compaction gofail point the robustness suite names (`tests/robustness/failpoint/gofail.go`), whether the server still declares it. | any etcd checkout | `cd <checkout> && sh check_failpoints.sh` |
| `check_failpoints-pr-head.log`, `check_failpoints-base.log` | `compactBeforeCommitBatch` is `MISSING` at the PR head and declared at the base. | PR head, base | as above |
| `review_compaction_hash_test.go` (package `mvcc`, `server/storage/mvcc/`; the reviewer's) | The compaction's late-visible deletes do not change `HashByRev` when a key is live (the same hash during and after a compaction). With no key live, the hash differs (`issues/etcd-hash-empty-keep.md`, symptom 2: older than the PR, not caused by it). The file also adds the `fakeBatchTx.UnsafeDeleteForCompaction` the PR head lacks, so mvcc's tests compile. Do not use it on the fork branch, which already has that method. | PR head | `cp review_compaction_hash_test.go <checkout>/server/storage/mvcc/ && cd <checkout>/server && GOTOOLCHAIN=go1.26.4 go test -v -run TestReviewHashByRevDuringCompaction ./storage/mvcc/` |
| `review_compaction_hash_test.log` | Its output: `liveKey=true` the hashes are equal, `liveKey=false` they differ (FAIL). | PR head | as above |
