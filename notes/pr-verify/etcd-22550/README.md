# Files for the verification of etcd-io/etcd#22550

The report is `notes/pr-verify/etcd-22550.md`. Revisions: PR head `4dd8e296b242e700a139624d76edaa5af4b44d7d`,
upstream base `f061acd0902d489041448cdd19d71a345d27b9f5`, verified fork commit `a632fb56d`
(`mit-pdos/etcd-grove` branch `pr-etcd-22550-goose-lean`, the PR on the fork's `goose-lean` `09669450f`).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `kvstore_fastkeysonly_lease_test.go` | `TestFastKeysOnlyLeaseRestore`: 20 random histories (puts with leases 0/1/2, deletes, an optional compaction); at every uncompacted revision, the fast keys-only range (index) and the full range (backend) agree on key, revisions, version and **lease**, on the live store and after a restart (`restoreIntoIndex`, small `restoreChunkKeys`). Covers the restore path, which the proof leaves at the trust boundary. | PR head (passes), upstream base (fails: lease 0) | `cp kvstore_fastkeysonly_lease_test.go <etcd>/server/storage/mvcc/ && cd <etcd>/server && go test ./storage/mvcc/ -run TestFastKeysOnlyLeaseRestore` |
| `kvstore_fastkeysonly_lease_test.pr.log`, `kvstore_fastkeysonly_lease_test.base.log` | the two runs above (base log truncated to its first failures) | as named | as above |
| `range-keys-only-lease-tests.patch` | the tests of `issues/etcd-range-keys-only-lease.md` (fork branch `range-keys-only-lease`, commit `01e522548`): `TestRangeKeysOnlyLease` (`server/etcdserver/txn/txn_test.go`) and `TestKVGetKeysOnlyLease` (`tests/integration/clientv3/kv_test.go`), keys-only ranges for every sort target, at the current and at a past revision | PR head | `git apply range-keys-only-lease-tests.patch`, then `cd server && go test ./etcdserver/txn/ -run TestRangeKeysOnlyLease` and `cd tests && go test ./integration/clientv3/ -run TestKVGetKeysOnlyLease` |
| `range-keys-only-lease-tests.pr.log` | both pass on the PR head (they fail on the base: see the issue) | PR head | as above |
| `kvstore_review_lease_test.go` (reviewer) | `TestReviewLeaseSubRevisions`: one write txn puts a key several times with different leases and re-creates a deleted key with a new lease; keys-only reads inside the txn, after it, at the compaction revision, after a restart and after a snapshot `Restore` give the full read's lease. `TestReviewRevisionLeaseSize`: `Revision` 16 bytes, `revisionLease` 24 | PR head (passes); does not build on the base (`revisionLease`) | `cp kvstore_review_lease_test.go <etcd>/server/storage/mvcc/ && cd <etcd>/server && go test ./storage/mvcc/ -run TestReview -v` |
| `txn_review_lease_test.go` (reviewer) | `TestReviewIgnoreLeaseKeysOnly`: after an `IgnoreLease` put, and in a txn of a put then a keys-only range (both shared-buffer modes), the keys-only read returns lease 7 | PR head (passes), base (fails: `expected 7, actual 0`) | `cp txn_review_lease_test.go <etcd>/server/etcdserver/txn/ && cd <etcd>/server && go test ./etcdserver/txn/ -run TestReview` |
| `review-tests.pr.log`, `review-tests.base.log` | the reviewer's tests on the PR head and on the base | as named | as above |

Go: `GOTOOLCHAIN=go1.27.1`.
