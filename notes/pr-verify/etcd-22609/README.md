# Files for `notes/pr-verify/etcd-22609.md`

Go tests for etcd-io/etcd#22609 (`mvcc: fix data race between Hash and Restore`). Each goes in
`server/storage/mvcc/` of an etcd checkout and runs from `server/`.

| File | Shows | Revision | Command | Result |
|---|---|---|---|---|
| `kvstore_hash_put_race_test.go` | `TestHashConcurrentWithPut`: before the PR, `hash` reads `currentRev` without `revMu`, racing with every write transaction's `End` (no `Restore` needed); `issues/etcd-mvcc-hash-currentrev-unlocked.md` | upstream base `b25719d10`; PR head `afd94a12c` | `cp kvstore_hash_put_race_test.go <etcd>/server/storage/mvcc/ && cd <etcd>/server && go test -race -count=5 -run '^TestHashConcurrentWithPut$' ./storage/mvcc/` | base: `WARNING: DATA RACE` (write `storeTxnWrite.End` kvstore_txn.go:214, read `store.hash`), FAIL; PR head: passes, 50 runs of 50 |
| `kvstore_hash_restore_rev_test.go` | `TestHashRevisionDuringRestore` (the reviewer's): with the PR, a `Restore` between `hash`'s `s.mu.RUnlock()` and its read of `currentRev` makes `hash` return the old backend's hash with `Restore`'s transient revision 1 (or the new store's) | PR head `afd94a12c` | `cp kvstore_hash_restore_rev_test.go <etcd>/server/storage/mvcc/ && cd <etcd>/server && go test -race -count=3 -run '^TestHashRevisionDuringRestore$' ./storage/mvcc/` | PR head: `hash of the old backend (at revision 11) returned with revision 1; store now at 21`, FAIL (3 of 3); with `currentRev` read under `revMu` before `s.mu.RUnlock()`: passes |

The PR's own test, `TestHashConcurrentWithRestore`, passes on the fork branch
`pr-etcd-22609-goose-lean` (`dd7ab1507`) with `go test -race ./storage/mvcc/`.
