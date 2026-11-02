---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#17331 issue closed: related, not this bug (ConcurrentReadTx's stale-cache path copies the buffer redundantly; closed not planned)
  - etcd-io/etcd#12933 pr merged: introduced the read-buffer cache and bufVersion (v3.5); origin of the behavior
blocks-proof: no
---

# backend: after a commit, ConcurrentReadTx reuses a read-buffer copy from before it

`ConcurrentReadTx` caches its copy of the read buffer, keyed by a version that only a write-back
increments; a commit empties the buffer without changing the version, so the next
`ConcurrentReadTx` lays the pre-commit buffer over the post-commit bbolt transaction: a range over
the `Key` bucket returns a key twice, a key deleted by the commit comes back, a key a pre-commit hook
overwrote reads its old value.

**Why not an issue:** a precondition etcd's only caller meets: mvcc's `store.Read` reads its
`ConcurrentReadTx` one revision key at a time from the `Key` bucket (never a range, never `Meta`,
where the hook writes), and revision keys are never overwritten, while compaction commits before any
reader can cache a revision it deletes; no wrong mvcc or API result exists (2000-trial mvcc tests,
2026-10-23). The backend breaks its own comment ("guaranteed to be up-to-date") only for a caller
etcd does not have.

## Proof

no: the backend's contract promises no range read of a `ConcurrentReadTx` and excludes the hook's
buckets (`keyReadSnap` with `rng = false`, `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean`),
which is what mvcc uses; no fork fix.

## Notes

`TestConcurrentReadTxAfterCommit` in
[`nonissues/etcd-backend-read-buffer-cache-stale-after-commit/concurrent_read_after_commit_test.go`](etcd-backend-read-buffer-cache-stale-after-commit/concurrent_read_after_commit_test.go)
(copied as `zz_concurrent_read_after_commit_test.go` into `server/storage/backend`) fails at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (go1.27.3): `expected: []string{"abc"}`,
`actual  : []string{"abc", "abc"}` (`after commit`). A one-line hardening fix (increment `bufVersion`
in `readTx.reset`) is on `fix/etcd-backend-read-buffer-cache-stale-after-commit` (upamanyus/etcd,
pushed: d426dcdb9 test, 1714a913c fix, off 22cc5d9ac); it becomes an issue if a caller that
range-reads `Key` through `ConcurrentReadTx` is added.
