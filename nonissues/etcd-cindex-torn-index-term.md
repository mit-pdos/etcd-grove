---
upstream: none
checked: 2026-11-27
links:
  - etcd-io/etcd#22028 issue open: related, not this: a backend consistent index above the WAL's commit
blocks-proof: yes
---
# etcdserver: a backend commit can save the consistent index with the term of another index

The consistent index and its term are two separate atomics. The apply loop sets them outside the
backend's batch lock (after an entry whose apply takes no write transaction, such as the empty entry
a new leader appends at the start of its term), while the backend's periodic commit loads them one
after the other and saves them. A commit between the two stores saves a pair no entry has: the new
index with the previous index's term, or the previous index with the new term. A crash before the
next commit keeps it on disk.

**Why not an issue:** no wrong result upstream. Upstream reads the stored term only to detect a
v3.5 schema (`term != 0`) and in `ETCD_VERIFY`'s `validateConsistentIndex`, and a running member
overwrites the pair at its next commit. The tests reach the torn pair through `EtcdServer.apply` and
the backend's commit loop (and at the `cindex` API), not through a client.

**Tests** (in [`etcd-cindex-torn-index-term/`](etcd-cindex-torn-index-term/)), copied into etcd-io/etcd@4e090c033
(`main`, 2026-11-24), go1.27.4:

- `TestEmptyEntrySavesConsistentIndexWithItsTerm` (`server/etcdserver`): applies empty entries, each
  the first of a new term (term = index), through `EtcdServer.apply` (`applyEntryNormal`'s deferred
  set, `server/etcdserver/server.go:1947`), while another writer keeps the backend's commit loop
  committing; a wrapper of `BackendHooks` reads back, in the commit's transaction, the pair the
  pre-commit hook saved. Both directions, 3 of 3 runs:

  ```
  $ go test ./server/etcdserver -run TestEmptyEntrySavesConsistentIndexWithItsTerm
      cindex_term_boundary_test.go:103: the backend saved consistent index 712950 with term 712949
  FAIL
      cindex_term_boundary_test.go:103: the backend saved consistent index 230476 with term 230477
  FAIL
  ```

- `TestConsistentIndexSavesTermOfIndex` (`server/etcdserver/cindex`): the two calls alone, a writer
  setting `(i, i)` and `UnsafeSave` under the batch lock. Fails within 10 saves (3 of 3 runs):
  `saved consistent index 22444 with term 22443`.

**Cause:** `consistentIndex.SetConsistentIndex` stores `consistentIndex` then `term` with two
`atomic.StoreUint64`s, and `UnsafeSave` loads them with two `atomic.LoadUint64`s
(`server/etcdserver/cindex/cindex.go:112-121`). `UnsafeSave` runs under the batch lock
(`OnPreCommitUnsafe`), but two of `SetConsistentIndex`'s callers do not hold it:
`applyEntryNormal`'s deferred set (`server.go:1947`) and a refused conf change (`server.go:2013`).
The post-lock hook's set does hold it.

## Proof

yes: the keep-guard replacement (the boot step of the fork branch `keepfix-d/2026-11-27`,
`~/coordinator-notes/plans/keepfix-d-design.md`) labels the restart's raft snapshot with the stored term
(too low: the member stalls; too high: it overstates its last term in elections), and our fork's merged
snapshot already labels a snapshot above the applied index with it (`snapshot_merge.go`). The fix, one
mutex for the pair in `SetConsistentIndex` and `UnsafeSave`, is on that branch (both tests pass there,
the server-level one over about 29,000 commits). The proofs at the current pin do not read the term.

## Notes

Raft's term for the stored index is otherwise exact: every set takes the entry's own `(Index,
Term)`, and a backend installed from a leader snapshot carries the leader's pair.
