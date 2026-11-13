---
upstream: known
checked: 2026-11-03
links:
  - etcd-io/etcd#22184 issue open: this bug (lazureykis, 2026-07-23); claims the apply loop can wedge through `createMergedSnapshotMessage`'s `Commit`, which at `main` runs on the apply loop itself
  - etcd-io/etcd#22185 pr open: the fix of #22184 (the revision read under `revMu` in `progressIfSync`)
  - etcd-io/etcd#21871 pr closed: an earlier fix (the revision read before taking `watchableStore.mu`), not merged
blocks-proof: no
---

# mvcc: a progress request takes the two store locks in the wrong order, deadlocking with a write transaction's End and a waiting Commit

`progressIfSync` (behind `WatchStream.RequestProgress` and `RequestProgressAll`) holds
`watchableStore.mu` and then reads the revision through `store.Read`, taking `store.mu`, the order
`watchableStore.mu`'s comment forbids. A write transaction holds `store.mu` (shared) until its `End`,
which takes `watchableStore.mu`; with a third goroutine waiting for `store.mu` exclusively (`Commit`,
`Compact`, `Restore`), Go's `RWMutex` blocks the progress request's shared lock behind it, and the
three wait on each other forever.

**Why not an issue:** a precondition etcd meets: the server takes `store.mu` exclusively only on its
apply loop (`Commit` in `snapshot` and `createMergedSnapshotMessage`, both run by `applyAll`,
[server.go#L978-L999](https://github.com/etcd-io/etcd/blob/4b0b745025716b893c64dbee443e3f969931a16b/server/etcdserver/server.go#L978-L999);
`Compact` and `Restore` in the apply), which also runs every write transaction, so none waits while a
write is open. Only an embedder of mvcc that commits or compacts concurrently with writes and
progress requests can hang.

## Proof

no: a hang, not a panic or a wrong result; the specs are partial correctness and
`WatchStream.RequestProgress.contract` says nothing of termination
(`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`).

## Notes

`TestProgressCommitEndDeadlock` in
[`nonissues/etcd-mvcc-progress-lock-order-deadlock/progress_commit_end_deadlock_test.go`](etcd-mvcc-progress-lock-order-deadlock/progress_commit_end_deadlock_test.go)
(copied as `zz_progress_commit_end_deadlock_test.go` into `server/storage/mvcc`; #22184's test is
the same) fails 3 of 3 at etcd-io/etcd@4b0b745025716b893c64dbee443e3f969931a16b (2026-11-03,
go1.27.3):

```
$ (cd server && go test ./storage/mvcc -run '^TestProgressCommitEndDeadlock$' -count=1)
--- FAIL: TestProgressCommitEndDeadlock (3.22s)
    zz_progress_commit_end_deadlock_test.go:51: the write transaction's End did not return: RequestProgress, Commit and End wait on each other
FAIL
```

#22185's fix (read `currentRev` under `revMu`, as `watch` does) is cheap and restores the documented
order; worth a comment on #22184 that its path through `createMergedSnapshotMessage` is on the apply
loop at `main`, so etcd's server does not reach it.
