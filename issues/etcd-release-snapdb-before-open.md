---
upstream: unchecked
---

# A second snapshot's `Release` can delete the `.snap.db` file `applySnapshot` is about to open

- **Status**: a bug by code reading, **not reproduced**: a race between the raft goroutine and the
  apply goroutine that ends in `lg.Panic("failed to open snapshot backend")` on a follower. It
  needs two snapshots handed out by raft in quick succession (a second `MsgSnap` of a higher index
  already stepped while the first batch is processed, e.g. from a new leader) and the apply
  goroutine delayed for the few fsyncs of the second round inside a window of a few statements.
  Rare; found while designing the proof's invariant on the snapshot directory.
- **Where** (the etcd pin of `etc/goose.py`, `de825d8c6`):
  - `server/etcdserver/raft.go:271-291` (`raftNode.start`, a batch with a snapshot): after
    `storage.Sync()`, `notifyc <- struct{}{}` (`:279`, the "snapshot persisted" signal), then
    `raftStorage.ApplySnapshot` and `r.storage.Release(raftSnap)` (`:286`); the second
    `notifyc` send (`:309` or `:334`, cap 1) waits only until `applySnapshot` has taken the first;
    then `Advance` and the next `Ready`.
  - `server/storage/storage.go:75-82` (`Release`) -> `snap/snapshotter.go:45-72`
    (`ReleaseSnapDBs`): removes every `<index>.snap.db` with `index` below the released snapshot's.
  - `server/etcdserver/server.go:1049-1063` (`applySnapshot`): `<-toApply.notifyc`, `s.bemu.Lock()`,
    then `serverstorage.OpenSnapshotBackend` (`storage/backend.go:63-72`): `DBFilePath(index)`
    errors if the file does not exist (`snap/db.go:98-115`), and `os.Rename` of it; either error is
    `lg.Panic`.
  - `server/etcdserver/server.go:839-841`: the run loop takes each `toApply` from `applyc` at once
    and schedules `applyAll` on the FIFO scheduler, so the raft goroutine is not held by the apply.
- **What happens**: batch `i` (snapshot `i`) reaches the apply goroutine; `applySnapshot(i)` takes
  the first `notifyc` token, which unblocks the raft goroutine's second send; the raft goroutine
  advances and, if raft already holds a newer snapshot `i' > i` (raft steps incoming messages while
  the driver processes a `Ready`), hands out batch `i'`: `SaveSnap`, `Save`, `Sync`, the
  (non-blocking, fresh channel) `notifyc`, `ApplySnapshot`, `Release(i')`, which deletes
  `<i>.snap.db`. If `applySnapshot(i)` has not yet renamed that file (it may be waiting on `bemu`,
  descheduled, or in GC), `DBFilePath(i)` fails and the member panics; on restart it recovers from
  the WAL and the newer snapshot file. A reproduction would build etcd with gofail and put a sleep
  at the existing failpoint `applyBeforeOpenSnapshot` (`server.go:1060`) while a new leader sends a
  second snapshot; not attempted.
- **Expected**: the file of a snapshot handed to the apply loop stays until the apply loop has
  opened it; a member catching up by two snapshots in a row does not crash.
- **How the proof handles it**: not reached (no member installs a snapshot; `applySnapshot`'s spec
  covers only the empty snapshot). The snapshot directory's invariant (`snapDirInv`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Net.lean:122`) lets only removals with
  a fact `Rm i`, and stage S-j's design needs `Rm` to exclude the index being applied; with the
  code as is, no `Rm` that `Release(i')` can establish for `i < i'` refutes "the apply goroutine has
  not opened `i` yet" (`notes/decisions.md`, "D22 S-j2 carried out", "For S-j1").
- **Possible fixes**: release the snapshot files only up to the apply loop's applied index (e.g.
  `Release` from the apply goroutine after `applySnapshot`, or `ReleaseSnapDBs` given the applied
  snapshot's index), or have the raft goroutine wait for `applySnapshot`'s open (a second signal)
  before `Release`.
- **Found**: 2026-10-20, stage S-j2 of track T-S, stating the removal fact `Rm` of the snapshot
  directory for `applySnapshot`'s precondition.
