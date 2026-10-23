---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#18055 issue open: this bug (robustness test; root cause by ahrtr, "lock the snapshot file until it has been applied")
  - etcd-io/etcd#20133 issue closed: duplicate (Antithesis, main 3be967f, default configuration)
  - etcd-io/etcd#20657 issue closed: duplicate (3.5.18, two snapshots at index 17 and 18)
  - etcd-io/etcd#21082 pr closed: an earlier fix attempt, unmerged
  - etcd-io/etcd#22046 pr open: keep snapshot db files until they have been applied, with a test
---

# A second snapshot's `Release` can delete the `.snap.db` file `applySnapshot` is about to open

- **Status**: a bug by code reading, reproduced only at the unit level (the fork's regression test,
  "Fixed in the fork" below, delays the apply goroutine by holding `bemu`; not reproduced in a
  cluster): a race between the raft goroutine and the
  apply goroutine that ends in `lg.Panic("failed to open snapshot backend")` on a follower. It
  needs two snapshots handed out by raft in quick succession (a second `MsgSnap` of a higher index
  already stepped while the first batch is processed, e.g. from a new leader) and the apply
  goroutine delayed for the few fsyncs of the second round inside a window of a few statements.
  Rare; found while designing the proof's invariant on the snapshot directory.
- **Where** (the etcd fork's `goose-lean` at `de825d8c6`, where this was found; the same code at the pin of `etc/goose.py`, `2aed163b1`):
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
- **Fixed in the fork** (2026-10-22, `goose-lean` `188113160`, the pin of `etc/goose.py`): the
  raft goroutine no longer calls `Release`; `applySnapshot` calls `s.r.storage.Release(toApply.snapshot)`
  (the WAL and the `.snap.db` files below the snapshot) right after `s.bemu.Unlock()`, once
  `OpenSnapshotBackend` has renamed the snapshot's own file (the `raftAfterWALRelease` failpoint moves
  with it). The WAL is still fsynced before `Release` (the raft goroutine's `Sync` precedes the
  `notifyc` that `applySnapshot` waits on, etcd-io/etcd#10219); its locks are released a little later.
  Regression test `TestSnapshotDBKeptUntilOpened` (`server/etcdserver/server_test.go`, deterministic:
  a fake raft node hands out snapshots 2 and 4 while the test holds `bemu`, so `applySnapshot(2)` waits
  before its open; the test waits until the raft goroutine has appended the second batch's entry,
  past where it released, and checks `<2>.snap.db` is still there): fails 5 of 5 without the fix,
  passes 10 of 10 with it (`-race`).
- **Upstream** (from the search of branch `bug-triage`, 2026-10-16, which filed the same bug as
  `issues/etcd-snapshot-db-released-before-apply.md`): known, etcd-io/etcd#18055, open, reproduced
  upstream by the robustness tests and Antithesis (two closed duplicates); the fix PR #22046 keeps
  the snapshot's `.snap.db` files until they have been applied. Our fork's fix above is another
  form of the same idea; supporting #22046 is the useful step, not a new report.
- **Found**: 2026-10-20, stage S-j2 of track T-S, stating the removal fact `Rm` of the snapshot
  directory for `applySnapshot`'s precondition.
