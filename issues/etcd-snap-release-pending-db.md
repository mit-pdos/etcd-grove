---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#18055 issue open: the panic ("failed to open snapshot backend") this describes
  - etcd-io/etcd#22046 pr open: pending-apply marks in the Snapshotter (verified on branch pr-verify/etcd-22046)
  - etcd-io/etcd#21082 pr closed: an earlier fix (a reservation taken in OpenSnapshotBackend)
---

# ReleaseSnapDBs deletes a received snapshot database that is waiting to be applied

- **Status**: bug (a reachable panic), known upstream (etcd-io/etcd#18055). Recorded here while
  verifying etcd-io/etcd#22046, which fixes it.
- **Where**: `server/etcdserver/api/snap/snapshotter.go`, `(*Snapshotter).ReleaseSnapDBs` (pinned
  etcd `09669450f`), called from `server/storage/storage.go` `(*storage).Release`, which the raft
  loop runs after persisting a snapshot from the leader (`server/etcdserver/raft.go`, after
  `r.raftStorage.ApplySnapshot`). The apply loop opens the file later, in
  `server/etcdserver/server.go` `applySnapshot` → `serverstorage.OpenSnapshotBackend` →
  `ss.DBFilePath`.
- **What happens**: the receiver saves snapshot A's database as `<A>.snap.db` (`SaveDBFrom`) and
  raft hands A to the apply loop. Before the apply loop reaches `OpenSnapshotBackend(A)`, raft
  persists a newer snapshot B and `ReleaseSnapDBs(B)` deletes every `.snap.db` file with an index
  below B's, A's included. `DBFilePath(A)` then fails and `applySnapshot` panics with "failed to
  open snapshot backend". Reproduction: `notes/pr-verify/etcd-22046/snapshotter_release_pending_test.go`
  (`TestReleaseSnapDBsDeletesDBPendingApply`; fails at the pinned base, passes with #22046;
  `notes/pr-verify/etcd-22046/release-pending.log`).
- **Expected**: a received snapshot's database file stays until the snapshot has been applied.
- **How the proof handles it**: the snapshotter is names-only on `lean` (no spec of
  `ReleaseSnapDBs` or `SaveDBFrom`); the server's verified apply loop assumes raft hands it no
  snapshot (`EtcdServer.applySnapshot`'s spec, `ap.snapshot = nil`), so the snapshot path is
  outside every verified result. Branch `pr-verify/etcd-22046` specifies the PR's fix.
- **Possible fixes**: #22046's pending-apply marks (set by `SaveDBFrom`, dropped by
  `OpenSnapshotBackend`, skipped by `ReleaseSnapDBs`); #21082's reservation (taken by the apply
  path); or releasing database files only up to the last applied snapshot.
- **Found**: 2026-10-17, while verifying etcd-io/etcd#22046 (`etcd-pr-verify`).
