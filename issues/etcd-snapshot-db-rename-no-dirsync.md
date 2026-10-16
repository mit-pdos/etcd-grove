---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22498 issue open: this finding (the reporter's reproduction simulates the lost rename with hard links)
  - etcd-io/etcd#22499 pr open: fsync the snap directory after the rename in OpenSnapshotBackend
  - etcd-io/etcd#22518 pr open: the same fix, an alternative PR
  - etcd-io/etcd#22340 issue closed: related, not this bug: the same missing directory fsync at the receive-side rename (SaveDBFrom); fixed by #22314 (e9e56564d, in the pin)
  - etcd-io/etcd#18055 issue open: related, not this bug (the same OpenSnapshotBackend path panics when a newer snapshot's Release has already deleted the db; issues/etcd-snapshot-db-released-before-apply.md)
---

# `OpenSnapshotBackend` adopts a snapshot db by an unsynced rename; a crash can leave the old db with the snapshot's consistent index

- **Status**: a bug (silent data loss on one member after a power loss), present at the etcd
  pin. Found by the triage of etcd-io/etcd#22498 (`notes/bug-triage/etcd-22498.md`), not by a
  proof.
- **Where**: etcd pin `107edf7e4` (`etc/goose.py`): `storage.OpenSnapshotBackend`
  (`server/storage/backend.go:63-71`; the rename at `:68`, with no `fileutil.Fsync` of
  `member/snap` after it). Its caller is `EtcdServer.applySnapshot` (`server/etcdserver/server.go:1001`;
  `OpenSnapshotBackend` at `:1048`, `consistIndex.SetBackend(newbe)` at `:1060`, the old backend's
  `Close` in a goroutine at `:1095`). The shared pre-commit hook is
  `BackendHooks.OnPreCommitUnsafe` → `consistentIndex.UnsafeSave` (`server/storage/hooks.go:45-46`).
  On restart, `RecoverSnapshotBackend` (`server/storage/backend.go:106-117`) is reached through
  `bootstrap` → `recoverSnapshot` (`server/etcdserver/bootstrap.go:437,465`).
- **What happens**: a follower installs a leader snapshot at index `i`. The rename of
  `<i>.snap.db` to `db` is in the page cache only. `SetBackend(newbe)` makes the consistent
  index reload as `i`. The old backend's final commit (its `Close`) runs the shared hook, which
  saves `i` into the **old** db file, and bolt fsyncs that file. A power loss before the directory
  entry reaches the disk leaves `member/snap/db` naming the old file. Its stored consistent index
  is `i`, but its data is the pre-snapshot state. On restart `RecoverSnapshotBackend` sees
  `i ≤ consistent_index` and keeps the old db ("Skipping snapshot backend"). The member then
  serves and applies on top of a state missing the snapshot's writes, with no error.
  Reproduction: the issue's (a 3-member cluster; `ln db db.old-inode` before the follower restarts
  and installs the snapshot; after "closed old backend file", kill it and restore the old inode as
  `db`). No Go test here: the step that matters is a lost directory operation at a crash.
- **Expected**: adopting the snapshot db is durable before anything can persist the snapshot's
  index. Equivalently, a restart never pairs a db file with a consistent index whose effects it
  does not contain (the invariant `RecoverSnapshotBackend`'s comment states).
- **How the proof handles it**: not reached. `applySnapshot.spec` covers only `ap.snapshot = nil`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`). The premise comes
  from the raft wrapper's `rnApP` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRaftNode.lean:682`),
  backed by `ownRawNode`'s `snap = none` (`notes/STATUS.md`, stage S item 2).
  `OpenSnapshotBackend` is names-only (`Code/go_etcd_io/etcd/server/v3/storage.lean:93`). Crashes
  and file-system durability are out of scope (`notes/STATUS.md`, "Out of scope for now"). The
  apply protocol (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApply.lean`) ties the consistent
  index to a single backend, and the backend swap is not one of its steps.
- **Possible fixes**: fsync `member/snap` after the rename in `OpenSnapshotBackend` (PRs #22499,
  #22518). Additionally, or instead, the old backend's final commit should not save the new
  backend's consistent index: retire the hook for the old backend before `SetBackend`, or close
  the old backend without the pre-commit hook.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#22498 (batch `bug-triage/2026-10-16`).
