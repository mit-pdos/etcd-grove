---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: yes
---

# etcd: a crash that loses the first boot's backend file after a local snapshot makes the restart panic

A first boot creates `member/snap/db` through `bolt.Open` (`O_CREATE`) and never syncs the
directory `member/snap` afterwards (`nonissues/bbolt-create-dir-not-synced.md`): `fileutil.TouchDirAll`
(`server/etcdserver/bootstrap.go:211`) creates the directory before the file exists, a local
snapshot (`EtcdServer.snapshot`, `storage.SaveSnap`, `server/storage/storage.go:59-70`) writes only
the WAL's snapshot record, and the only sync of that directory is
`Snapshotter.SaveDBFrom`'s (`snap/db.go:61,76`), which runs only for a snapshot received from the
leader. Under POSIX as written (and OsFs's crash model, D4), a crash may then drop the file's name
while the WAL keeps its fsynced snapshot record at index `k > 0`.

The restart then panics instead of recovering from the WAL: `recoverSnapshot`
(`bootstrap.go:449-482`) opens the WAL's newest valid snapshot record `k`; the backend is absent, so
`beExist` is false and its consistent index is taken as `0 < k`; `RecoverSnapshotBackend` calls
`OpenSnapshotBackend`, whose `DBFilePath(k)` finds no `k.snap.db` (a local snapshot makes none), and
`cfg.Logger.Panic("failed to recover v3 backend from snapshot")` fires. The member cannot restart
until an operator intervenes. Before the first local snapshot the restart replays the WAL from
index `0`, as `bbolt-create-dir-not-synced.md` says; after it, it does not.

**Why not an issue:** on the file systems etcd is deployed on, journaled ext4 (`data=ordered`) and
xfs, the first `fdatasync` of a newly created file commits the directory entry that created it, so
the name survives with the first commit (`bolt.Open`'s `init` syncs before `Open` returns), and the
crash above does not happen. Found by code reading (the second crash pass of the specs-only branch,
`notes/specs-only/verify/repair5-crash.md`, G-a), no test: it needs a crash simulation that drops
unsynced directory entries.

## Proof

yes, pending a decision: the specs now state the file's possible loss (4a's `Backend.beOpenUpd` puts
`none` in the revert list of a file it creates, so `beFile_crash` and `beCrash` may give no file),
which makes 2e's `disk_crash` unrealizable for a member's files after a local snapshot (no restartable
`diskState` exists: `bootstrap` panics). Options (`repair5-crash.md`, New decisions): an environment
premise that a created file's name is durable at its first sync (the ext4/xfs fact; OsFs's crash
rule would need that variant, and 4c's `BoltSt.named` would become true at `Open`'s `init` sync,
which revisits the A11 F1 decision); a scope restriction (no crash before the backend's directory is
synced: in practice almost every crash of a member that never received a snapshot); or a fork fix
(sync `member/snap` after `OpenBackend` creates the file).

## Notes

A fix in etcd: `fileutil.Fsync` of `cfg.SnapDir()` after `OpenBackend` creates the file (the
`beExist == false` path of `bootstrapBackend`), as the WAL does for its directory in `wal.Create`.
