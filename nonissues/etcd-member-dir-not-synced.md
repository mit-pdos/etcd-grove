---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: yes
---

# etcd: the member directory is never made durable, so a crash can lose a member's whole data

`bootstrap` creates the data directory and `member/` with `fileutil.TouchDirAll`
(`server/etcdserver/bootstrap.go:64,68`), which is `os.MkdirAll` followed by writing and
removing a `.touch` file (`client/pkg/v3/fileutil/fileutil.go:36-68`): it never fsyncs a
directory. The only fsync of a directory that holds `member/`'s entries is `wal.Create`'s fsync
of `member/` itself (`server/storage/wal/wal.go:202,225`), which makes `member/wal` and
`member/snap` durable inside `member/` but not `member/` inside the data directory. Nothing else
in the server syncs the data directory (the other directory fsyncs are the WAL directory's, at a
segment cut, `wal.go:879`, and `Snapshotter.SaveDBFrom`'s of `member/snap`, `snap/db.go:126-131`).

Under POSIX as written, where a new directory entry is durable only after an fsync of the
directory holding it, a power loss at any time after a first boot may drop `member/` and with it
the WAL, the backend and the snapshots, though every write was acknowledged after an fsync of the
WAL. The restart then finds no WAL (`wal.Exist` is false) and boots the member as a new one: a
single-member cluster started with `--initial-cluster-state=new` silently starts an empty cluster,
and a member of a larger cluster fails to start ("member has already been bootstrapped").

**Why not an issue:** behavior etcd does not observe in practice: on journaled ext4
(`data=ordered`, the default) and xfs, an fsync of a file commits the journal transaction holding
the earlier `mkdir`s of the directories on its path, so the WAL's first fsync makes `member/`
durable. Found by code reading (`notes/specs-only/verify/F2-crash.md`, N3), no test: it needs a
crash simulation that drops unsynced directory entries.

## Proof

yes, pending a decision (`notes/specs-only/open-questions.md`, D7): the WAL's trusted crash laws
(`Wal.walRecs_crash`, `walWriting_crash`, `walCreating_crash`, `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/wal/Api.lean`)
and so every `EtcdServer.disk_crash` rely on `member/`'s entry being durable, which is true on
ext4/xfs and not under POSIX as written; the fork fix of D7's option (c) (sync `member/snap`) does
not cover it, an environment premise that a directory entry on the path of a file is durable once
that file is fsynced (D7's option (a), stated for directory entries generally) does.

## Notes

The same holds of the WAL's first segment file: it is created in `member/wal.tmp`, whose entries are
never fsynced before the rename, and `member/wal` itself is fsynced only at the first segment cut
(`wal.go:879`), so under POSIX `member/wal` may come back without its `.wal` file (which `wal.Exist`
also reads as no WAL). A fix in etcd: `fileutil.Fsync` of each directory `TouchDirAll` creates, and
of its parent, after creating it (and of the WAL directory after `wal.Create`'s rename), as
`wal.Create` already does for `member/`.
