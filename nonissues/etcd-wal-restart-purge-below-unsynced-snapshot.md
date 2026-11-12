---
upstream: none
checked: 2026-11-06
links:
  - etcd-io/etcd#22709 issue open: related, different: ReadAll's ZeroToEnd is not fsynced (a machine crash at boot, not a process restart)
blocks-proof: no
---

# wal: a member restarted without a sync purges WAL files below a snapshot record that is only in the page cache

A member killed while syncing a new snapshot record, and restarted while the machine stays up,
opens its WAL at that record, read from the page cache, and locks only the files from the
record's file on. The WAL purge, which runs as soon as the server starts, deletes the older files
beyond `--max-wals`, including the one the previous durable snapshot record needs. A power loss
before the record reaches the disk leaves a WAL whose newest durable snapshot points into a deleted
file: the member exits at every start ("failed to open WAL") and must be removed and re-added.

**Why not an issue:** no test, found by code reading (`notes/restart-vs-crash.md`, Q5); it needs a
process restart without a sync followed by a power loss within the writeback window, and more than
`--max-wals` (default 5) WAL files written between the two snapshots, which etcd's documentation
does not exclude but no test harness here reaches.

## Execution

At upamanyus/etcd@673da07c (the pinned `goose-lean`).

1. G1 takes snapshot S (index *s*): the backend commits, then `WAL.SaveSnapshot`
   (`server/storage/wal/wal.go:1076-1098`) writes the record and is killed during its `sync`
   (`:1097`; a slow `fdatasync` is when a liveness probe kills etcd). Within one run, files are
   unlocked only by `ReleaseLockTo` (`wal.go:941-982`), called by `storage.Release`
   (`server/storage/storage.go:75-78`) after the snapshot is saved and synced
   (`server/etcdserver/server.go:1116`, `:2156`), so G1 kept the files below S locked; the previous
   durable snapshot is S₀, more than five files before S.
2. G2 starts on the page cache: `recoverSnapshot` (`server/etcdserver/bootstrap.go:449-506`)
   takes the newest record `wal.ValidSnapshotEntries` sees (`wal.go:645-670`), S, and
   `openAtIndex` (`wal.go:369-406`) locks only the files from S's on (`selectWALFiles`,
   `:408-424`; `openWALFiles`, `:426-440`). The purge loop (`server.go:538`, `:607-613`;
   `client/pkg/fileutil/purge.go:44-110`, `:66-76`) deletes the oldest files it can lock while
   more than `--max-wals` remain, including S₀'s. The unlinks reach the journal within seconds.
3. Power loss before S's record is synced or written back (an idle member).
4. G3 on the disk: the newest durable snapshot record is S₀ (or none, if its record was in a
   deleted file); `selectWALFiles` finds no file at or below its index (`wal.go:414-417`), and
   `openWALFromSnapshot` exits with "failed to open WAL" (`bootstrap.go:677`).

Under machine crashes alone it cannot happen: files below a snapshot are unlocked only after its
record is synced. After a fleet-wide restart and then a rack power loss, several members can be
in this state, and the cluster needs a restore from backup.

## Proof

no: the Linux file extension assumes a restart follows a machine restart or a `sync(2)` of what
the old process left (`GooseLang/Ext/Fs/Impl.lean`, header "Restarts"), so a process restart is a
machine crash and every generation boots on a durable state; this execution is outside the
theorem, by that stated assumption.

## Fix

The note's proposal (`notes/restart-vs-crash.md`, Q7 and conclusion 4): `fdatasync` the WAL tail
(and `fsync` the WAL directory and its parent) at the end of `ReadAll`, or in
`openWALFromSnapshot` (`bootstrap.go:668`), before raft and the purge loop start. The snapshot
record is in the tail file (only the tail holds unsynced data: `cut` syncs the old tail before it
switches, `wal.go:829-833`), so that one sync makes it durable before anything below it is
unlocked. The same sync closes `nonissues/etcd-wal-restart-acks-unsynced-entries.md`.
