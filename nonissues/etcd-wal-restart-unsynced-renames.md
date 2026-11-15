---
upstream: none
checked: 2026-11-06
links:
blocks-proof: no
---

# wal: a member restarted between a WAL rename and its directory fsync builds on a name that is not durable (strict POSIX only)

`cut` renames `N.tmp` to the next segment's name and then `fsync`s the WAL directory; `Create`
renames `member/wal.tmp` to `member/wal` and then `fsync`s `member/`. A member killed between the
rename and the `fsync`, and restarted while the machine stays up, finds the new name, appends,
`fdatasync`s and acknowledges entries in that file, and syncs the directory only at its own next
`cut`, 64 MB later. Under POSIX's directory semantics (a file's `fdatasync` makes no name
durable), a power loss then keeps the old name: the WAL ends at the previous segment (acknowledged
entries and the saved term and vote lost), or `member/wal` is missing and the member bootstraps a
fresh log, forgetting what it voted and acknowledged.

**Why not an issue:** harmless on the file systems etcd runs on: on ext4 (`data=ordered`) and xfs
the rename is journaled before the restarted process's writes, the journal commits in order, and
its first `fdatasync` (or the 5 s periodic commit) commits the rename with it. Found by code reading
(`notes/restart-vs-crash.md`, Q3 and Q4); it needs a process restart without a sync followed by a
power loss, and a file system with POSIX's weakest directory ordering.

## Execution

At upamanyus/etcd@673da07c (the pinned `goose-lean`).

- `cut` (`server/storage/wal/wal.go:822-904`): the new file's header is synced (`:866`), then
  `os.Rename` (`:875`) and `fileutil.Fsync(w.dirFile)` (`:879`). Killed between `:875` and `:879`,
  the restarted member's `readWALNames` (through the dentry cache) sees the renamed segment, opens
  it as the tail (`openAtIndex`, `wal.go:369-406`) and writes into it; the restart syncs no
  directory. After a power loss the file is `N.tmp` again, which `readWALNames` ignores
  (`checkWALNames`, `server/storage/wal/util.go:72-99`).
- `Create` (`wal.go:102-241`): `renameWAL` (`:185`, `os.Rename` at `:306`) and then the parent's
  `fileutil.Fsync(pdir)` (`:225`). Killed between them, the restarted member sees `member/wal`
  (`wal.Exist`, `server/etcdserver/bootstrap.go:77`) and restarts from it; its own `cut`s `fsync`
  the WAL directory, never `member/`. After a power loss `member/wal` is missing, `Create`
  removes the stale `wal.tmp` (`wal.go:113-117`) and a fresh log is bootstrapped.

Under machine crashes alone neither can happen: the restarted member sees the old names (and the
old tail was synced and truncated by `cut`, `wal.go:829-833`).

## Proof

no: the Linux file extension assumes a restart follows a machine restart or a `sync(2)` of what
the old process left (`GooseLang/Ext/Fs/Impl.lean`, header "Restarts"), so a process restart is a
machine crash and every generation boots on a durable state; this execution is outside the
theorem, by that stated assumption. (The model's directories are POSIX's: a file's `fsync`
commits no name, so without the assumption the theorem would be false here.)

## Fix

The note's proposal (`notes/restart-vs-crash.md`, Q7 and conclusion 4): at boot, `fsync` the WAL
directory and its parent (with the `fdatasync` of the tail that
`nonissues/etcd-wal-restart-acks-unsynced-entries.md` proposes), before raft starts.
