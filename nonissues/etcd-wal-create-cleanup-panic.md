---
upstream: none
checked: 2026-11-13
links:
  - etcd-io/etcd#10689 pr merged: related (added cleanupWAL with its panics)
  - etcd-io/etcd#21766 pr merged: related, different (closes files on Open's and Create's error paths)
blocks-proof: yes
---

# wal: Create panics when the cleanup of a failed creation fails

When `wal.Create` fails after renaming the new WAL directory into place (opening, fsyncing or closing
its parent directory fails), it runs `cleanupWAL`, which closes the WAL and renames the directory to
`<dir>.broken.<timestamp>`; if that close or rename fails, it calls `lg.Panic` instead of returning
an error ([wal.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/wal.go#L279-L293),
called at [wal.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/storage/wal/wal.go#L194-L199)).

**Why not an issue:** no worse outcome for etcd: its only caller, `bootstrapNewWAL`, panics on any
error of `Create` ([bootstrap.go](https://github.com/etcd-io/etcd/blob/1b969e26a2c6/server/etcdserver/bootstrap.go#L716-L719)),
and the WAL left in place is complete (synced before the rename). Reaching it also needs two failures
in a row (the parent directory, then the close or the rename). `TestCreateFailsAfterRenameWithoutPanic`
in [etcd-wal-create-cleanup-panic/](etcd-wal-create-cleanup-panic/) (a write-only parent directory,
so the parent cannot be opened after the rename; a 240-byte WAL name, so the `.broken` name is too
long) panics at upstream main `1b969e26a2c6` (2026-11-12) with `failed to rename WAL during cleanup`.
At the fork's pin `0b50f0426` that injection stops earlier (the fork's `TouchDirAll` fsyncs the parent
when it creates `<dir>.tmp`), and only a failed fsync or close of the parent reaches the cleanup;
`TestCleanupWALRenameFails` (same file, calling `cleanupWAL` on a created WAL with the long name)
panics there.

## Proof

yes: the WAL's `Create` over `fsExt`, where the parent's open, fsync and close may fail, needs the fix
to be panic-free: on the fork's local branch `goose-lean-walfs` (not pushed), `f15d88841` (on
`0fa9710dc`, on the pin `0b50f0426`): `cleanupWAL` logs and returns the error of its close or rename,
and `Create` returns it (wrapping the parent directory's error); both tests pass. `Create`'s error arm
then covers a WAL left at its name (`notes/wal-fsext-plan.md`, §0 item 5, Q4, Q5).

## Notes

Upstream not searched beyond "cleanupWAL".
