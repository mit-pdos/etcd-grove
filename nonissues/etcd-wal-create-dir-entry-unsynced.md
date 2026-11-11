---
upstream: none
checked: 2026-11-11
links:
blocks-proof: yes
---
# etcd: a power loss after a new member's first writes can leave its WAL directory empty, and the member restarts as a fresh one

`wal.Create` writes the first WAL file into `<dir>.tmp`, renames the directory to `<dir>` and
fsyncs the parent; it never fsyncs `<dir>.tmp` itself. fsync(2) of the parent makes the new name
durable but not the entries of the renamed directory, so after a power loss the WAL directory can
exist without its first file, even after writes the WAL acknowledged as synced. `wal.Exist` then
reports no WAL and bootstrap starts a fresh member, which has forgotten its log, hard state and
votes.

**Why not an issue:** no test in etcd's own harness: it needs a model of directory-entry
durability under the bare fsync(2) contract (POSIX; ext4 and xfs in their default journal modes
order the create before the file's first `fdatasync` and do not lose it). Shown with the WAL crash
spec's ptrace record-and-replay harness (W0 `TestCP3FirstStart`; W3 `TestW3FN` in
[etcd-fileutil-touchdirall-parent-unsynced/](etcd-fileutil-touchdirall-parent-unsynced/), against
the real code): with the data and member directories made durable beforehand (this file's case
alone), 66 of 868 posix images at the fork's `a4d2bb172` lose an acknowledged `Save` (in W0's run of
the same case, all with an empty WAL directory); at `71f99a4bf`, 0 of 899 (0 under kill -9 and
journal ordering either way). Code: [`Create`](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L101),
[`renameWAL`](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L305). The same at upstream main (6974f522338b).

## Proof

yes: the WAL's crash spec takes the bare fsync(2) contract (the user's choice U1, 2026-11-11), under
which `Create` cannot give a WAL that survives a crash without the fix. The fork's
`goose-lean-walsync` 161796636 (`etc/goose.py`) fsyncs `<dir>.tmp` before the rename.

## Fix

**Branch**: `fix/etcd-wal-create-dir-entry-unsynced` in `/shared/tmp/wal-spec/w3/upstream-etcd`
(not pushed): ddfb2aa07 fix (no in-tree test; the regression test is the harness's `TestW3FN`)
**Base**: etcd-io/etcd@6974f522338b7dc67575080f07285e5b4348d47d

**PR draft**:

Title: wal: fsync the temporary WAL directory before renaming it in Create

`Create` fsyncs the parent after renaming `<dir>.tmp` to `<dir>`
([wal.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L184)), which makes the new name durable but not the first
WAL file's entry inside the renamed directory. On a file system that does not order directory
operations (the POSIX fsync(2) contract), a power loss after `Create` returned can leave an empty
WAL directory, and the member bootstraps as a new one. This PR fsyncs `<dir>.tmp` before the
rename.

## Notes

The second half of the same symptom is
[etcd-fileutil-touchdirall-parent-unsynced.md](etcd-fileutil-touchdirall-parent-unsynced.md) (the
data and member directories themselves). The commit needs a `Signed-off-by` before filing.
