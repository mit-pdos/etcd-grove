---
upstream: none
checked: 2026-11-11
links:
blocks-proof: yes
---
# etcd: a power loss after a new member's first writes can lose its data directory, and the member restarts as a fresh one

`fileutil.TouchDirAll` creates missing directories with `os.MkdirAll` and never fsyncs their
parents. Bootstrap creates the data and member directories this way, and `wal.Create` its
temporary directory; the WAL then fsyncs its files, which makes their data durable but not the
directory entries that lead to them. After a power loss the data or member directory can be
missing, `wal.Exist` reports no WAL, and bootstrap starts a fresh member that has forgotten what it
acknowledged.

**Why not an issue:** no test in etcd's own harness, as for
[etcd-wal-create-dir-entry-unsynced.md](etcd-wal-create-dir-entry-unsynced.md) (the bare fsync(2)
contract; journaled ext4/xfs commit the `mkdir`s with the first `fdatasync` of the resized WAL
file). Shown with the WAL crash spec's harness (W0 `TestCP3FirstStart`; W3 `TestW3FN` in
[etcd-fileutil-touchdirall-parent-unsynced/](etcd-fileutil-touchdirall-parent-unsynced/), real code):
from an empty root, 131 of 899 posix images at the fork's `a4d2bb172` lose an acknowledged `Save`
(W0's classification of the same run: data directory missing 77, member directory missing 37, WAL
directory empty 17); at `71f99a4bf`, 0 of 1023. Code:
[`TouchDirAll`](https://github.com/etcd-io/etcd/blob/6974f522338b/client/pkg/fileutil/fileutil.go#L49), its calls in
[`bootstrap`](https://github.com/etcd-io/etcd/blob/6974f522338b/server/etcdserver/bootstrap.go#L64). The same at upstream main (6974f522338b).

## Proof

yes: as for `Create`'s entry, under the bare fsync(2) contract. The fork's `goose-lean-walsync`
71f99a4bf (`etc/goose.py`) fsyncs the parent of each directory `TouchDirAll` creates.

## Fix

**Branch**: `fix/etcd-fileutil-touchdirall-parent-unsynced` in
`/shared/tmp/wal-spec/w3/upstream-etcd` (not pushed): 34fe32fb3 fix with `TestTouchDirAllNested`
(functional only: each level created, relative paths; durability is the harness's `TestW3FN`)
**Base**: etcd-io/etcd@6974f522338b7dc67575080f07285e5b4348d47d

**PR draft**:

Title: fileutil: TouchDirAll fsyncs the parent of each directory it creates

`TouchDirAll` ([fileutil.go](https://github.com/etcd-io/etcd/blob/6974f522338b/client/pkg/fileutil/fileutil.go#L59)) creates the data, member and
temporary WAL directories with `os.MkdirAll`, and nothing syncs their parents. fsync(2) of a file
does not make the directory entries leading to it durable, so after a power loss the WAL that etcd
had acknowledged writes from can be unreachable, and the member bootstraps as a new one. This PR
fsyncs the parent of each directory `TouchDirAll` creates.

**If a reviewer asks**: `os.MkdirAll` is kept (its error handling for an existing non-directory);
the missing levels are listed before it, and their parents synced after it.

## Notes

The commit needs a `Signed-off-by` before filing.
