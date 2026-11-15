---
upstream: none
checked: 2026-11-11
links:
blocks-proof: yes
---
# etcd: a member killed while creating its data directory, restarted, then hit by a power loss, can lose the directory and restart as a fresh member

`fileutil.TouchDirAll` returns early when the directory exists. With the fsync of a new directory's
parent added by [etcd-fileutil-touchdirall-parent-unsynced.md](etcd-fileutil-touchdirall-parent-unsynced.md)
(F-N2), a process killed between the `mkdir` and that fsync leaves the entry in the page cache
only. The restarted process (no reboot) finds the directory, skips the fsync, creates the WAL inside
it and acknowledges writes; a power loss then removes the directory with the WAL, `wal.Exist`
reports no WAL, and bootstrap starts a fresh member that has forgotten what it acknowledged.
Bootstrap calls `TouchDirAll` on the data and member directories at every start
([bootstrap.go](https://github.com/etcd-io/etcd/blob/6974f522338b/server/etcdserver/bootstrap.go#L64)),
so the fix covers restarts as well as the first start.

**Why not an issue:** as for F-N2, the bare fsync(2) contract (the user's U1 decision): journaled
ext4/xfs commit the `mkdir` with the restarted process's first fsync. Upstream does not fsync a new
directory's parent at all (F-N2), so the window is the fork's. Shown with the WAL tester (W3b,
`/shared/tmp/wal-spec/w3b/`, real code, ptrace-recorded file system): `TestKillThenPowerKN1` in
[etcd-fileutil-touchdirall-existing-after-kill/](etcd-fileutil-touchdirall-existing-after-kill/)
(the tester's `kn_test.go`) is deterministic: at the fork's `71f99a4bf` the restart after the kill
acknowledges entry 1 and the posix power-loss image has no WAL ("NOWAL"); with the fix it reads
entry 1. The random kill-then-power-loss runs (`-killpl 1 -killdir mkdir`, 150 chains, kill right
after `mkdir data` or `mkdir member` in the first start): posix 72 of 150 chains end in the "WAL vanished" panic (166 kills: 78 after `mkdir data` or `mkdir member` in the violating chains, 39 each); ordered 0 of 150 (153 kills)
(the journal commits the `mkdir` with the next fsync); at the fix (`goose-lean` b18c2d500) 0 and 0 (156 and 152 kills).
Code: [`TouchDirAll`](https://github.com/etcd-io/etcd/blob/6974f522338b/client/pkg/fileutil/fileutil.go#L53).

## Proof

yes: the tester's "WAL vanished after wal.Create returned" panic is reachable through a kill, a
restart and a power loss, so `etcd_wal_safe` (any crash) is false at `71f99a4bf`, and
`TouchDirAll`'s `dirDurable` post (W4 Draft §1.4) is false for a kill. The fork's
`goose-lean` 055b2f69a (pinned at b18c2d500) fsyncs the parent when the directory exists (F-N4 part 1).

## Fix

**Branch**: `fix/etcd-fileutil-touchdirall-existing-parent-unsynced` in
`/shared/tmp/wal-spec/w3/upstream-etcd` (not pushed): c44be4f1f with `TestTouchDirAllExisting`
(functional only: absolute and relative paths, a missing parent is an error; durability is the
tester's `TestKillThenPowerKN1`), stacked on F-N2's branch `fix/etcd-fileutil-touchdirall-parent-unsynced`
(34fe32fb3), which it extends.
**Base**: etcd-io/etcd@6974f522338b7dc67575080f07285e5b4348d47d (through 34fe32fb3)

**PR draft** (with F-N2's, or after it):

Title: fileutil: TouchDirAll fsyncs the parent of an existing directory too

`TouchDirAll` returns early when the directory exists. A process killed after creating it, before
syncing its parent, leaves the directory's entry in the page cache only: the restarted process
finds it, skips the sync, and creates the WAL inside it. A power loss then removes the directory
with the WAL. This PR fsyncs the parent in the existing-directory case too.

**If a reviewer asks**: only the immediate parent: bootstrap calls `TouchDirAll` level by level
(data, then member), so each call syncs the entry the next level hangs from. A nested chain created
by one `MkdirAll` and killed before its syncs is covered for its last level only; syncing every
ancestor up to the root would cover it, at the cost of an fsync per level at every start.

## Notes

The commit needs a `Signed-off-by` before filing. Upstream was not searched again in W3b (W3's
search for the sibling findings, 2026-11-11, found nothing).
