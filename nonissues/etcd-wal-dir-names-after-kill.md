---
upstream: none
checked: 2026-11-11
links:
blocks-proof: yes
---
# etcd: a member killed during WAL creation or a segment cut, restarted, then hit by a power loss, can lose its WAL or the records of its last segment

`wal.Create` renames `<dir>.tmp` to `<dir>` and then fsyncs the parent; `cut` renames the new
segment `N.tmp` to `<seq>-<index>.wal` and then fsyncs the WAL directory. A process killed between
such a rename and its fsync leaves the new name in the page cache only. The restarted process (no
reboot) opens the WAL through that name, reads it, and appends synced records to it; nothing makes
the name durable. A power loss then reverts it: after Create's rename the WAL directory is
`<dir>.tmp` again, `wal.Exist` reports no WAL and bootstrap starts a fresh member; after a cut's
rename the last segment is `N.tmp` again, and the records synced into it since the restart (and
the cut's own) are lost: the next restart reads less than the member acknowledged. Two sites, one
cause and one fix (W4 Draft §6's K-N2 and K-N3).

**Why not an issue:** the bare fsync(2) contract (the user's U1 decision), as for
[etcd-wal-create-dir-entry-unsynced.md](etcd-wal-create-dir-entry-unsynced.md): journaled ext4/xfs
commit the rename with the restarted process's first fsync, or with the extent conversion of its
first `fdatasync` into the preallocated segment. Shown with the WAL tester (W3b,
`/shared/tmp/wal-spec/w3b/`, real code, ptrace-recorded file system): `TestKillThenPowerKN2` and
`TestKillThenPowerKN3` in [etcd-wal-dir-names-after-kill/](etcd-wal-dir-names-after-kill/) (the
tester's `kn_test.go`) are deterministic: at the fork's `71f99a4bf` the restart after the kill
acknowledges entry 1 (Create) or 6 (cut, 4 KiB segments), and the posix power-loss image has no WAL
("NOWAL") or reads entry 5; with the fix both read what was acknowledged. (The tester's ordered
model fails them too, because its journal-commit rule does not count `ZeroToEnd`'s truncate and
fallocate as metadata; real ext4 likely commits there.) The random kill-then-power-loss runs
(`-killpl 1`, 150 chains each, kill right after the rename): Create (`-killdir create`) posix
66 of 150 chains end in the "WAL vanished" panic (157 kills), ordered 0 (154); cut (`-killdir cut -target`, 4 KiB segments) posix
50 of 150 chains end in "read a state that no crash image of the history gives" (364 kills; e.g. the image keeps `N.tmp` in place of the last `.wal` segment), ordered 0 (450); at the fix (`goose-lean` b18c2d500) 0 in all four (154/154/434/449 kills).
Code: [Create's rename](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L184)
and [its parent fsync](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L224);
[cut's rename](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L843) and
[its directory fsync](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L847);
[`ReadAll`'s write-mode tail](https://github.com/etcd-io/etcd/blob/6974f522338b/server/storage/wal/wal.go#L571).
The same at upstream main (6974f522338b).

## Proof

yes: the tester's "WAL vanished" panic (Create) and "read a state no crash image gives" panic
(cut) are reachable through a kill, a restart and a power loss, so `etcd_wal_safe` (any crash) is
false at `71f99a4bf`, and `walCrash`'s `named := true` arm (W4 Draft §1.1) is false for a kill. The
fork's `goose-lean` b18c2d500 (the pin) makes `ReadAll` in write mode, after F-Z's `Fdatasync`, fsync the
WAL directory and its parent (F-N4 part 2).

## Fix

**Branch**: `fix/etcd-wal-readall-sync-dirs` in `/shared/tmp/wal-spec/w3/upstream-etcd` (not
pushed): 26f00c7f1 with `TestReadAllSyncsDirs` (functional only: the WAL stays usable with a
relative directory whose parent is "."; a failed directory sync fails `ReadAll`; durability is the
tester's `TestKillThenPowerKN2`/`KN3`). Off main, independent of F-Z's branch (both edit the same
lines of `ReadAll`: a trivial conflict).
**Base**: etcd-io/etcd@6974f522338b7dc67575080f07285e5b4348d47d

**PR draft**:

Title: wal: fsync the WAL directory and its parent in ReadAll

A process killed between Create's rename of the temporary WAL directory and the parent's fsync, or
between a cut's rename of the new segment and the WAL directory's fsync, leaves the new name in the
page cache only. The restarted process opens the WAL through it and appends synced records; a power
loss then reverts the name, and the WAL vanishes or loses its last segment's records. This PR
fsyncs the WAL directory and its parent in `ReadAll` (write mode), before anything is appended.

**If a reviewer asks**: two directory fsyncs per restart, none on the write path. The member
directory's own entry in the data directory is covered by `TouchDirAll` at every start (with F-N2
and the existing-directory fix).

## Notes

The commit needs a `Signed-off-by` before filing. Upstream was not searched again in W3b (W3's
search for the sibling findings, 2026-11-11, found nothing).
