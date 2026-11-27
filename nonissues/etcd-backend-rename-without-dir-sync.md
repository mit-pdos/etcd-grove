---
upstream: none
checked: 2026-11-24
links:
blocks-proof: yes
---

# etcd renames a database file onto the backend path without syncing the directory

Two places replace `member/snap/db` by a rename and never sync `member/snap` afterwards (etcd fork
`bc2b5f4d0`, as upstream):

- `storage.OpenSnapshotBackend` (`server/storage/backend.go:68`): `os.Rename(snapPath, cfg.BackendPath())`
  of a received snapshot's `.snap.db`, then `OpenBackend` (bbolt's `Open` `fdatasync`s the file, not the
  directory). Reachable in `etcd_safe`: a member far behind receives a snapshot.
- defrag (`server/storage/backend/backend.go:588`): `os.Rename(tdbp, dbp)` of the defragmented copy, then
  `bolt.Open`. Not reachable in `etcd_safe` (no workload calls `Defragment`).

A power loss before the next commit of the journal can undo the rename: `member/snap/db` names the old
database again (the pre-defrag file, or the pre-install backend), while later backend commits went to the
new inode. In the file extension's model a name becomes durable only with a directory sync of any directory
(`DirSync` commits every logged operation); the WAL's next `cut` syncs its directory, after which the rename
is durable. On ext4 the rename is journaled and committed within the commit interval (5 s by default), or
by an `fsync` that forces a journal commit; a file's `fdatasync` after the rename need not.

**Why not an issue:** found by code reading, no test; fixed in the fork (below). Whether it breaks etcd's safety is not shown:
after the loss the member restarts from an older backend (a lower consistent index), and raft replays or
the leader resends the entries above it, as for a backend behind the WAL; the snapshot install's case may
need the WAL's snapshot record (`SaveSnap`, synced before the install) to be above the old backend's index,
which `bootstrap`'s `recoverSnapshot` handles by reopening the `.snap.db` if it still exists (it was
renamed away, then the rename lost: it exists again). A test with the configuration-C harness
(`examples/osfs/semantics`) would decide it.

## Proof

yes: C-I1 (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`) gives the file at `path`
only when its name is durable (`dbSyncs γ path`); the snapshot install's rename makes no such fact until the
WAL's next directory sync, so the member's crash law (T7) must handle a backend file that is the old one
(a fork change, `syncDir` after both renames, would remove the window; the owner decides).

## Fix (fork)

`upamanyus/etcd` branch `goose-lean-crashfixes` (`71295dd6d`, 2026-11-24): both renames are followed by a sync
of the parent directory (`syncParentDir` in `backend.go`, `syncDir` in `storage/backend.go`; test
`TestSyncParentDir`; `go test ./storage/ ./storage/backend/ ./etcdserver/` pass). The branch stacks the WAL
torn-`Save` fix (`768ecf158`) and the applySnapshot guard (`8aa40fd5c`) on the pin `bc2b5f4d0`: the one pin
`etcd_safe` needs (not yet `etc/goose.py`'s). With it, C-I1's durable-name fact holds right after each rename.
