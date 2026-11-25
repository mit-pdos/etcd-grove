---
upstream: none
checked: 2026-11-25
links: []
blocks-proof: no
---

# etcd: a `.snap.db` removed by `Release` before `SaveDBFrom` syncs its directory can reappear after a crash

`Snapshotter.SaveDBFrom` (rafthttp's snapshot handler goroutine, `http.go:279`) links the received file at
`<index>.snap.db` and then syncs the snapshot directory (`snap/db.go:39-85`). `storage.Release` (the apply
goroutine: `applySnapshot`, `server.go:1114`, and `snapshot()`, `server.go:2155`) runs concurrently and
`ReleaseSnapDBs` removes every `.snap.db` below the released snapshot's index (`snapshotter.go:45-75`). A
stale `MsgSnap` (an index below the member's latest snapshot, e.g. a leader's old snapshot delivered after the
follower caught up by log and snapshotted itself) can have its file linked, then removed by `Release`, before
`SaveDBFrom`'s directory sync; if the machine crashes before any later sync of the directory, neither the link
nor the removal is on disk, or the link is and the removal is not, and the stale file is back after restart.

**Why not an issue:** not a bug: the file left is an orphan below the WAL's snapshot index, which nothing
reads (`OpenSnapshotBackend` opens the file of the WAL's snapshot index) and the next `Release` removes again.
No test: found by code reading while specifying the snapshot directory's crash law (D6-T6, P7).

## Proof

no: the snapshot directory's invariant (`snapDirInv`, `Proof/.../rafthttp/Net.lean`) accounts for it: a
removed index joins the saved set with its `Rm`, so a file a crash brings back at it is covered by `Rm`, as
any file at a released index is (`ReleaseSnapDBs.spec`, `storage.Release.spec`; coordinator decision on #50,
2026-11-25).
