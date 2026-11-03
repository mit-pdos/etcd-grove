---
upstream: none
checked: 2026-11-02
links:
blocks-proof: yes
---
# etcd: a member's own disk snapshot saved after a received one makes the restart open the WAL at the older snapshot

Two goroutines write the WAL's snapshot records with nothing ordering them: the raft loop saves a
received snapshot `k` (`raftNode.start`: `SaveSnap`, `Save` of its hard state, then
`ApplySnapshot`; server/etcdserver/raft.go), and the apply thread saves its own snapshot of its
applied index `i` (`EtcdServer.snapshot`: `CreateSnapshot(i)` then `storage.SaveSnap`;
server/etcdserver/server.go), which `applyAll` runs once raft has advanced past its batch, while
the raft loop may already be handling the next `Ready`. `storage.SaveSnap` takes only a read lock.
`CreateSnapshot`'s `ErrSnapOutOfDate` check covers only a `CreateSnapshot` after the loop's
`ApplySnapshot(k)`. So the WAL can hold `snapshot(k)`, the hard state at commit `k`, then
`snapshot(i)` with `i < k`. At restart `recoverSnapshot` (server/etcdserver/bootstrap.go) takes
the *last* snapshot record at or below the saved commit, not the highest: `ReadAll` starts at `i`,
ignores the record at `k`, and returns the log above `i` the member had before the received
snapshot, with the commit index `k`. If that log ends below `k`, raft's restart panics (the commit
index out of range); otherwise the restarted log holds, as committed, entries the snapshot
discarded.

**Why not an issue:** found by code reading (the restart plan's R2b-1 review, 2026-11-02); no test
reaches the interleaving yet. Since `.snap` files are no longer written or loaded (upstream
`5d1a827c1`, in the fork's history), `recoverSnapshot` builds the snapshot from the last WAL record;
the old `LoadNewestAvailable` picked the newest by index. Upstream not searched (no GitHub access
from the session).

**The fork's fix** (branch `goose-lean-walsnap`, with
`nonissues/etcd-wal-stale-entries-above-snapshot.md`'s): `recoverSnapshot` opens the WAL at the
valid snapshot record of the highest index, so that a later record of a lower index is ignored.

## Proof

yes: the image of a stopped member (`srvDiskImage`) says the WAL's records hold the node's durable
state; with the records opened at the older snapshot they do not. The WAL's model
(`etcdserver/InvWal.lean`'s `walSaveSnap`) describes the fixed choice: a snapshot record below the
records' base leaves them unchanged.
