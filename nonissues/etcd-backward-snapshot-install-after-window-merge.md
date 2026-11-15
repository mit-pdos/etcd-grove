---
upstream: none
checked: 2026-11-15
links: []
blocks-proof: no
---

# etcdserver: a member can install a snapshot older than its backend, so its revision goes back until it re-applies

A restarted leader that is still replaying its WAL (its backend's consistent index ahead of its applied
index) merges a follower's snapshot at its applied index with its whole backend, whose consistent index is
higher. The follower installs it: its raft log is at the snapshot's index, its backend ahead of it. If
another leader then sends that follower a snapshot at an index between the follower's raft commit and its
backend's consistent index, raft accepts it (the index is above the commit) and `applySnapshot` accepts it
(the index is above `ep.appliedi`), and the follower's backend is replaced by the older image. The member
then re-applies the entries between the two indices. Until it has, its store's current revision is lower
than before, so two serializable reads on that member can see the revision go back.

**Expected:** nothing etcd documents is violated: serializable reads may be stale, and the re-applied
entries rebuild the same state.

**Impact:** none known. A linearizable read is not affected: its read index is the leader's commit, which
covers the newer state once any read has seen it, so the member applies past it first. A watcher is not
affected: `watchableStore.Restore` marks the synced watchers `restore`, so a watcher whose next revision is
above the restored current revision is not a panic (`watcher_group.go:244-254`) and is moved back to synced
with its `minRev`, which filters the re-applied events (`watchable_store.go:381-395`). Reaching it needs a
restarted leader elected inside its replay window and a second leader that is lagging in applying.

**Cause:** `createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState)` stamps the merged
snapshot with the applied index and streams `s.be.Snapshot()`, the whole backend
(`server/etcdserver/snapshot_merge.go`); inside the replay window the backend's consistent index is above
`ep.appliedi` (`bootstrap.go` restores it from the backend). `applySnapshot` checks only `Index >
ep.appliedi` (`server/etcdserver/server.go:1046`) and opens the snapshot's database unconditionally
(`:1068`). At the etcd fork pin `2eaeb872bc`; the run was found by the review of the Q16-3 design
(`notes/decisions.md`, "R2s: snapshots across windows", F1).

**Why not an issue:** found by code reading, no test; behavior etcd does not guarantee against (serializable
reads only), and etcd's own watch code anticipates a restore below a watcher's revision.

## Proof

It blocks a design, not a property: R2s-A's plan to follow such a merged snapshot in the ghost
(`notes/restart3-a0-draft.md` §2.2) cannot follow the backward install, because the server's KV store
invariant keeps the store's log as a monotone list whose floors are persistent (`KVStoreApi.lean:114-120`,
probe P1). The recommended variant A-g changes the goose fork so that a leader defers a merged snapshot
while it is inside its replay window (`notes/restart3-a0-draft.md` §3), which makes the install always
forward; until then no proof covers a restarted member's in-window merge (the restart triple's premise
`srvWinPend` excludes it, and no closed theorem carries that premise).
