---
upstream: none
checked: 2026-11-15
links: []
blocks-proof: no
---

# etcdserver: a member that installs a snapshot older than its backend can panic on a catching-up watcher

A member can install a snapshot whose database is older than its current backend. The mvcc store is
then restored to the lower revision. `watchableStore.Restore` marks only the *synced* watchers
`restore`. A watcher that is still catching up (unsynced), or that is a victim moved back to unsynced, and
whose next revision is above the restored revision, makes the next `syncWatchers` panic in
`watcherGroup.chooseAll` ("watcher minimum revision … should not exceed current revision …"), which kills
the member. The store's revision also goes backward until the member re-applies the skipped entries, so
two serializable reads on that member can see the revision decrease, and a progress notification can
report a revision below events already sent.

**Expected:** installing a snapshot should never panic the member. `chooseAll`'s own comment expects a
watcher above the current revision only after a restore, and `Restore` should mark every watcher it can
leave above the restored revision (the unsynced and victim ones too), or keep the newer backend.

**Impact:** a member must install an image below its backend's consistent index. Two ways reach it, both
found by reading the code:
- **A restarted leader's in-window merge, then another leader's snapshot.** A restarted leader that is
  still replaying its WAL merges a follower's snapshot at its applied index with its whole backend, whose
  consistent index is higher. The follower's raft log is then at the snapshot's index while its backend is
  ahead. Another leader that is lagging in applying can then send it a snapshot at an index between the
  two, which raft accepts (above its commit) and `applySnapshot` accepts (above `ep.appliedi`).
- **A crash.** The raft loop hands a batch to apply before it saves the batch's HardState, so after a
  machine crash the backend's consistent index can be above the WAL's commit; a snapshot between the two
  is then accepted.
In either case a watch must be catching up at that member at that moment (a watch opened with an old
start revision, or a slow one). Linearizable reads are not affected: a read's index is the leader's
commit, so the member applies past the newer state first.

**Reproduction (internal API):** `TestZZBackwardRestoreUnsyncedWatcher` in
[`etcd-backward-snapshot-install-panics-watcher/backward_restore_test.go`](etcd-backward-snapshot-install-panics-watcher/backward_restore_test.go),
copied into `server/storage/mvcc` at the etcd fork pin `2eaeb872bc`, go1.27:

```
zz_backward_restore_test.go:40: restored: current revision 3
zz_backward_restore_test.go:43: syncWatchers panicked after a backward restore: watcher minimum revision 5 should not exceed current revision 3
--- FAIL: TestZZBackwardRestoreUnsyncedWatcher (0.04s)
```

**Cause:** `createMergedSnapshotMessage(m, ep.appliedt, ep.appliedi, ep.confState)` stamps the merged
snapshot with the applied index and streams the whole backend (`server/etcdserver/snapshot_merge.go:34-50`).
`applySnapshot` checks only `Index > ep.appliedi` (`server/etcdserver/server.go:1046`) and opens the
snapshot's database unconditionally (`:1068`). `watchableStore.Restore` sets `restore` only on
`s.synced.watchers` (`server/storage/mvcc/watchable_store.go:215-218`); `chooseAll` panics on any other
watcher above the current revision (`watcher_group.go:244-250`). The first run was found by the review of
the Q16-3 design (`notes/decisions.md`, "R2s: snapshots across windows", F1).

**Why not an issue:** the test calls `Restore` with an older backend directly; no test yet reaches the
backward install through etcd's own paths (a forced in-window leader plus a lagging second leader, or a
crash between apply and the HardState save). Writing that integration test would move this to `issues/`.

## Proof

No top-level result covers it: the closed theorems' restarts are graceful, and the restart triple's
premise `srvWinPend` excludes a restarted member's in-window merge (no closed theorem carries it). It blocks
R2s-A's recorded design (`notes/restart3-a0-draft.md` §2.2): the server's KV store invariant keeps the
store's log as a monotone list with persistent floors (`KVStoreApi.lean:114-120`, probe P1), and its floor
read law is false of Go under a backward install. Variant A-g (§3 there, a fork guard deferring a merged
snapshot inside the sender's replay window) removes the first cause for graceful restarts; the crash cause
remains for a crash-model restart theorem.
