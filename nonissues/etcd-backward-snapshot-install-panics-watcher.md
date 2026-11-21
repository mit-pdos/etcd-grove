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

**Why not an issue:** the backward install was not reached through etcd's own paths (D-A0-3's attempt,
2026-11-15). Half of it was: `TestZZBackwardInstallWatcherPanic` in
[`inwindow_merge_test.go`](etcd-backward-snapshot-install-panics-watcher/inwindow_merge_test.go) (five members,
graceful stops and restarts only, timing steered by gofail sleeps and `CutPeer`, built with `gofail enable` at
`2eaeb872bc`) makes a restarted leader merge a snapshot inside its replay window, and the follower installs
it with its raft log at the snapshot's index and its backend ahead: run of 2026-11-15, `applied snapshot
… "incoming-leader-snapshot-index": 217`, `restored mvcc store {"consistent-index": 467}`, after which the
follower re-applies 218..467 v2-only and serves all 455 keys. The second half needs a second leader whose
backend is below 467 and whose merge passes the fork's term guard (`m.Term == raftTerm`): its handed-out
batches of the new term must start below 467, so it must win an election knowing a commit below 467. With
the full log it learns the commit from any leader; so it must win with a log the first leader's term
entries never reached, from an electorate disjoint from a majority that holds them: not possible with the
first leader's term entries committed, and avoiding their replication needs the first leader elected and
then cut off before its first append (a gofail delay on the leader's send, about seven members, est. 2-4 d).
On upstream etcd (no term guard) the second leader merges at any batch end, which is easier; that was not
tried (the hold). **The crash path** reaches the receiver state more directly (a backend above the WAL's
commit after a power loss, then any normal leader's snapshot between the two), not tried either. The panic
itself is shown only by calling `Restore` with an older backend.

## Proof

No top-level result covers it: the closed theorems' restarts are graceful, and the restart triple's
premise `srvWinPend` excludes a restarted member's in-window merge (no closed theorem carries it). It blocks
R2s-A's recorded design (`notes/restart3-a0-draft.md` §2.2): the server's KV store invariant keeps the
store's log as a monotone list with persistent floors (`KVStoreApi.lean:114-120`, probe P1), and its floor
read law is false of Go under a backward install. Variant A-g (§3 there, a fork guard deferring a merged
snapshot inside the sender's replay window) removes the first cause for graceful restarts; the crash cause
remains for a crash-model restart theorem.

The former replay deferral has a separate sender regression that checks the delivered database and its Raft metadata for both current and legacy backends, including a recovered HardState commit below the consistent index. [Sender replay issue](../issues/etcd-merged-snapshot-replay-failure.md).
