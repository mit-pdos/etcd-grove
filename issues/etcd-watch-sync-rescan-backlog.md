---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22264 issue open: this bug (syncWatchers rescans [minRev, curRev] every pass but delivers at most watchBatchMaxRevs revisions; apply loop stalls on watchableStore.mu)
  - etcd-io/etcd#22265 pr open: fix, bound the scan to deliverable revisions
  - etcd-io/etcd#22304 pr open: fix, bound the scan to watchBatchMaxRevs
  - etcd-io/etcd#22594 pr open: fix, bound the backend scan by entry count
  - etcd-io/etcd#16839 issue open: related (watch starvation and OOM from lagging watchers)
  - etcd-io/etcd#18109 issue closed: related (slow watchers raise PUT latency)
---

# `syncWatchers` re-reads a lagging watcher's whole backlog on every pass while holding `s.mu`

- **Status**: bug (performance: quadratic backend reads in a watcher's lag, with
  `watchableStore.mu` held throughout, so writes stall). Not a wrong result.
- **Where**: `server/storage/mvcc/watchable_store.go` at the etcd pin of `etc/goose.py`
  (`107edf7e4`): `syncWatchers` (`:347-416`, which holds `s.mu`, `:349-350`, and calls
  `rangeEvents(..., minRev, curRev+1, ...)`, `:366`), `rangeEvents` (`:419-439`, a full
  `UnsafeRange` of the window with no limit, `:432`), and `watcher_group.go`'s `eventBatch.add`
  (`:39-62`, which caps a batch at `watchBatchMaxRevs = 1000` revisions and records `moreRev`).
- **What happens**: a watcher `N` revisions behind is caught up 1000 revisions per pass, and each
  pass reads every revision from its `minRev` to the current revision. Recovery reads about
  `N²/2000` revisions. The reporter's unit test (in #22264, run at `main` `ee043b3`, the same code
  as the pin) reads 210,001 revisions to deliver 20,000, and in production a backlog of 500,000
  revisions held the lock for about 1.3 s per 100 ms tick.
- **Expected**: a bounded scan per pass. The apply path should not be blocked for times that grow
  with a watcher's lag.
- **How the proof handles it**: the specs admit it, and in fact state the full read.
  `mvcc.rangeEvents.spec` (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/rangeEvents.lean:32-53`)
  returns every event of `[minRev, maxRev)`, and `syncWatchers.spec` describes the capped delivery
  exactly. The model has no notion of cost (class C-perf; `notes/bug-triage/etcd-22264.md`,
  proposal `watch-sync-bounded-scan`).
- **Possible fixes**: the open PRs above (bound `maxRev`, or limit the `UnsafeRange` by entry count
  and resume from the last key read).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#22264.
