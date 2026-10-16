---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22294 issue open: this bug
  - etcd-io/etcd#22295 pr open: fix of #22294 (`choose` deletes from the source group the watchers `chooseAll` retired)
  - etcd-io/etcd#21174 pr closed: an earlier fix of the same bug (unmerged)
  - etcd-io/etcd#21189 pr closed: related (`choose` always copies, `chooseAll` no longer deletes while iterating; unmerged)
  - etcd-io/etcd#17529 issue closed: related, not this bug (a compaction response that could not be sent; fixed by #17555, whose skip in `syncWatchers` is at the pin)
---

# mvcc: with at least `maxWatchersPerSync` unsynced watchers, a watcher canceled as compacted stays unsynced and is sent `CompactRevision` again on every resync

- **Status**: a bug (a watcher retired by compaction is never removed from the unsynced group: a
  repeated compaction response, a leaked unsynced watcher, a wrong `syncWatchers` result and
  `slowWatcherGauge`). Present at the pin. Reproduced by a Go test.
- **Where** (etcd pin `107edf7e4`, `server/storage/mvcc/`): `watcherGroup.choose`
  (`watcher_group.go:226-239`): with `len(wg.watchers) >= maxWatchers` it copies up to
  `maxWatchers` members into a fresh group `ret` and calls `ret.chooseAll`; `chooseAll`
  (`watcher_group.go:241-270`): a member with `minRev < compactRev` is sent `WatchResponse{CompactRevision}`,
  marked `compacted` and removed by `wg.delete(w)` (line 259), from `ret` only.
  `watchableStore.syncWatchers` (`watchable_store.go:347-416`) calls
  `s.unsynced.choose(maxWatchersPerSync, ...)` (line 365) and then iterates the returned group, so
  it never reaches `s.unsynced.delete(w)` (lines 382, 405) for that watcher. `maxWatchersPerSync`
  is 512 (`watchable_store.go:41`).
- **What happens**: when at least `maxWatchersPerSync` watchers are unsynced at once (a busy
  member after a compaction, after `Restore`, which moves every synced watcher to unsynced) and one
  of the chosen is below the compaction revision, that watcher gets its compaction response and
  stays in `s.unsynced`. Every later resync (each `watchResyncPeriod`, 100 ms) can choose it again
  and send another `CompactRevision` response on the stream, until the client cancels the watch
  (`cancelWatcher` finds it in `s.unsynced`). `syncWatchers` returns, and `slowWatcherGauge`
  reports, a count that includes it. No event is lost or duplicated. With fewer unsynced watchers
  `choose` returns the group itself and the delete works. Reproduction:
  `issues/etcd-watch-choose-capped-compacted/watch_choose_capped_compacted_test.go` (package `mvcc`,
  dropped into `server/storage/mvcc/`; from `server/`: `GOTOOLCHAIN=go1.27.1 go test
  ./storage/mvcc/ -run TestWatchChooseCompactedWatcherRetired -count=1 -v`). Two watchers from
  revision 1 after a compaction at 5, three `syncWatchers` calls: with `maxWatchersPerSync = 2`
  (capped) it fails at the pin on every run (10 of 10) with `unsynced watchers after resyncs: 2;
  CompactRevision responses per watch ID: map[0:3 1:3]`; with `maxWatchersPerSync = 3` (uncapped)
  it passes (`0`, `map[0:1 1:1]`).
- **Expected**: a watcher canceled as compacted gets one compaction response and leaves the
  watchable store's groups, whatever the number of unsynced watchers (as in the uncapped branch).
- **How the proof handles it**: outside the verified scope. `choose` and `chooseAll` are verified
  (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Link.lean:443`) only under the premise that no
  member is below `compactRev`
  (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/watcherGroup__choose.lean:33-35`,
  `watcherGroup__chooseAll.lean:32-34`), which the store discharges because the watch path is
  proved for a store that is never compacted (`crevFrozen`,
  `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/InvStore.lean:1254`). So `chooseAll`'s compaction
  branch, where the delete goes to the wrong group, is dead code in the model. The proposal
  `watch-under-compaction` (`notes/bug-triage/etcd-18089.md`, `etcd-17529.md`) would make it live;
  with `chooseAll.spec` stating that a compacted member is either sent the response and removed from
  the group or kept unchanged, `choose`'s capped branch would have to remove it from `wg` too, and
  the proof would fail on the pinned code.
- **Possible fixes**: in `choose`'s capped branch, delete from `wg` the chosen watchers that
  `chooseAll` retired (#22295: remember the chosen ones, check `w.compacted`); or let `chooseAll`
  only report the compacted watchers and have `syncWatchers` delete them from `s.unsynced`.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#17529 (and its group, etcd-io/etcd#15220),
  reading `choose`'s capped branch against `watch-under-compaction`; upstream as etcd-io/etcd#22294.
