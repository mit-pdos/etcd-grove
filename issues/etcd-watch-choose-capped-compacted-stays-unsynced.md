---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22294 issue open: same bug, reported by the PR's author
  - etcd-io/etcd#22295 pr open: the fix (choose deletes from the source group the watchers chooseAll retired); verified in notes/pr-verify/etcd-22295.md on branch pr-verify/etcd-22295
---

# server/storage/mvcc: a compacted watcher stays in the unsynced group when `choose` is capped

- **Status**: bug (wrong result: a retired watcher is left registered and is sent its compaction
  response again on every resync).
- **Where**: `server/storage/mvcc/watcher_group.go` at 09669450f (`etc/goose.py`'s etcd pin),
  `watcherGroup.choose` (`watcher_group.go:226-239`) and `watcherGroup.chooseAll`
  (`watcher_group.go:241-271`); the caller `watchableStore.syncWatchers`
  (`watchable_store.go:347`, the call at line 365, the skip at line 371).
- **What happens**: when the unsynced group has at least `maxWatchers` members, `choose` copies
  `maxWatchers` of them into a fresh group `ret` and runs `ret.chooseAll`. `chooseAll` retires a
  member whose `minRev` is below `compactRev` (it sends `WatchResponse{CompactRevision:
  compactRev}`, sets `w.compacted = true` and calls `wg.delete(w)`, line 259) - but its `wg` is
  `ret`, so the watcher is removed from the copy only. `syncWatchers` iterates the returned group,
  which no longer has it, so it never calls `s.unsynced.delete(w)` either. The watcher stays in
  `s.unsynced` for good (until the client cancels it), every later resync chooses it again and
  sends another compaction response for the same watch id, and `s.unsynced.size()` (the value
  `syncWatchers` returns, the resync loop's pacing input, and `slowWatcherGauge`) counts it. The
  uncapped branch (`len(wg.watchers) < maxWatchers`) runs `chooseAll` on `wg` itself and is
  correct. Reproduction: the PR's test `TestWatchCompactedWatcherRemovedFromUnsyncedWhenCapped`
  (`notes/pr-verify/etcd-22295/watchable_store_test.go` on branch `pr-verify/etcd-22295`) fails at
  09669450f with "compacted watchers should be removed from the unsynced group: expected 0, actual
  2", and passes with the PR applied.
- **Expected**: `syncWatchers`' own comment (`watchable_store.go:344`: "iterate over the set to
  get the minimum revision and remove compacted watchers") and `cancelWatcher`'s `wa.compacted`
  case (line 174), which counts a compacted watcher as in no group: a compacted watcher is
  retired from the unsynced group once its compaction response is sent.
- **How the proof handles it**: out of scope by premise. `chooseAll`'s and `choose`'s specs
  (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/watcherGroup__chooseAll.lean`,
  `watcherGroup__choose.lean`) require that no member is below `compactRev`, and the watchable
  store is verified as frozen (`compactMainRev = -1`, `notes/decisions.md`, "The watchable store's
  concurrency (unit 3)" and the compaction section), so the compaction branch never runs in a
  verified result. On `pr-verify/etcd-22295` the compaction-aware spec
  `mvcc.watcherGroup.choose.specC` (relative to an abstract statement of what `chooseAll` retires)
  is proved of the PR's code; it is false of the pinned code.
- **Possible fixes**: the PR's: record the members moved into `ret` and, after `ret.chooseAll`,
  delete from `wg` each one that is no longer in `ret`. Alternatively `chooseAll` could take the
  source group to delete from.
- **Found**: 2026-10-17, verifying etcd-io/etcd#22295 (`.claude/skills/etcd-pr-verify`); the
  existing proofs did not find it because of the premise above.
