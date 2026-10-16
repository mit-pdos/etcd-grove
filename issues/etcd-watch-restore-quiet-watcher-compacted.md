---
upstream: none
checked: 2026-10-16
links:
  - etcd-io/etcd#15271 issue closed: same root (a synced watcher's stale `minRev` read after `Restore`); its fix #15492 advances `minRev` only for watchers that get events
  - etcd-io/etcd#15439 pr closed: an earlier attempt at #15271 ("update minRev when watcher stays synced")
  - etcd-io/etcd#19487 issue closed: another `Restore` bug of the same path (future watchers' `minRev` lowered)
  - etcd-io/etcd#22294 issue open: different bug in the same branch (`chooseAll`'s compaction cancel in the capped `choose`)
  - etcd-io/etcd#13822 issue closed: related (a watch on a member that rejoined after compaction); withdrawn by the reporter as a jetcd bug; there the compacted cancel is legitimate
---

# After a snapshot restore, an up-to-date watcher of a quiet range is canceled as compacted

- **Status**: bug (a spurious `ErrCompacted`: a watcher that missed no event is canceled with
  `CompactRevision`). Reproduced at the pin by a Go test.
- **Where**: `server/storage/mvcc/` at the etcd pin of `etc/goose.py` (`107edf7e4`; the same
  code as upstream `main` `b25719d10`): `watchableStore.notify` (`watchable_store.go:470-494`:
  `w.minRev = rev + 1` only for the watchers `newWatcherBatch` selects, those with events of
  `rev`), `watchableStore.Restore` (`:207-221`: every synced watcher to `unsynced`, `minRev`
  untouched), `watcherGroup.chooseAll` (`watcher_group.go:255-263`: `w.minRev < compactRev` →
  a `CompactRevision` response and the watcher dropped), reached from `syncWatchers`.
- **What happens**: a synced watcher keeps the `minRev` of its registration (or of its last event)
  while writes to other keys move the store on. A compaction past that `minRev` does not affect it
  while it is synced. When the member installs a snapshot (`applySnapshot` → `kv.Restore`; a
  follower that fell behind, a member replacement), `Restore` moves it to the unsynced group, and
  the next `syncWatchers` compares its stale `minRev` with the restored store's compaction
  revision: the watcher is canceled with `CompactRevision`, and the client's watch ends with
  `ErrCompacted` (Kubernetes relists), although every event of its range was delivered. Every
  watcher on that member whose range was quiet since the last compaction is affected at once.
  Reproduction: `issues/etcd-watch-restore-quiet-watcher-compacted/watch_restore_quiet_test.go`
  (a test of package `mvcc`, `server/storage/mvcc`; fails on every run with
  `watcher of an untouched key canceled: CompactRevision=11, events=0`). Its test function:

  ```go
  func TestWatchRestoreQuietWatcherSpuriousCompaction(t *testing.T) {
  	b, _ := betesting.NewDefaultTmpBackend(t)
  	s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{}).(*watchableStore)
  	defer cleanup(s, b)

  	w := s.NewWatchStream()
  	defer w.Close()
  	if _, err := w.Watch(context.TODO(), 0, []byte("quiet"), nil, 0); err != nil { // synced, minRev = 2
  		t.Fatal(err)
  	}
  	var rev int64
  	for i := 0; i < 10; i++ {
  		rev = s.Put([]byte("busy"), []byte("v"), lease.NoLease)
  	}
  	done, err := s.Compact(traceutil.TODO(), rev)
  	if err != nil {
  		t.Fatal(err)
  	}
  	<-done
  	if err := s.Restore(b); err != nil { // as on a snapshot install
  		t.Fatal(err)
  	}
  	select {
  	case resp := <-w.Chan():
  		t.Fatalf("watcher of an untouched key canceled: CompactRevision=%d, events=%d", resp.CompactRevision, len(resp.Events))
  	case <-time.After(3 * watchResyncPeriod):
  	}
  }
  ```

  (The test restores the same backend; a real snapshot carries a compaction revision at least the
  leader's, so the condition `minRev < compactRev` is easier to meet, not harder.)
- **Expected**: the watch API cancels a watch as compacted only when the revision it needs has been
  compacted; a synced watcher needs only revisions after the last one it was delivered.
- **How the proof handles it**: outside the verified scope twice. `Restore` is translated but not
  specified (the watch invariant fixes `restore = false`, `Proof/.../mvcc/InvWatchStore.lean:341`),
  and the watch path is proved for a store that is never compacted (`crevFrozen`; `chooseAll.spec`
  requires every member at or above `compactRev`, `Spec/.../mvcc/watcherGroup__chooseAll.lean:28-36`).
  The invariant already lets a synced watcher's `minRev` lag its delivery point (`lo ≤ minRev ≤ d`,
  `InvWatchStore.lean:605`), which is the state this bug needs. Triage:
  `notes/bug-triage/etcd-15271.md` (proposals `verify-watchable-restore`, `watch-under-compaction`).
- **Possible fixes**: in `Restore`, set each moved watcher's `minRev` to `max(minRev, currentRev +
  1)` of the store *before* the restore (it was synced, so it had everything up to there), so only
  revisions the snapshot adds are re-read; or advance `minRev` for every synced watcher in `notify`
  (cost: a pass over all synced watchers per write, which #15439 avoided).
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#15271 (reading the invariant's synced clause
  `minRev ≤ d` against `Restore`).
