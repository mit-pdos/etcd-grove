---
upstream: unchecked
---

# server/storage/mvcc: a compacted watcher chosen from a large unsynced group stays unsynced and is sent the compaction response again

- **Status**: a bug (a wrong result of the watchable store's bookkeeping; a duplicate response on
  the wire), reproduced at the mvcc level. Narrow: it needs more than `maxWatchersPerSync` (512)
  unsynced watchers at once, some of them behind the compaction revision.
- **Where** (the fork pin, `etc/goose.py`): `server/storage/mvcc/watcher_group.go:226-238`
  (`choose`: with at least `maxWatchers` members it copies `maxWatchers` of them into a fresh
  group `ret` and calls `ret.chooseAll`), `:241-269` (`chooseAll`: a member with
  `minRev < compactRev` is sent `WatchResponse{WatchID, CompactRevision}`, marked
  `compacted = true` and `wg.delete(w)`d: from `ret`, the copy), and
  `server/storage/mvcc/watchable_store.go:368-411` (`syncWatchers` iterates over the copy `wg`,
  skipping the members below `compactionRev`, and deletes from `s.unsynced` only the members it
  syncs).
- **What happens**: in the copy branch the compacted watcher is deleted from the copy only and
  stays in `s.unsynced` with `compacted = true`. Every later `syncWatchers` that chooses it (every
  100 ms, `syncWatchersLoop`) sends it the compaction response again, with the compaction revision
  of the moment, until the client cancels the watch. The Go client tolerates it (the substream is
  closing; the duplicate is a response for an unknown id, which the client answers with a cancel),
  but every duplicate is a canceled response on the stream for an id the server already ended, the
  watcher counts as unsynced (`slowWatcherGauge`) meanwhile, and a client that ignores responses
  for ended ids and never cancels gets one every sync. Below 512 unsynced watchers `choose` passes
  the group itself, the delete is from `s.unsynced`, and the response is sent once.
- **Reproduction** (a test in package `mvcc`, `maxWatchersPerSync` lowered to 2 so that three
  watchers take the copy branch; run with `go test -overlay` at the pin): two of the three streams
  get the compaction response twice, and `s.unsynced` still holds all three.

  ```go
  func TestWatchCompactedResentOverMaxPerSync(t *testing.T) {
  	old := maxWatchersPerSync
  	maxWatchersPerSync = 2
  	defer func() { maxWatchersPerSync = old }()
  	b, _ := betesting.NewDefaultTmpBackend(t)
  	s := newWatchableStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
  	defer cleanup(s, b)
  	for i := 0; i < 5; i++ {
  		s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
  	}
  	if _, err := s.Compact(traceutil.TODO(), 4); err != nil {
  		t.Fatal(err)
  	}
  	ws := make([]WatchStream, 3)
  	for i := range ws {
  		ws[i] = s.NewWatchStream()
  		ws[i].Watch(t.Context(), 0, []byte("foo"), nil, 1)
  	}
  	s.syncWatchers()
  	s.syncWatchers()
  	total := 0
  	for i := range ws {
  		for len(ws[i].Chan()) > 0 {
  			if wr := <-ws[i].Chan(); wr.CompactRevision != 0 {
  				total++
  			}
  		}
  	}
  	if total > 3 {
  		t.Fatalf("%d compaction responses for 3 watchers; unsynced left: %d", total, s.unsynced.size())
  	}
  }
  ```

  (Fails at the pin: 5 responses, 3 left unsynced. Run 2026-11-01.)
- **Expected**: one compaction response per watcher, and the watcher out of `s.unsynced` once it is
  sent (as with fewer than 512 unsynced watchers).
- **How the proof handles it**: not yet (watches across a compaction are being specified,
  `notes/watch-compaction-plan.md`); the watchable store's state model will admit a compacted
  watcher that is still unsynced and is sent the response repeatedly, as the code does.
- **Possible fixes**: in `syncWatchers`, delete from `s.unsynced` the members `chooseAll` compacted
  (they are the ones with `compacted` set); or have `choose` return the compacted members to its
  caller; or make `chooseAll` delete from the source group as well as the copy.
- **Found**: 2026-11-01, by the spec review of the watch-compaction Draft (the statement of
  `watcherGroup.choose` in its copy branch).
