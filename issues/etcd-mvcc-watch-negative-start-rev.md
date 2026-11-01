---
upstream: unchecked
checked: 2026-11-01
links: []
---

# server/storage/mvcc: `WatchStream.Watch` with a negative start revision does not watch "after currentRev" as documented

- **Status**: documentation the code contradicts. Not reachable through etcd's gRPC API, which
  rejects a negative start revision first; a client of mvcc's Go API (mvcc's own callers, tests,
  embedders) gets a replay of the history, or a compaction response from a store never compacted.
- **Where**: `server/storage/mvcc/watcher.go:44-45` at the etcd pin (`etc/goose.py`, `249d76bea`):
  `WatchStream.Watch`'s documentation, "If "startRev" <=0, watch observes events after
  currentRev." The code (`watchable_store.go`, `watch`, lines 139-153) treats only `0` that way:
  `synced := startRev > s.store.currentRev || startRev == 0`. A negative start revision makes an
  unsynced watcher with `minRev = startRev`; `syncWatchers` then reads from `minRev` (clamped to `0`
  by `rangeEvents`, `watchable_store.go:430-433`) or, when `minRev` is below the compaction revision
  (`-1` on a store never compacted, so for `startRev ≤ -2`), sends a compaction response with
  `CompactRevision = -1`.
- **What happens** (reproduction, a test in a package importing mvcc; passes, confirming the
  behaviour, at the pin): with one put at revision 2 before the watch, `startRev = 0` receives
  nothing until a later write, as documented; `startRev = -1` receives the put of revision 2 at
  once; `startRev = -2` receives a compaction response (`CompactRevision -1`, no events).

  ```go
  func TestWatchNegativeStartRev(t *testing.T) {
  	for _, start := range []int64{0, -1, -2} {
  		lg := zap.NewNop()
  		bcfg := backend.DefaultBackendConfig(lg)
  		bcfg.Path = filepath.Join(t.TempDir(), "x.db")
  		be := backend.New(bcfg)
  		kv := mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
  		kv.Put([]byte("a"), []byte("1"), lease.NoLease) // revision 2, before the watch
  		ws := kv.NewWatchStream()
  		if _, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, start); err != nil {
  			t.Fatal(err)
  		}
  		select {
  		case r := <-ws.Chan():
  			t.Logf("startRev %d: before any later write, got %d events, revision %d, compactRevision %d",
  				start, len(r.Events), r.Revision, r.CompactRevision)
  		case <-time.After(500 * time.Millisecond):
  			t.Logf("startRev %d: nothing before a later write (as documented)", start)
  		}
  		ws.Close()
  		kv.Close()
  		be.Close()
  	}
  }
  ```

  Output: `startRev 0: nothing before a later write (as documented)`; `startRev -1: ... got 1
  events, revision 2, compactRevision 0`; `startRev -2: ... got 0 events, revision 0,
  compactRevision -1`.
- **Expected**: per the documentation, a negative start revision watches from the revision after
  the current one, as `0` does.
- **How the proof handles it**: today's `watchStream.Watch.spec` and the candidate
  `watchStream.Watch.specC` (`notes/mvcc-api-candidate.md`) take `0 ≤ startRev`; the candidate's
  docstring says the premise is what keeps the first revision and the compaction responses' law
  (`0 < CompactRevision`) true. etcd's gRPC watch rejects a negative start revision
  (`etcdserver/api/v3rpc/watch.go:270-284`), so the server meets the premise.
- **Possible fixes**: treat `startRev < 0` as `0` in `watchableStore.watch` (what the
  documentation says), or document `<= 0` as `== 0` and that a negative start revision is invalid
  (and reject it with an error).
- **Found**: 2026-11-01, by the spec review of the candidate mvcc API (round 2, the `spec-reviewer`
  agent), reproduced with the test above.
