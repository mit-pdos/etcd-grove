---
upstream: unchecked
checked: 2026-11-02
links: []
---

# server/storage/mvcc: a watch from exactly the compaction revision loses the earlier changes of a key changed twice in that revision

- **Status**: a wrong result at mvcc's Go API (an event missing from a watch). Not reachable through
  etcd's gRPC API, which rejects a transaction that changes a key twice (`checkIntervals`,
  `server/etcdserver/api/v3rpc/key.go:236-290`: `ErrGRPCDuplicateKey` for a key put twice, or put
  and covered by a delete of the same request); a client of mvcc's `TxnWrite` (mvcc's own tests,
  embedders, this repository's randomized tester `examples/mvccrand`) can make such a revision.
- **Where**: at the etcd pin (`etc/goose.py`, `249d76bea`), `server/storage/mvcc/`:
  - the compaction keeps, per key, only the largest revision at or below the compaction revision
    `c` (`key_index.go`, `doCompact`: `g.walk(f)` stops at the first, from the newest, revision with
    `Main <= atRev`), so of two changes of a key at revision `c` (`{c,0}`, `{c,1}`) the backend
    loses `{c,0}`;
  - a watcher is told it was compacted only when its next revision is *below* the compaction
    revision (`watchable_store.go:371`, `if w.minRev < compactionRev`); at `minRev == c`,
    `syncWatchers` reads revision `c`'s events from the backend (`rangeEvents`), where `{c,0}` is gone.
- **What happens** (reproduction; at the pin it fails as shown): revision 2 puts `a` twice; a watch
  of `a` from revision 2 receives both events before the compaction at 2, and one after it, with no
  compaction response.

  ```go
  func TestWatchFromCompactRevSameKeyTwice(t *testing.T) {
  	lg := zap.NewNop()
  	bcfg := backend.DefaultBackendConfig(lg)
  	bcfg.Path = filepath.Join(t.TempDir(), "db")
  	be := backend.New(bcfg)
  	defer be.Close()
  	kv := mvcc.New(lg, be, &lease.FakeLessor{}, mvcc.StoreConfig{})
  	defer kv.Close()
  	tw := kv.Write(traceutil.TODO())
  	tw.Put([]byte("a"), []byte("v1"), lease.NoLease)
  	tw.Put([]byte("a"), []byte("v2"), lease.NoLease)
  	tw.End()
  	c := kv.Rev()                                   // 2
  	kv.Put([]byte("b"), []byte("x"), lease.NoLease) // 3
  	count := func() int {
  		ws := kv.NewWatchStream()
  		defer ws.Close()
  		if _, err := ws.Watch(context.TODO(), 0, []byte("a"), nil, c); err != nil {
  			t.Fatal(err)
  		}
  		n := 0
  		timeout := time.After(500 * time.Millisecond)
  		for {
  			select {
  			case r := <-ws.Chan():
  				if r.CompactRevision != 0 {
  					t.Fatalf("compacted response %d", r.CompactRevision)
  				}
  				n += len(r.Events)
  			case <-timeout:
  				return n
  			}
  		}
  	}
  	before := count()
  	ch, err := kv.Compact(traceutil.TODO(), c)
  	if err != nil {
  		t.Fatal(err)
  	}
  	<-ch
  	after := count()
  	if before != after { // 2 before, 1 after
  		t.Errorf("watch from the compaction revision lost events: %d before, %d after", before, after)
  	}
  }
  ```

  (imports: `context`, `path/filepath`, `testing`, `time`, `go.uber.org/zap`,
  `go.etcd.io/etcd/pkg/v3/traceutil`, `go.etcd.io/etcd/server/v3/lease`,
  `go.etcd.io/etcd/server/v3/storage/backend`, `go.etcd.io/etcd/server/v3/storage/mvcc`.)
- **Expected**: a watch from revision `r` receives every event at and after `r`, or a compaction
  response when `r` is compacted. Revision `c` is not reported compacted (a `Range` at `c` succeeds,
  showing the last value), yet its history is incomplete: either a watch from `c` should get a
  compaction response when `c` had several changes of one key, or the compaction should keep them.
- **How the proof handles it**: mvcc's candidate API (2026-11-02, the scratch candidate of
  `notes/mvcc-api-candidate.md`'s round 10) states a watcher's events exactly only while the store's
  compaction revision is below the watcher's first revision (`wsRecvOk`'s `σ.crev < w.lo`); the
  tester never compacts, and etcd's watch proof excludes compaction (`noCompactor`, v3rpc's
  `upOk`).
- **Possible fixes**: in `syncWatchers`, treat `w.minRev <= compactionRev` as compacted when the
  compaction revision had several sub-revisions of a key in the watcher's range (or always, as
  `Range` at the compaction revision still answers from the kept one); or make `doCompact` keep every
  sub-revision of the compaction revision's main revision.
- **Found**: 2026-11-02, designing the watch guarantee of mvcc's candidate API under compaction
  (`notes/mvcc-api-candidate.md`).
