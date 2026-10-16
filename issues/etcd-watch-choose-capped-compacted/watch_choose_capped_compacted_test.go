// Reproduction for issues/etcd-watch-choose-capped-compacted.md (etcd-io/etcd#22294).
//
// Drop into go.etcd.io/etcd/server/v3/storage/mvcc (repository etcd-io/etcd, or the fork
// upamanyus/etcd at the pinned revision 107edf7e492a5cd7e8d958ed8a7ac9dbf1ecf81f), then run, from
// the module directory server/:
//
//	GOTOOLCHAIN=go1.27.1 go test ./storage/mvcc/ -run TestWatchChooseCompactedWatcherRetired -count=1 -v
//
// At the pin the subtest "capped" fails (each compacted watcher stays in s.unsynced and gets a
// CompactRevision response on every resync); the subtest "uncapped" passes.
package mvcc

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

func TestWatchChooseCompactedWatcherRetired(t *testing.T) {
	// Two unsynced watchers below the compaction revision. With maxWatchersPerSync = 2,
	// choose takes its capped branch (len(watchers) >= maxWatchers); with 3, the uncapped one.
	for _, tc := range []struct {
		name    string
		maxSync int
	}{{"capped", 2}, {"uncapped", 3}} {
		t.Run(tc.name, func(t *testing.T) {
			oldMax := maxWatchersPerSync
			maxWatchersPerSync = tc.maxSync
			defer func() { maxWatchersPerSync = oldMax }()

			b, _ := betesting.NewDefaultTmpBackend(t)
			s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{}).(*watchableStore)
			defer cleanup(s, b)

			for i := 0; i < 10; i++ {
				s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
			}
			_, err := s.Compact(traceutil.TODO(), 5)
			require.NoError(t, err)

			w := s.NewWatchStream()
			defer w.Close()
			for id := WatchID(0); id < 2; id++ {
				_, err := w.Watch(t.Context(), id, []byte("foo"), nil, 1) // startRev 1 < 5: unsynced
				require.NoError(t, err)
			}

			// Three resyncs (the background loop may add more; it changes nothing below).
			s.syncWatchers()
			s.syncWatchers()
			s.syncWatchers()

			s.mu.Lock()
			unsynced := s.unsynced.size()
			s.mu.Unlock()

			compactResps := map[WatchID]int{}
		drain:
			for {
				select {
				case resp := <-w.Chan():
					if resp.CompactRevision != 0 {
						compactResps[resp.WatchID]++
					}
				default:
					break drain
				}
			}
			t.Logf("unsynced watchers after resyncs: %d; CompactRevision responses per watch ID: %v",
				unsynced, compactResps)
			require.Equal(t, 0, unsynced, "a watcher canceled as compacted stayed in s.unsynced")
			require.Equal(t, map[WatchID]int{0: 1, 1: 1}, compactResps,
				"each compacted watcher must get exactly one CompactRevision response")
		})
	}
}
