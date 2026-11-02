package mvcc

import (
	"testing"
	"time"

	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// TestWatchCompactedResentManyUnsynced: 600 watches (one per stream, as 600
// clients would have) start below the compaction revision. More than
// maxWatchersPerSync (512) of them are unsynced at once, so the store's sync
// loop handles them through a copy of the unsynced group. Each watch should be
// sent the compaction response once and then leave the unsynced group; the
// compacted ones chosen through the copy stay unsynced and are sent it again
// at every sync.
func TestWatchCompactedResentManyUnsynced(t *testing.T) {
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := New(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)

	for i := 0; i < 5; i++ {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	}
	if _, err := s.Compact(traceutil.TODO(), 4); err != nil {
		t.Fatal(err)
	}

	const n = 600
	ws := make([]WatchStream, n)
	for i := range ws {
		ws[i] = s.NewWatchStream()
		defer ws[i].Close()
		if _, err := ws[i].Watch(t.Context(), 0, []byte("foo"), nil, 1); err != nil {
			t.Fatal(err)
		}
	}

	// Let the sync loop (every 100 ms) run a few times.
	time.Sleep(time.Second)

	compacted := 0
	for i := range ws {
		for len(ws[i].Chan()) > 0 {
			if wr := <-ws[i].Chan(); wr.CompactRevision != 0 {
				compacted++
			}
		}
	}
	if compacted != n {
		t.Fatalf("%d compaction responses for %d compacted watches, want one each", compacted, n)
	}
}
