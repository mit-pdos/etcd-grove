package mvcc

import (
	"testing"

	"github.com/prometheus/client_golang/prometheus/testutil"
	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
)

// Capped choose, a mix of compacted and live watchers, one compacted watcher whose channel is
// full; gauges after cancelling everything.
func TestWatcherGroupChooseCappedMix(t *testing.T) {
	old := maxWatchersPerSync
	defer func() { maxWatchersPerSync = old }()
	b, _ := betesting.NewDefaultTmpBackend(t)
	s := newWatchableStore(zaptest.NewLogger(t), b, &lease.FakeLessor{}, StoreConfig{})
	defer cleanup(s, b)
	for i := 0; i < 10; i++ {
		s.Put([]byte("foo"), []byte("bar"), lease.NoLease)
	}
	_, err := s.Compact(traceutil.TODO(), 5)
	require.NoError(t, err)

	g0 := testutil.ToFloat64(watcherGauge)
	maxWatchersPerSync = 2
	type wc struct {
		ch     chan WatchResponse
		cancel cancelFunc
		w      *watcher
	}
	var ws []wc
	// 3 compacted (start 1), 3 live (start 7), 1 compacted with a full unbuffered channel.
	for i := 0; i < 7; i++ {
		start := int64(1)
		if i >= 3 && i < 6 {
			start = 7
		}
		bufsz := 16
		if i == 6 {
			bufsz = 0
		}
		ch := make(chan WatchResponse, bufsz)
		w, c := s.watch([]byte("foo"), nil, start, WatchID(i), ch)
		ws = append(ws, wc{ch, c, w})
	}
	require.Equal(t, 7, s.unsynced.size())
	got := map[int][]WatchResponse{}
	for round := 0; round < 20 && s.unsynced.size() > 1; round++ {
		s.syncWatchers()
		for i, x := range ws {
		drain:
			for {
				select {
				case r := <-x.ch:
					got[i] = append(got[i], r)
				default:
					break drain
				}
			}
		}
	}
	// only the full-channel watcher stays unsynced
	require.Equal(t, 1, s.unsynced.size())
	_, in := s.unsynced.watchers[ws[6].w]
	require.True(t, in)
	for i := 0; i < 3; i++ {
		require.Len(t, got[i], 1, "watcher %d", i)
		require.Equal(t, int64(5), got[i][0].CompactRevision)
		require.True(t, ws[i].w.compacted)
	}
	for i := 3; i < 6; i++ {
		require.NotEmpty(t, got[i], "watcher %d", i)
		require.Zero(t, got[i][0].CompactRevision)
		_, insync := s.synced.watchers[ws[i].w]
		require.True(t, insync)
	}
	// now let the full-channel watcher receive
	done := make(chan WatchResponse, 1)
	go func() { done <- <-ws[6].ch }()
	for s.unsynced.size() > 0 {
		s.syncWatchers()
	}
	r := <-done
	require.Equal(t, int64(5), r.CompactRevision)
	require.InDelta(t, 0, testutil.ToFloat64(slowWatcherGauge), 0)
	for _, x := range ws {
		x.cancel()
	}
	require.Equal(t, g0, testutil.ToFloat64(watcherGauge))
}
