package cache

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// TestProbeStoreWatcherLag demonstrates what happens when storeW lags behind
// d.history (nextRev < d.minRev):
//  1. d.resyncLaggingWatchers() calls storeW.Compact(nextRev), closing storeW.respCh.
//  2. applyStorage(storeW) reads !ok from storeW.respCh, returns nil (ignoring
//     storeW.cancelResp), and closes applyErr without sending an error.
//  3. watchEvents receives nil from applyErr, calls c.ready.Reset() (so
//     c.Ready() becomes false), and returns nil to c.watch(rev).
//  4. c.watch(rev) loops in-place with the SAME rev (6) and the SAME, already
//     spent readyOnce, registering a new storeW2 at rev=6 (which is still
//     < d.minRev=7!) and opening a new upstream Watch from rev=6.
//  5. On the new upstream Watch, CreatedNotify and ProgressNotify do not make
//     the cache ready again (readyOnce is spent), and each resync tick compacts
//     storeW again and reopens the upstream Watch from rev=6 until a stale event
//     triggers ErrRevisionTooLow.
func TestProbeStoreWatcherLag(t *testing.T) {
	sw := newStreamWatcher()
	kv := newKVStub(
		&clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 5}},
		&clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 8}},
	)
	fakeClient := &clientv3.Client{Watcher: sw, KV: kv}

	cfg := defaultConfig()
	cfg.HistoryWindowSize = 2
	cfg.PerWatcherBufferSize = 0
	cfg.ResyncInterval = 20 * time.Millisecond

	c, err := newCache(fakeClient, "", cfg, newFakeClock())
	require.NoError(t, err)
	t.Cleanup(c.Close)

	s1 := sw.nextStream(t)
	require.Equal(t, int64(6), s1.rev)
	s1.send(t, clientv3.WatchResponse{Created: true, Header: &pb.ResponseHeader{Revision: 5}})
	waitReady(t, c)
	t.Logf("After stream 1 CreatedNotify: Ready()=%v, store.LatestRev()=%d", c.Ready(), c.store.LatestRev())

	// Send 3 events (revisions 6, 7, 8) before resyncLaggingWatchers runs.
	// With HistoryWindowSize=2, appending revision 8 advances d.minRev to 7 while
	// storeW is still in d.laggingWatchers at nextRev=6 < d.minRev=7.
	for rev := int64(6); rev <= 8; rev++ {
		s1.send(t, clientv3.WatchResponse{
			Header: &pb.ResponseHeader{Revision: rev},
			Events: []*clientv3.Event{event(mvccpb.PUT, "/k", rev)},
		})
	}

	// Next resync tick compacts storeW (6 < d.minRev=7), closing applyErr with nil.
	// watchEvents calls c.ready.Reset() and returns nil, so c.watch(6) loops in-place
	// and opens stream 2 from the OLD rev=6 with the already-spent readyOnce!
	s2 := sw.nextStream(t)
	t.Logf("Stream 2 opened at rev=%d (d.minRev=%d, d.maxRev=%d, store.LatestRev()=%d, Ready()=%v)",
		s2.rev, c.demux.minRev, c.demux.LatestRev(), c.store.LatestRev(), c.Ready())
	require.Equal(t, int64(6), s2.rev)
	require.False(t, c.Ready(), "c.ready was reset when storeW was compacted")

	// Stream 2 receives CreatedNotify at revision 8, but readyOnce was already spent
	// in iteration 1 of c.watch(6), so c.Ready() stays false!
	s2.send(t, clientv3.WatchResponse{Created: true, Header: &pb.ResponseHeader{Revision: 8}})
	s2.send(t, clientv3.WatchResponse{Header: &pb.ResponseHeader{Revision: 8}}) // ProgressNotify
	time.Sleep(10 * time.Millisecond)
	t.Logf("After stream 2 CreatedNotify + ProgressNotify: Ready()=%v, store.LatestRev()=%d",
		c.Ready(), c.store.LatestRev())
	require.False(t, c.Ready(), "Ready() remains false because readyOnce in c.watch(6) was already spent")
}
