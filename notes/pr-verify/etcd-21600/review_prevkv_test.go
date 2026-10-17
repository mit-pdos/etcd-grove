// Review probes for etcd-io/etcd#21600 (WithPrevKV on cache watch).
package cache

import (
	"context"
	"fmt"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

func reviewPut(rev int64) clientv3.WatchResponse {
	return clientv3.WatchResponse{Events: []*clientv3.Event{{
		Type: clientv3.EventTypePut,
		Kv: &mvccpb.KeyValue{Key: []byte("/a"), Value: []byte(fmt.Sprintf("v%d", rev)),
			CreateRevision: 2, ModRevision: rev, Version: rev - 1},
	}}}
}

// A: a WithRev watch at the oldest revision the demux still replays (no slow
// consumer, accepted, not compacted) gets PrevKv == nil for its first event:
// the store's history holds as many snapshots as the demux holds batches, so
// the snapshot before the demux's oldest batch is already gone.
func TestReviewPrevKVHistoricalWatchOldestRev(t *testing.T) {
	initial := &clientv3.GetResponse{
		Header: &pb.ResponseHeader{Revision: 2},
		Kvs:    []*mvccpb.KeyValue{{Key: []byte("/a"), Value: []byte("v2"), CreateRevision: 2, ModRevision: 2, Version: 1}},
	}
	mw := newMockWatcher(64)
	c, err := New(&clientv3.Client{Watcher: mw, KV: newKVStub(initial)}, "", WithHistoryWindowSize(3))
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	mw.triggerCreatedNotify()
	<-mw.registered
	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
	defer cancel()
	if err := c.WaitReady(ctx); err != nil {
		t.Fatal(err)
	}
	for rev := int64(3); rev <= 8; rev++ {
		mw.responses <- reviewPut(rev)
		if err := c.WaitForRevision(ctx, rev); err != nil {
			t.Fatal(err)
		}
	}
	c.demux.mu.RLock()
	minRev := c.demux.minRev
	c.demux.mu.RUnlock()
	t.Logf("demux minRev=%d (oldest replayable), store oldest snapshot=%d", minRev, c.store.history.PeekOldest())

	ch := c.Watch(ctx, "/a", clientv3.WithRev(minRev), clientv3.WithPrevKV())
	for rev := minRev; rev <= 8; rev++ {
		select {
		case <-ctx.Done():
			t.Fatal("timeout")
		case resp := <-ch:
			if resp.Canceled {
				t.Fatalf("watch canceled: %q compactRev=%d", resp.CancelReason, resp.CompactRevision)
			}
			for _, ev := range resp.Events {
				var got string
				if ev.PrevKv != nil {
					got = string(ev.PrevKv.Value)
				}
				want := fmt.Sprintf("v%d", ev.Kv.ModRevision-1)
				t.Logf("event rev %d: PrevKv=%q (etcd: %q)", ev.Kv.ModRevision, got, want)
				if got != want {
					t.Errorf("event rev %d: PrevKv %q, want %q", ev.Kv.ModRevision, got, want)
				}
			}
		}
	}
}

// B: after the cache's upstream watch fails and the cache reconnects at the
// same revision (the demux keeps its watchers: Init(maxRev+1)), the store's
// history is rebased to the one Restore snapshot, so every buffered event of a
// WithPrevKV watcher not yet attached loses its PrevKv, silently.
func TestReviewPrevKVLostAfterReconnectSameRev(t *testing.T) {
	initial := &clientv3.GetResponse{
		Header: &pb.ResponseHeader{Revision: 2},
		Kvs:    []*mvccpb.KeyValue{{Key: []byte("/a"), Value: []byte("v2"), CreateRevision: 2, ModRevision: 2, Version: 1}},
	}
	again := &clientv3.GetResponse{
		Header: &pb.ResponseHeader{Revision: 6},
		Kvs:    []*mvccpb.KeyValue{{Key: []byte("/a"), Value: []byte("v6"), CreateRevision: 2, ModRevision: 6, Version: 5}},
	}
	mw := newMockWatcher(64)
	c, err := New(&clientv3.Client{Watcher: mw, KV: newKVStub(initial, again)}, "")
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	mw.triggerCreatedNotify()
	<-mw.registered
	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
	defer cancel()
	if err := c.WaitReady(ctx); err != nil {
		t.Fatal(err)
	}
	ch := c.Watch(ctx, "/a", clientv3.WithPrevKV())
	for rev := int64(3); rev <= 6; rev++ {
		mw.responses <- reviewPut(rev)
		if err := c.WaitForRevision(ctx, rev); err != nil {
			t.Fatal(err)
		}
	}
	// Upstream watch ends with a non-compaction error; the cache re-gets (rev 6) and re-watches at 7.
	mw.resetRegistered()
	mw.responses <- clientv3.WatchResponse{Canceled: true, CancelReason: "transient"}
	<-mw.registered
	waitUntil(t, 2*time.Second, 5*time.Millisecond, func() bool {
		c.store.mu.RLock()
		defer c.store.mu.RUnlock()
		return c.store.history.size == 1 && c.store.history.PeekOldest() == 6
	})
	for rev := int64(3); rev <= 6; rev++ {
		select {
		case <-ctx.Done():
			t.Fatal("timeout")
		case resp, ok := <-ch:
			if !ok || resp.Canceled {
				t.Fatalf("watch ended: ok=%v %+v", ok, resp)
			}
			for _, ev := range resp.Events {
				var got string
				if ev.PrevKv != nil {
					got = string(ev.PrevKv.Value)
				}
				want := fmt.Sprintf("v%d", ev.Kv.ModRevision-1)
				t.Logf("event rev %d: PrevKv=%q (etcd: %q)", ev.Kv.ModRevision, got, want)
				if got != want {
					t.Errorf("event rev %d: PrevKv %q, want %q", ev.Kv.ModRevision, got, want)
				}
			}
		}
	}
}
