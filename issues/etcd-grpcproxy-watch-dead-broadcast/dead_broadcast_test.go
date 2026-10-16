// Reproduction for issues/etcd-grpcproxy-watch-dead-broadcast.md (etcd-io/etcd#18231, #21813).
//
// Drop into go.etcd.io/etcd/server/v3/proxy/grpcproxy (repository etcd-io/etcd, or the fork
// upamanyus/etcd at the pinned revision 107edf7e492a5cd7e8d958ed8a7ac9dbf1ecf81f), then run, from
// the module directory server/:
//
//	go test ./proxy/grpcproxy/ -run TestWatchBroadcastDeadAfterBackendClose -v
//
// Passes at the pin: after the backend watch channel closes (preceded by the client's final
// Canceled response, as closeSubstream sends it on a stream error), the broadcast's goroutine
// exits without re-watching or telling its receiver; it stays in bcasts with nextrev reset to 1;
// a new watcher starting at revision 3 is put into it, and coalesce moves a live broadcast's
// watcher into it. Every check below states the buggy behavior.
package grpcproxy

import (
	"context"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// fakeWatcher hands out a fresh channel per Watch call and records them. It does not close a
// channel when its context is canceled, so stopping the live broadcast below waits out
// watchBroadcast.stop's one-second timeout.
type fakeWatcher struct {
	mu  sync.Mutex
	chs []chan clientv3.WatchResponse
}

func (f *fakeWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	ch := make(chan clientv3.WatchResponse, 4)
	f.mu.Lock()
	f.chs = append(f.chs, ch)
	f.mu.Unlock()
	return ch
}
func (f *fakeWatcher) RequestProgress(ctx context.Context) error { return nil }
func (f *fakeWatcher) Close() error                              { return nil }

func (f *fakeWatcher) calls() int {
	f.mu.Lock()
	defer f.mu.Unlock()
	return len(f.chs)
}

func (f *fakeWatcher) ch(i int) chan clientv3.WatchResponse {
	f.mu.Lock()
	defer f.mu.Unlock()
	return f.chs[i]
}

type fakeWatchServer struct{ pb.Watch_WatchServer }

func (fakeWatchServer) Context() context.Context { return context.Background() }

func waitFor(t *testing.T, what string, cond func() bool) {
	t.Helper()
	deadline := time.Now().Add(5 * time.Second)
	for !cond() {
		if time.Now().After(deadline) {
			t.Fatalf("timed out waiting for %s", what)
		}
		time.Sleep(time.Millisecond)
	}
}

func TestWatchBroadcastDeadAfterBackendClose(t *testing.T) {
	fw := &fakeWatcher{}
	wp := &watchProxy{cw: fw, ctx: context.Background(), lg: zap.NewNop()}
	wbs := newWatchBroadcasts(wp)
	wps := &watchProxyStream{
		watchCh: make(chan *pb.WatchResponse, 16),
		stream:  fakeWatchServer{},
		ctx:     context.Background(),
		cancel:  func() {},
		lg:      zap.NewNop(),
	}
	bcastOf := func(w *watcher) *watchBroadcast {
		wbs.mu.Lock()
		defer wbs.mu.Unlock()
		return wbs.watchers[w]
	}

	// w1: a current watch on "a"; the backend watch is created at revision 5.
	w1 := &watcher{wr: watchRange{key: "a"}, id: 1, wps: wps}
	wbs.add(w1)
	dead := bcastOf(w1)
	waitFor(t, "first backend Watch", func() bool { return fw.calls() == 1 })
	fw.ch(0) <- clientv3.WatchResponse{Header: &pb.ResponseHeader{Revision: 5}, Created: true}
	if r := <-wps.watchCh; !r.Created {
		t.Fatalf("expected w1's Created, got %v", r)
	}

	// The backend stream fails: the client sends a final Canceled response with an empty
	// header (client/v3/watch.go:495) and closes the channel.
	fw.ch(0) <- clientv3.WatchResponse{Header: &pb.ResponseHeader{}, Canceled: true}
	close(fw.ch(0))
	<-dead.donec

	// #18231: w1 is told nothing, and nothing re-watches.
	select {
	case r := <-wps.watchCh:
		t.Fatalf("w1 got a response after the backend close: %v", r)
	case <-time.After(100 * time.Millisecond):
	}
	if fw.calls() != 1 {
		t.Fatalf("expected no re-watch, got %d Watch calls", fw.calls())
	}
	dead.mu.RLock()
	nextrev := dead.nextrev
	dead.mu.RUnlock()
	if nextrev != 1 {
		t.Fatalf("expected the final Canceled response to reset nextrev to 1, got %d", nextrev)
	}

	// #21813: a new watcher from revision 3 is put into the dead broadcast (a Created is emulated
	// for it), and no backend watch is started for it.
	w2 := &watcher{wr: watchRange{key: "a"}, id: 2, nextrev: 3, wps: wps}
	wbs.add(w2)
	if bcastOf(w2) != dead {
		t.Fatal("expected w2 to join the dead broadcast")
	}
	if r := <-wps.watchCh; !r.Created || r.WatchId != 2 {
		t.Fatalf("expected w2's emulated Created, got %v", r)
	}
	if fw.calls() != 1 {
		t.Fatalf("expected no backend watch for w2, got %d Watch calls", fw.calls())
	}

	// A current watcher gets a live broadcast of its own; on its first update, coalesce moves
	// it into the dead broadcast (8 >= 1 and responses > 0) and stops the live one.
	w3 := &watcher{wr: watchRange{key: "a"}, id: 3, wps: wps}
	wbs.add(w3)
	live := bcastOf(w3)
	if live == dead {
		t.Fatal("expected w3 to get a new broadcast")
	}
	waitFor(t, "second backend Watch", func() bool { return fw.calls() == 2 })
	fw.ch(1) <- clientv3.WatchResponse{Header: &pb.ResponseHeader{Revision: 7}, Created: true}
	waitFor(t, "w3 moved into the dead broadcast", func() bool { return bcastOf(w3) == dead })
	t.Logf("w1, w2 and w3 all wait on a broadcast whose backend watch has ended")
}
