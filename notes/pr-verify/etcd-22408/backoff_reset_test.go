package cache

import (
	"context"
	"sync"
	"testing"
	"testing/synctest"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// okKV always answers the bootstrap Get at revision 1 and records when.
type okKV struct {
	clientv3.KV
	mu    sync.Mutex
	times []time.Time
}

func (k *okKV) Get(context.Context, string, ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	k.mu.Lock()
	k.times = append(k.times, time.Now())
	k.mu.Unlock()
	return &clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 1}}, nil
}

// healthyThenFailWatcher: each watch is healthy (created) for `healthy`, then
// is canceled by the server (e.g. a leader change); records when it failed.
type healthyThenFailWatcher struct {
	healthy time.Duration
	mu      sync.Mutex
	fails   []time.Time
}

func (w *healthyThenFailWatcher) Watch(ctx context.Context, _ string, _ ...clientv3.OpOption) clientv3.WatchChan {
	ch := make(chan clientv3.WatchResponse)
	go func() {
		defer close(ch)
		select {
		case ch <- clientv3.WatchResponse{Created: true, Header: &pb.ResponseHeader{Revision: 1}}:
		case <-ctx.Done():
			return
		}
		select {
		case <-time.After(w.healthy):
		case <-ctx.Done():
			return
		}
		w.mu.Lock()
		w.fails = append(w.fails, time.Now())
		w.mu.Unlock()
		select {
		case ch <- clientv3.WatchResponse{Canceled: true, CancelReason: "leader changed", Header: &pb.ResponseHeader{Revision: 1}}:
		case <-ctx.Done():
		}
	}()
	return ch
}
func (w *healthyThenFailWatcher) RequestProgress(context.Context) error { return nil }
func (w *healthyThenFailWatcher) Close() error                          { return nil }

// After each of a series of watches that were healthy for an hour, how long
// is the cache down (from the watch failing to the next bootstrap Get)?
func TestReviewBackoffNeverResetsAfterHealthyWatch(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		kv := &okKV{}
		w := &healthyThenFailWatcher{healthy: time.Hour}
		c, err := newCache(&clientv3.Client{KV: kv, Watcher: w}, "", defaultConfig(), realClock{})
		if err != nil {
			t.Fatal(err)
		}
		time.Sleep(10*time.Hour + time.Minute)
		c.Close()
		kv.mu.Lock()
		w.mu.Lock()
		defer kv.mu.Unlock()
		defer w.mu.Unlock()
		// each watch is healthy for w.healthy after its Get; the rest of the gap is the retry wait
		var downs []time.Duration
		for i := 1; i < len(kv.times); i++ {
			downs = append(downs, kv.times[i].Sub(kv.times[i-1])-w.healthy)
		}
		t.Logf("downtime after each 1h-healthy watch fails: %v", downs)
		if len(downs) > 0 && downs[len(downs)-1] > defaultConfig().InitialBackoff {
			t.Errorf("after a healthy watch, the retry waited %v, not InitialBackoff %v: the backoff is never reset", downs[len(downs)-1], defaultConfig().InitialBackoff)
		}
	})
}
