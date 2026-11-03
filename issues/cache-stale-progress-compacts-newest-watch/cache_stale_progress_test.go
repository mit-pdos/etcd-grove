package integration

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	cache "go.etcd.io/etcd/cache/v3"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// A progress notification answered before the cache's watch is created, at a
// revision below the cache's Get, reaches the cache's watch after its Created
// response (sendLoop sends ctrlStream's Created before the queued progress
// response), and makes a cache watch "from now" compacted.
func TestCacheStaleProgressCompactsNewestWatch(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.Client(0)
	ctx := t.Context()

	// A busy watch on the same gRPC watch stream as the cache's (no metadata
	// in either context), with prevKV so that the server's sendLoop is slow.
	bctx, bcancel := context.WithCancel(ctx)
	defer bcancel()
	for i := 0; i < 8; i++ {
		bw := cli.Watch(bctx, "/busy/", clientv3.WithPrefix(), clientv3.WithPrevKV())
		go func() {
			for range bw {
			}
		}()
	}
	val := strings.Repeat("v", 12*1024)
	var wg sync.WaitGroup
	stop := make(chan struct{})
	wg.Add(1)
	go func() {
		defer wg.Done()
		n := 0
		for {
			select {
			case <-stop:
				return
			default:
			}
			ops := make([]clientv3.Op, 0, 100)
			for j := 0; j < 100; j++ {
				ops = append(ops, clientv3.OpPut(fmt.Sprintf("/busy/%d", j), val))
			}
			tr, err := cli.Txn(ctx).Then(ops...).Commit()
			if err != nil {
				return
			}
			if n++; n%50 == 0 {
				cli.Compact(ctx, tr.Header.Revision-10)
			}
		}
	}()
	defer func() { close(stop); wg.Wait() }()
	time.Sleep(200 * time.Millisecond)

	hits := 0
	trials := 0
	stales, progs := 0, 0
	for trial := 0; trial < 500 && hits == 0; trial++ {
		trials++
		prefix := fmt.Sprintf("/c%d/", trial)
		// Another user of the client asks for progress on the shared watch
		// stream until the cache's Get returns.
		stopReq := make(chan struct{})
		reqDone := make(chan struct{})
		go func() {
			defer close(reqDone)
			for {
				select {
				case <-stopReq:
					return
				default:
				}
				cli.RequestProgress(ctx)
				time.Sleep(200 * time.Microsecond)
			}
		}()
		kv := &spyKV{KV: cli.KV, onGet: func() { close(stopReq); <-reqDone }}
		sw := &spyWatcher{Watcher: cli.Watcher, kv: kv}
		c, err := cache.New(&clientv3.Client{KV: kv, Watcher: sw}, prefix)
		if err != nil {
			t.Fatal(err)
		}
		if err := c.WaitReady(ctx); err != nil {
			t.Fatal(err)
		}
		time.Sleep(10 * time.Millisecond)
		wctx, wcancel := context.WithCancel(ctx)
		wch := c.Watch(wctx, prefix+"x")
		if _, err := cli.Put(ctx, prefix+"x", "1"); err != nil {
			t.Fatal(err)
		}
		select {
		case resp, ok := <-wch:
			if !ok {
				t.Fatalf("trial %d: watch closed", trial)
			}
			if resp.CompactRevision != 0 || resp.Canceled {
				hits++
				t.Logf("trial %d: a cache watch from now was canceled (compact revision %d, %q)", trial, resp.CompactRevision, resp.CancelReason)
			}
		case <-time.After(5 * time.Second):
			t.Fatalf("trial %d: no response", trial)
		}
		wcancel()
		c.Close()
		progs += int(sw.progs.Load())
		if sw.stale.Load() != 0 {
			stales++
			t.Logf("trial %d: the cache's watch (from %d, after its Get at %d) received a progress notification at %d", trial, kv.rev.Load()+1, kv.rev.Load(), sw.staleRev.Load())
		}
	}
	t.Logf("%d trials with a stale progress at the cache's watch, %d progress responses", stales, progs)
	if hits > 0 {
		t.Fatalf("%d of %d trials: a stale progress notification compacted a cache watch from now", hits, trials)
	}
	t.Logf("no hit in %d trials", trials)
}

type spyKV struct {
	clientv3.KV
	rev   atomic.Int64
	once  sync.Once
	onGet func()
}

func (k *spyKV) Get(ctx context.Context, key string, opts ...clientv3.OpOption) (*clientv3.GetResponse, error) {
	if k.onGet != nil {
		k.once.Do(k.onGet)
	}
	r, err := k.KV.Get(ctx, key, opts...)
	if err == nil {
		k.rev.Store(r.Header.Revision)
	}
	return r, err
}

type spyWatcher struct {
	clientv3.Watcher
	kv       *spyKV
	stale    atomic.Int32
	progs    atomic.Int32
	staleRev atomic.Int64
}

func (w *spyWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	R := w.kv.rev.Load()
	in := w.Watcher.Watch(ctx, key, opts...)
	out := make(chan clientv3.WatchResponse)
	go func() {
		defer close(out)
		for resp := range in {
			if resp.IsProgressNotify() {
				w.progs.Add(1)
			}
			if resp.IsProgressNotify() && resp.Header.Revision < R {
				w.stale.Add(1)
				w.staleRev.Store(resp.Header.Revision)
			}
			select {
			case out <- resp:
			case <-ctx.Done():
				return
			}
		}
	}()
	return out
}
