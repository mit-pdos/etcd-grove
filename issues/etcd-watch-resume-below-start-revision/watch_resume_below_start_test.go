package watch

import (
	"context"
	"sync"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestWatchResumeBelowStartRevision: a progress response the server computed before a watch
// from a future revision was registered reaches that watch (sendLoop sends the watch's Created
// response before the queued progress response, and the client broadcasts the progress to every
// substream, the new one included). The client then lowers the watch's resume revision below its
// start revision, and after a reconnect the watch delivers an event below the revision it asked for.
func TestWatchResumeBelowStartRevision(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1, UseBridge: true})
	defer clus.Terminate(t)
	cli := clus.Client(0)
	ctx := t.Context()
	const trials = 2000
	for trial := 0; trial < trials; trial++ {
		gresp, err := cli.Get(ctx, "k")
		if err != nil {
			t.Fatal(err)
		}
		start := gresp.Header.Revision + 100 // above every revision this trial writes
		w := clientv3.NewWatcher(cli)        // a fresh gRPC watch stream per trial
		tctx, cancel := context.WithCancel(ctx)
		bw := w.Watch(tctx, "busy", clientv3.WithPrefix())
		var wg sync.WaitGroup
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 30; j++ {
				cli.Put(ctx, "busy/x", "v")
			}
		}()
		time.Sleep(time.Millisecond)
		if err := w.RequestProgress(tctx); err != nil {
			t.Fatal(err)
		}
		wch := w.Watch(tctx, "k", clientv3.WithRev(start))
		stale := int64(0)
		select {
		case resp := <-wch:
			if resp.IsProgressNotify() && resp.Header.Revision < start {
				stale = resp.Header.Revision
			}
		case <-time.After(50 * time.Millisecond):
		}
		wg.Wait()
		if stale != 0 {
			t.Logf("trial %d: the watch from revision %d received a progress notification at revision %d", trial, start, stale)
			presp, err := cli.Put(ctx, "k", "below-start")
			if err != nil {
				t.Fatal(err)
			}
			clus.Members[0].Bridge().DropConnections()
			select {
			case resp := <-wch:
				for _, ev := range resp.Events {
					if ev.Kv.ModRevision < start {
						t.Fatalf("after a reconnect, the watch from revision %d delivered an event at revision %d (the put at %d)",
							start, ev.Kv.ModRevision, presp.Header.Revision)
					}
				}
				t.Fatalf("unexpected response after the reconnect: %+v", resp)
			case <-time.After(10 * time.Second):
				t.Fatalf("trial %d: stale progress, but no event below the start revision within 10s of the reconnect", trial)
			}
		}
		cancel()
		w.Close()
		for range bw {
		}
	}
	t.Logf("no stale progress notification in %d trials", trials)
}
