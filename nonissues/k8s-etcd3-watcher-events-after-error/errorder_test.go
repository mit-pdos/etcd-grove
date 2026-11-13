package etcd3

// Not part of the driver: the 7f Scope's check of the etcd3 watcher's error ordering
// (notes/k8s-7f-scope.md, §2.4; nonissues/k8s-etcd3-watcher-events-after-error.md). A fake clientv3.Watcher delivers events and then an error; a slow
// consumer then reads the store's ResultChan. The watcher's sendError (from startWatching's
// goroutine) and sendEvent (from the processing goroutine) race on resultChan, so the watch.Error
// event may come before events of lower revisions, which correctness.WatchValidator rejects
// (validateMaybeLastEventError) and TestCorrectness's runWatch reports ("watch channel was not
// closed after watch.Error").

import (
	"context"
	"fmt"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/watch"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/etcd3"
)

type fakeWatcher struct{ n int }

func (f fakeWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	ch := make(chan clientv3.WatchResponse, 2)
	var evs []*clientv3.Event
	for i := 0; i < f.n; i++ {
		rev := int64(6 + i)
		o := Obj{Namespace: "ns-1", Name: fmt.Sprintf("pod-%d", i), Value: "x"}
		evs = append(evs, &clientv3.Event{Type: mvccpb.Event_PUT, Kv: &mvccpb.KeyValue{
			Key: []byte(Prefix + storeKey(o.Namespace+"/"+o.Name)), Value: encodeObj(&o),
			CreateRevision: rev, ModRevision: rev, Version: 1}})
	}
	ch <- clientv3.WatchResponse{Events: evs}
	ch <- clientv3.WatchResponse{CompactRevision: 3}
	go func() { <-ctx.Done(); close(ch) }()
	return ch
}
func (fakeWatcher) RequestProgress(ctx context.Context) error { return nil }
func (fakeWatcher) Close() error                              { return nil }

func TestErrorEventNotLast(t *testing.T) {
	kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{"127.0.0.1:1"}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	defer kc.Close()
	kc.Client.Watcher = fakeWatcher{n: 150}
	s, err := etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix,
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		decoder{}, versioner{})
	if err != nil {
		t.Fatal(err)
	}
	bad := 0
	const trials = 50
	for trial := 0; trial < trials; trial++ {
		ctx, cancel := context.WithCancel(context.Background())
		w, err := s.Watch(ctx, ResourcePrefix+"/", storage.ListOptions{ResourceVersion: rvString(5), Recursive: true,
			Predicate: storage.Everything})
		if err != nil {
			t.Fatal(err)
		}
		time.Sleep(100 * time.Millisecond) // a stalled consumer: both producers block on resultChan
		errAt, n := -1, 0
		for ev := range w.ResultChan() {
			if ev.Type == watch.Error && errAt < 0 {
				errAt = n
			}
			n++
		}
		if errAt >= 0 && errAt != n-1 {
			bad++
			if bad == 1 {
				t.Logf("trial %d: watch.Error at index %d of %d events", trial, errAt, n)
			}
		}
		cancel()
	}
	t.Logf("%d of %d trials delivered events after the watch.Error event", bad, trials)
}
