package watcherctx

// nonissues/k8s-etcd3-watcher-gap-after-cancel.md (found by etcd-grove-81's review of k8s 7f-5a-D,
// 2026-11-14): after the watch's context is cancelled (Stop(), or the caller's ctx), queueEvent
// (watcher.go:827-834) drops an event when its select picks ctx.Done(), and startWatching goes on
// queueing the next ones (watcher.go:514-536); serialProcessEvents and sendEvent
// (watcher.go:556-574, 813-825) pick between ctx.Done() and progress at random too. So the consumer
// can receive event k+1 without event k.
//
// The fake Watcher delivers one response of n create events (consecutive revisions, the shape of an
// etcd catch-up batch) after the watch's context is done: the real client can do so (client/v3
// watch.go serveSubstream: select between `outc <- *curWr` and `<-initReq.ctx.Done()`). Copy into
// examples/premisefix/watcherctx (package watcherctx: noCompactor, identity).

import (
	"context"
	"fmt"
	"strconv"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"k8s.io/apimachinery/pkg/api/meta"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
	"k8s.io/apimachinery/pkg/apis/meta/v1/unstructured"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/etcd3"
	utilfeature "k8s.io/apiserver/pkg/util/feature"
)

var bigStr = string(make([]byte, 0)) + func() string {
	b := make([]byte, 1<<16)
	for i := range b {
		b[i] = 'a' + byte(i%26)
	}
	return string(b)
}()

type lateWatcher struct {
	got chan struct{}
	first, n int
	post     chan int
}

func mkEvs(from, n int) []*clientv3.Event { return mkEvsD(from, n, bigStr) }

func mkEvsD(from, n int, data string) []*clientv3.Event {
	var evs []*clientv3.Event
	for i := 0; i < n; i++ {
		rev := int64(from + i)
		name := fmt.Sprintf("o%05d", rev)
		val := fmt.Sprintf(`{"apiVersion":"v1","kind":"Obj","metadata":{"name":%q},"data":%q}`, name, data)
		evs = append(evs, &clientv3.Event{Type: mvccpb.PUT, Kv: &mvccpb.KeyValue{
			Key: []byte("/registry/objs/" + name), Value: []byte(val),
			CreateRevision: rev, ModRevision: rev, Version: 1}})
	}
	return evs
}

// Watch: single-event responses (revisions 6, 7, ...) paced so that the processing goroutine keeps
// up, until the watch's context is done; then one more response of n events (a buffered response
// the real client may still deliver after the context is done: serveSubstream's select).
func (f *lateWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	ch := make(chan clientv3.WatchResponse)
	go func() {
		rev := 6
		for ctx.Err() == nil {
			select {
			case ch <- clientv3.WatchResponse{Events: mkEvs(rev, 1)}:
				rev++
			case <-ctx.Done():
				continue
			}
			if rev > 7 {
				select {
				case <-f.got:
				case <-ctx.Done():
				}
			}
		}
		f.post <- rev
		ch <- clientv3.WatchResponse{Events: mkEvsD(rev, f.n, "x")}
		close(ch)
	}()
	return ch
}
func (*lateWatcher) RequestProgress(ctx context.Context) error { return nil }
func (*lateWatcher) Close() error                              { return nil }

func TestReviewGapAfterStop(t *testing.T) {
	if err := utilfeature.DefaultMutableFeatureGate.Set("ConcurrentWatchObjectDecode=false"); err != nil {
		t.Fatal(err)
	}
	const trials, n = 400, 5
	gaps, nonEmpty := 0, 0
	hist := map[int64]int{}
	defer func() { t.Logf("last-post histogram: %v", hist) }()
	example := ""
	for tr := 0; tr < trials; tr++ {
		lw := &lateWatcher{first: 30, n: n, post: make(chan int, 1), got: make(chan struct{}, 1000)}
		s2 := newStoreW(t, lw)
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		w, err := s2.Watch(ctx, "/objs/", storage.ListOptions{ResourceVersion: "5", Recursive: true, Predicate: storage.Everything})
		if err != nil {
			t.Fatal(err)
		}
		done := make(chan []int64)
		go func() {
			var rvs []int64
			for e := range w.ResultChan() {
				if e.Type == "ERROR" {
					t.Logf("error event: %v", e.Object)
					continue
				}
				m, err := meta.Accessor(e.Object)
				if err != nil {
					t.Error(err)
					continue
				}
				rv, _ := strconv.ParseInt(m.GetResourceVersion(), 10, 64)
				rvs = append(rvs, rv)
				lw.got <- struct{}{}
			}
			done <- rvs
		}()
		time.Sleep(time.Duration(20000+tr*37) * time.Microsecond)
		w.Stop()
		rvs := <-done
		cancel()
		post := <-lw.post
		if tr < 3 {
			t.Logf("trial %d: post=%d received %d, last %v", tr, post, len(rvs), rvs[max(0, len(rvs)-3):])
		}
		if len(rvs) > 0 {
			hist[rvs[len(rvs)-1]-int64(post)]++
		}
		if len(rvs) > 0 && rvs[len(rvs)-1] >= int64(post) {
			nonEmpty++
		}
		for i, rv := range rvs {
			if rv != int64(6+i) {
				gaps++
				if example == "" {
					example = fmt.Sprint(rvs)
				}
				break
			}
		}
	}
	t.Logf("%d trials: %d delivered a post-cancel event, %d with a gap (example RVs received: %s)", trials, nonEmpty, gaps, example)
	if gaps == 0 {
		t.Fatalf("no gap observed")
	}
}

func newStoreW(t *testing.T, fw clientv3.Watcher) storage.Interface {
	kc, err := kubernetes.New(clientv3.Config{Endpoints: []string{"127.0.0.1:1"}, Logger: zap.NewNop()})
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { kc.Close() })
	kc.Client.Watcher = fw
	codec := unstructured.UnstructuredJSONScheme
	versioner := storage.APIObjectVersioner{}
	newFunc := func() runtime.Object { return &unstructured.Unstructured{} }
	s, err := etcd3.New(kc, noCompactor{}, codec, newFunc, nil, nil, "/registry", "/objs",
		schema.GroupResource{Resource: "objs"}, identity{}, etcd3.NewDefaultLeaseManagerConfig(),
		etcd3.NewDefaultDecoder(codec, versioner), versioner)
	if err != nil {
		t.Fatal(err)
	}
	return s
}
