// Package watcherctx checks the claims of k8s 7f-5's trusted texts (notes/k8s-7f5-scope.md §4) at
// the pins (go1.27.3; k8s.io/apiserver 9c4ec15b8038; etcd's fork 0b50f0426):
//
//   - T5-b, the APF initialization-signal key. The etcd3 store's Watch calls
//     utilflowcontrol.WatchInitialized(ctx) (watcher.go:158) on the caller's goroutine, which reads
//     ctx.Value(priorityAndFairnessInitializationSignalKey) and, if the value is a non-nil
//     InitializationSignal, calls its Signal() (apf_context.go:42-53). No premise of the store's
//     specs before 7f-5 says anything of that key (k8sctx.k8sCtxOk: audit, utiltrace, runtime/trace,
//     grpc's and otel's keys). TestWatchInitializedKeyPanics and TestWatchInitializedForeignSignal:
//     a context meeting every other fact but panicking at the key, or holding a foreign signal whose
//     Signal panics, makes Watch panic. TestWatchStrictControl: a context answering nil at the key
//     (the new fact, k8sctx.k8sCtxOk's fourth key with flowcontrol.initSignalRes) and panicking at
//     every key the store's watch path is not known to read does not make Watch panic; the context
//     the client's Watch receives carries the caller's outgoing metadata plus hasleader.
//     TestWatchInitializedRealSignal: APF's own signal (excluded by Q3's narrow choice, admitted by
//     Go) does not panic either.
//   - T5-a, WithRequireLeader (translated, Q2; requireleader_test.go).
//   - T5-c, the feature gate's Set(s=true) and the restated environment assumption (one Set per
//     feature, before any Enabled; featuregate_test.go).
//
// Run: cd examples/premisefix/watcherctx && GOWORK=off GOTOOLCHAIN=go1.27.3 go test -count=1 -v .
package watcherctx

import (
	"context"
	"fmt"
	"strings"
	"sync"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/kubernetes"
	"go.uber.org/zap"
	"google.golang.org/grpc/metadata"
	"k8s.io/apimachinery/pkg/apis/meta/v1/unstructured"
	"k8s.io/apimachinery/pkg/runtime"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apimachinery/pkg/util/wait"
	"k8s.io/apiserver/pkg/storage"
	"k8s.io/apiserver/pkg/storage/etcd3"
	"k8s.io/apiserver/pkg/storage/value"
	utilflowcontrol "k8s.io/apiserver/pkg/util/flowcontrol"
)

// The keys by their dynamic types (the APF key's and grpc's types are unexported).
const (
	apfKeyType      = "flowcontrol.priorityAndFairnessKeyType"
	mdOutgoingType  = "metadata.mdOutgoingKey"
	cancelCtxKeyTyp = "*int" // context's &cancelCtxKey
)

func keyType(k any) string { return fmt.Sprintf("%T", k) }

// keyPanicCtx answers as its parent except at keys of the listed types, where Value panics.
type keyPanicCtx struct {
	context.Context
	panicAt map[string]bool
}

func (c keyPanicCtx) Value(k any) any {
	if c.panicAt[keyType(k)] {
		panic("Value at " + keyType(k))
	}
	return c.Context.Value(k)
}

// strictCtx answers as its parent at the keys the facts cover (grpc's outgoing metadata, context's
// cancelCtxKey) and nil at the APF key, and panics at every other key: a context that meets the
// facts and nothing more.
type strictCtx struct{ context.Context }

func (c strictCtx) Value(k any) any {
	switch keyType(k) {
	case mdOutgoingType, cancelCtxKeyTyp:
		return c.Context.Value(k)
	case apfKeyType:
		return nil
	}
	panic("Value at an uncovered key " + keyType(k))
}

// panicSignal is a foreign InitializationSignal whose Signal panics.
type panicSignal struct{}

func (panicSignal) Signal() { panic("Signal") }
func (panicSignal) Wait()   {}

// fakeWatcher is a clientv3.Watcher that records the context of each Watch and returns a channel
// closed when that context is done.
type fakeWatcher struct {
	mu   sync.Mutex
	ctxs []context.Context
}

func (f *fakeWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	f.mu.Lock()
	f.ctxs = append(f.ctxs, ctx)
	f.mu.Unlock()
	ch := make(chan clientv3.WatchResponse)
	go func() { <-ctx.Done(); close(ch) }()
	return ch
}
func (*fakeWatcher) RequestProgress(ctx context.Context) error { return nil }
func (*fakeWatcher) Close() error                              { return nil }

func (f *fakeWatcher) last() context.Context {
	for i := 0; i < 200; i++ {
		f.mu.Lock()
		n := len(f.ctxs)
		var c context.Context
		if n > 0 {
			c = f.ctxs[n-1]
		}
		f.mu.Unlock()
		if c != nil {
			return c
		}
		time.Sleep(5 * time.Millisecond)
	}
	return nil
}

type identity struct{}

func (identity) TransformFromStorage(ctx context.Context, data []byte, dataCtx value.Context) ([]byte, bool, error) {
	return data, false, nil
}
func (identity) TransformToStorage(ctx context.Context, data []byte, dataCtx value.Context) ([]byte, error) {
	return data, nil
}

type noCompactor struct{}

func (noCompactor) CompactRevision() int64 { return 0 }

// newStore makes an etcd3 store over a kubernetes client whose Watcher is fw (the client never
// dials: the watch path with a positive resource version reaches only the Watcher).
func newStore(t *testing.T, fw *fakeWatcher) storage.Interface {
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

// watchOpts: a recursive watch from resource version 5 (no initial list, no feature gate read
// before WatchInitialized; areInitialEventsRequired reads WatchList only with RV 0).
var watchOpts = storage.ListOptions{ResourceVersion: "5", Recursive: true, Predicate: storage.Everything}

func panics(f func()) (msg string, p bool) {
	defer func() {
		if r := recover(); r != nil {
			msg, p = fmt.Sprint(r), true
		}
	}()
	f()
	return "", false
}

func TestWatchInitializedKeyPanics(t *testing.T) {
	fw := &fakeWatcher{}
	s := newStore(t, fw)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	bad := keyPanicCtx{Context: ctx, panicAt: map[string]bool{apfKeyType: true}}
	msg, p := panics(func() { s.Watch(bad, "/objs/", watchOpts) })
	if !p || !strings.Contains(msg, apfKeyType) {
		t.Fatalf("Watch over a context panicking at the APF key: panicked %v (%q); want a panic there", p, msg)
	}
	t.Logf("Watch panics: %s", msg)
}

func TestWatchInitializedForeignSignal(t *testing.T) {
	fw := &fakeWatcher{}
	s := newStore(t, fw)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	bad := utilflowcontrol.WithInitializationSignal(ctx, panicSignal{})
	msg, p := panics(func() { s.Watch(bad, "/objs/", watchOpts) })
	if !p || msg != "Signal" {
		t.Fatalf("Watch with a foreign signal: panicked %v (%q); want Signal's panic", p, msg)
	}
}

func TestWatchInitializedRealSignal(t *testing.T) {
	fw := &fakeWatcher{}
	s := newStore(t, fw)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	sig := utilflowcontrol.NewInitializationSignal()
	w, err := s.Watch(utilflowcontrol.WithInitializationSignal(ctx, sig), "/objs/", watchOpts)
	if err != nil {
		t.Fatal(err)
	}
	sig.Wait() // Signal was called: Wait returns
	w.Stop()
	for range w.ResultChan() {
	}
}

func TestWatchStrictControl(t *testing.T) {
	fw := &fakeWatcher{}
	s := newStore(t, fw)
	base, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()
	base = metadata.NewOutgoingContext(base, metadata.Pairs("caller", "x"))
	for _, ctx := range []context.Context{strictCtx{base}, strictCtx{context.Background()}} {
		w, err := s.Watch(ctx, "/objs/", watchOpts)
		if err != nil {
			t.Fatal(err)
		}
		got := fw.last()
		if got == nil {
			t.Fatal("the client's Watch was not called")
		}
		md, ok := metadata.FromOutgoingContext(got)
		if !ok || len(md.Get("hasleader")) != 1 || md.Get("hasleader")[0] != "true" {
			t.Fatalf("the client's context's outgoing metadata %v: want hasleader=true", md)
		}
		if ctx.(strictCtx).Context == base && (len(md.Get("caller")) != 1 || md.Get("caller")[0] != "x") {
			t.Fatalf("the caller's outgoing metadata is lost: %v", md)
		}
		w.Stop()
		for range w.ResultChan() {
		}
	}
}

// T5-d: wait.Jitter(d, f) (apimachinery pkg/util/wait/wait.go:92) returns a duration in
// [d, d + f*d] for f > 0 (d for f <= 0 replaced by f = 1): "some duration", what the local spec says.
func TestJitter(t *testing.T) {
	for i := 0; i < 1000; i++ {
		j := wait.Jitter(time.Second, 3)
		if j < time.Second || j > 4*time.Second {
			t.Fatalf("Jitter(1s, 3) = %v", j)
		}
	}
}
