package watcherctx

// k8s 7f-5a-D (notes/k8s-7f5a-draft.md §4): the Go evidence for the trusted texts the Draft of the
// etcd3 watcher needs.
//
// T5-e: WithRequireLeader's axiom gains "isContext ctx s -∗ isContext c s": over a parent with
// Perennial's context model (a *cancelCtx/*timerCtx chain, possibly under *valueCtx links), the
// result has the parent's Deadline, Done channel, Err (Canceled or DeadlineExceeded, the same value
// once done), Cause, and parentCancelCtx(c) finds the parent's *cancelCtx (isContext's HParentCC):
// WithCancel(c)'s child is registered in the parent's children and cancelled synchronously with it,
// not through propagateCancel's goroutine. TestIsContextCheckDetects shows the synchronous check
// fails on a wrapper whose Done is not the parent's.
//
// T5-f: the leaf trust-boundary specs the watcher reaches (no-op specs in the existing pattern):
// metrics.RecordEtcdEvent/RecordEtcdBookmark (return, for valid UTF-8 labels; panic on invalid
// ones once registered, as RecordEtcdRequest's premise records), mvccpb.Event_EventType.String
// (returns for every value), klog.Warningf (returns).

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3/metrics"
	"k8s.io/klog/v2"
)

type t5eKey struct{}

// The parents with Perennial's context model (isContext): cancel and timer contexts, possibly under
// value links, as the driver's WithTimeout(Background()).
func t5eParents() map[string]func() (context.Context, context.CancelFunc) {
	return map[string]func() (context.Context, context.CancelFunc){
		"cancel": func() (context.Context, context.CancelFunc) {
			return context.WithCancel(context.Background())
		},
		"timeout": func() (context.Context, context.CancelFunc) {
			return context.WithTimeout(context.Background(), time.Hour)
		},
		"deadline": func() (context.Context, context.CancelFunc) {
			return context.WithDeadline(context.Background(), time.Now().Add(time.Hour))
		},
		"value-over-timeout": func() (context.Context, context.CancelFunc) {
			c, cancel := context.WithTimeout(context.Background(), time.Hour)
			return context.WithValue(c, t5eKey{}, 1), cancel
		},
		"cancelcause": func() (context.Context, context.CancelFunc) {
			c, cancel := context.WithCancelCause(context.Background())
			return c, func() { cancel(errors.New("cause")) }
		},
	}
}

// syncPropagates reports whether WithCancel(c)'s child is done as soon as cancel returns (the
// child is in a *cancelCtx's children map: parentCancelCtx(c) succeeded).
func syncPropagates(c context.Context, cancel context.CancelFunc) bool {
	child, cc := context.WithCancel(c)
	defer cc()
	cancel()
	return child.Err() != nil
}

func TestWithRequireLeaderIsContext(t *testing.T) {
	for name, mk := range t5eParents() {
		for i := 0; i < 200; i++ {
			p, cancel := mk()
			c := clientv3.WithRequireLeader(p)
			pd, pok := p.Deadline()
			cdl, cok := c.Deadline()
			if pd != cdl || pok != cok {
				t.Fatalf("%s: Deadline differs: %v,%v vs %v,%v", name, pd, pok, cdl, cok)
			}
			if p.Done() != c.Done() {
				t.Fatalf("%s: Done channel differs", name)
			}
			if c.Err() != nil {
				t.Fatalf("%s: Err before cancel: %v", name, c.Err())
			}
			if !syncPropagates(c, cancel) {
				t.Fatalf("%s: WithCancel(c)'s child not cancelled synchronously: parentCancelCtx(c) failed", name)
			}
			if c.Err() != p.Err() || !(errors.Is(c.Err(), context.Canceled) || errors.Is(c.Err(), context.DeadlineExceeded)) {
				t.Fatalf("%s: Err after cancel: %v vs parent's %v", name, c.Err(), p.Err())
			}
			if context.Cause(c) != context.Cause(p) {
				t.Fatalf("%s: Cause differs", name)
			}
		}
	}
}

// otherDone wraps a context with a Done channel of its own, closed by a goroutine when the
// parent's is: parentCancelCtx of it fails (its Done is not the *cancelCtx's).
type otherDone struct {
	context.Context
	ch chan struct{}
}

func (o *otherDone) Done() <-chan struct{} { return o.ch }

func TestIsContextCheckDetects(t *testing.T) {
	misses := 0
	for i := 0; i < 200; i++ {
		p, cancel := context.WithCancel(context.Background())
		o := &otherDone{Context: p, ch: make(chan struct{})}
		go func() { <-p.Done(); close(o.ch) }()
		child, cc := context.WithCancel(o)
		cancel()
		if child.Err() == nil {
			misses++
		}
		cc()
	}
	if misses == 0 {
		t.Fatalf("the synchronous-propagation check never failed on a wrapper with its own Done")
	}
	t.Logf("not synchronous in %d of 200 trials (the check detects it)", misses)
}

func TestRecordEtcdEventBookmarkLabels(t *testing.T) {
	metrics.Register()
	good := schema.GroupResource{Group: "", Resource: "pods"}
	run := func(f func()) (p any) {
		defer func() { p = recover() }()
		f()
		return nil
	}
	if p := run(func() { metrics.RecordEtcdEvent(good); metrics.RecordEtcdBookmark(good) }); p != nil {
		t.Fatalf("valid labels panicked: %v", p)
	}
	bad := schema.GroupResource{Group: "\xff", Resource: "pods"}
	pe := run(func() { metrics.RecordEtcdEvent(bad) })
	pb := run(func() { metrics.RecordEtcdBookmark(bad) })
	t.Logf("invalid UTF-8 label: RecordEtcdEvent panic=%v, RecordEtcdBookmark panic=%v", pe != nil, pb != nil)
}

func TestEventTypeStringReturns(t *testing.T) {
	for _, v := range []mvccpb.Event_EventType{mvccpb.PUT, mvccpb.DELETE, 2, 7, -1} {
		if s := v.String(); s == "" {
			t.Fatalf("String of %d is empty", v)
		}
	}
}

func TestKlogWarningfReturns(t *testing.T) {
	klog.Warningf("watch chan error: %v", errors.New("mvcc: required revision has been compacted"))
}
