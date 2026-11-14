package watcherctx

// k8s 7f-5a-D (notes/k8s-7f5a-draft.md §4): the Go evidence for the trusted texts the Draft of the
// etcd3 watcher needs.
//
// T5-e: WithRequireLeader's axiom gains "□ ∀ cd, isContext ctx cd -∗ isContext c cd": over a parent
// with Perennial's context model (a *cancelCtx/*timerCtx chain, possibly under *valueCtx links, with
// or without outgoing metadata already, done or not), the result has the parent's Deadline, Done
// channel, Err (Canceled or DeadlineExceeded, the same value once done), Cause, and
// parentCancelCtx(c) succeeds, finding the parent's *cancelCtx (isContext's HParentCC). The tests
// observe the latter through a stand-in: WithCancel(c)'s child is done as soon as the parent's
// cancel returns, which holds when the child was registered in that *cancelCtx's children (and not
// through propagateCancel's goroutine). isContext itself claims no propagation to children; the
// stand-in is only how a test sees that parentCancelCtx succeeded. TestIsContextCheckDetects shows
// the stand-in fails on a wrapper whose Done is not the parent's.
//
// T5-f: the leaf trust-boundary specs the watcher reaches (no-op specs in the existing pattern):
// metrics.RecordEtcdEvent/RecordEtcdBookmark (return, for valid UTF-8 labels; panic on invalid
// ones once registered, as RecordEtcdRequest's premise records), mvccpb.Event_EventType.String
// (returns for every value, after mvccpb's init), klog.Warningf (returns, for a format whose only
// verb is %v and one error argument whose Error() returns; default klog flags, no SetLogger).

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
	"k8s.io/apimachinery/pkg/runtime/schema"
	"k8s.io/apiserver/pkg/storage/etcd3/metrics"
	"google.golang.org/grpc/metadata"
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
		// WithRequireLeader's other branch: the parent already carries outgoing metadata, which
		// it copies before adding its key.
		"metadata-over-cancel": func() (context.Context, context.CancelFunc) {
			c, cancel := context.WithCancel(context.Background())
			return metadata.AppendToOutgoingContext(c, "k", "v"), cancel
		},
		"metadata-over-timeout": func() (context.Context, context.CancelFunc) {
			c, cancel := context.WithTimeout(context.Background(), time.Hour)
			return metadata.AppendToOutgoingContext(c, "k", "v"), cancel
		},
	}
}

// The same parents, already done before WithRequireLeader: cancelled, or past their deadline.
func t5eDoneParents() map[string]func() context.Context {
	return map[string]func() context.Context{
		"precancelled": func() context.Context {
			c, cancel := context.WithCancel(context.Background())
			cancel()
			return c
		},
		"precancelled-metadata": func() context.Context {
			c, cancel := context.WithCancel(context.Background())
			cancel()
			return metadata.AppendToOutgoingContext(c, "k", "v")
		},
		"expired-deadline": func() context.Context {
			c, _ := context.WithDeadline(context.Background(), time.Now().Add(-time.Second))
			return c
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
				t.Fatalf("%s: WithCancel(c)'s child not done when the parent's cancel returned: parentCancelCtx(c) failed", name)
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

func TestWithRequireLeaderIsContextDone(t *testing.T) {
	for name, mk := range t5eDoneParents() {
		for i := 0; i < 200; i++ {
			p := mk()
			c := clientv3.WithRequireLeader(p)
			if p.Done() != c.Done() {
				t.Fatalf("%s: Done channel differs", name)
			}
			if c.Err() == nil || c.Err() != p.Err() ||
				!(errors.Is(c.Err(), context.Canceled) || errors.Is(c.Err(), context.DeadlineExceeded)) {
				t.Fatalf("%s: Err: %v vs parent's %v", name, c.Err(), p.Err())
			}
			if context.Cause(c) != context.Cause(p) {
				t.Fatalf("%s: Cause differs", name)
			}
			// propagateCancel's already-done arm: the child is done when WithCancel returns.
			child, cc := context.WithCancel(c)
			if child.Err() == nil {
				t.Fatalf("%s: WithCancel(c)'s child not done at once", name)
			}
			cc()
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
	if pe == nil || pb == nil {
		t.Fatalf("an invalid UTF-8 label did not panic (RecordEtcdEvent %v, RecordEtcdBookmark %v): the premise would not be needed", pe, pb)
	}
}

func TestEventTypeStringReturns(t *testing.T) {
	for _, v := range []mvccpb.Event_EventType{mvccpb.PUT, mvccpb.DELETE, 2, 7, -1} {
		if s := v.String(); s == "" {
			t.Fatalf("String of %d is empty", v)
		}
	}
}

// The watcher's call: the format's only verb is %v, the one argument an error whose Error() returns.
func TestKlogWarningfReturns(t *testing.T) {
	klog.Warningf("watch chan error: %v", errors.New("mvcc: required revision has been compacted"))
}
