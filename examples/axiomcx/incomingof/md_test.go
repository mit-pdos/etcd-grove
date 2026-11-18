package incomingoftest

import (
	"context"
	"errors"
	"sync"
	"testing"

	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
)

// etcd's v3rpc cancellableContext shape (interceptor.go:270-283): embeds Context, overrides Err only.
type cancellableContext struct {
	context.Context
	lock         sync.RWMutex
	cancel       context.CancelFunc
	cancelReason error
}

func newCancellableContext(parent context.Context) *cancellableContext {
	ctx, cancel := context.WithCancel(parent)
	return &cancellableContext{Context: ctx, cancel: cancel}
}

func (c *cancellableContext) Err() error {
	c.lock.RLock()
	defer c.lock.RUnlock()
	if c.cancelReason != nil {
		return c.cancelReason
	}
	return c.Context.Err()
}

// A1: the wrapper over WithCancel(ci) has ci's incoming metadata, per context.
func TestWrapperInheritsIncoming(t *testing.T) {
	for _, tok := range []string{"tokA", "tokB"} {
		ci := metadata.NewIncomingContext(context.Background(), metadata.Pairs("token", tok))
		l := newCancellableContext(ci)
		md, ok := metadata.FromIncomingContext(l)
		if !ok || md.Get("token")[0] != tok {
			t.Fatalf("wrapper lost metadata: %v %v", md, ok)
		}
		c1, cancel := context.WithCancel(ci)
		md1, _ := metadata.FromIncomingContext(c1)
		if md1.Get("token")[0] != tok {
			t.Fatalf("WithCancel lost metadata")
		}
		cancel()
		t.Logf("token %s: WithCancel child and wrapper carry it", tok)
	}
}

// A2: two *cancelCtx made in one run over parents with different metadata answer differently,
// so incomingOf is not constant on *cancelCtx values (what incomingOf_const would say).
func TestIncomingNotConstant(t *testing.T) {
	a, ca := context.WithCancel(metadata.NewIncomingContext(context.Background(), metadata.Pairs("k", "1")))
	b, cb := context.WithCancel(context.Background())
	defer ca()
	defer cb()
	_, okA := metadata.FromIncomingContext(a)
	_, okB := metadata.FromIncomingContext(b)
	if okA == okB {
		t.Fatalf("expected different answers")
	}
	t.Logf("cancelCtx over md: ok=%v; over Background: ok=%v", okA, okB)
}

// B1: the descriptions grpc gives the context errors are their Error() strings.
func TestCtxErrDescs(t *testing.T) {
	for _, e := range []error{context.Canceled, context.DeadlineExceeded} {
		s, ok := status.FromError(e)
		t.Logf("%T %q: FromError ok=%v code=%v msg=%q", e, e.Error(), ok, s.Code(), s.Message())
		if s.Message() != e.Error() {
			t.Fatalf("desc differs from Error()")
		}
	}
	// FromContextError (grpc's invoker on a done context): message kept.
	s := status.FromContextError(context.Canceled)
	t.Logf("FromContextError(Canceled): code=%v msg=%q", s.Code(), s.Message())
}

// B2: errDesc of an *errors.errorString depends on the value behind the pointer, not its type:
// two errors.New of different strings (same dynamic type) have different descriptions, and a
// user errors.New with a handler description's text has that description.
func TestErrorStringDescByCell(t *testing.T) {
	e1 := errors.New("context canceled")
	e2 := errors.New("etcdserver: mvcc: required revision is a future revision")
	d1, _ := status.FromError(e1)
	d2, _ := status.FromError(e2)
	t.Logf("%T %q / %T %q", e1, d1.Message(), e2, d2.Message())
	if d1.Message() == d2.Message() {
		t.Fatalf("same desc")
	}
	if e1 == context.Canceled {
		t.Fatalf("errors.New values are distinct pointers")
	}
}
