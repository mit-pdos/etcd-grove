// Review tests for etcd-io/etcd#21126 (closeRequireLeader). Copy into client/v3 and run:
//   go test -run 'TestReview21126' -count=1 -v .
package clientv3

import (
	"context"
	"testing"
	"time"
)

// subscribe registers a subscription the way KeepAlive does (without the network).
func reviewSubscribe(l *lessor, id LeaseID, ctx context.Context) (chan *LeaseKeepAliveResponse, context.Context) {
	ch := make(chan *LeaseKeepAliveResponse, LeaseResponseChSize)
	if ctx.Done() != nil {
		ctx = context.WithValue(ctx, keepAliveCtxKey{}, &ctx)
	}
	l.mu.Lock()
	ka, ok := l.keepAlives[id]
	if !ok {
		ka = &keepAlive{chs: []chan<- *LeaseKeepAliveResponse{ch}, ctxs: []context.Context{ctx},
			deadline: time.Now().Add(time.Hour), nextKeepAlive: time.Now(), donec: make(chan struct{})}
		l.keepAlives[id] = ka
	} else {
		ka.chs = append(ka.chs, ch)
		ka.ctxs = append(ka.ctxs, ctx)
	}
	l.mu.Unlock()
	if ctx.Done() != nil {
		go l.keepAliveCtxCloser(ctx, id, ka.donec)
	}
	return ch, ctx
}

func reviewLessor() *lessor {
	return &lessor{keepAlives: make(map[LeaseID]*keepAlive), donec: make(chan struct{})}
}

func isClosed(ch chan *LeaseKeepAliveResponse) bool {
	select {
	case _, ok := <-ch:
		return !ok
	default:
		return false
	}
}

// Mixed lease [require-leader, plain]: after one leader loss the plain subscriber must stay
// paired with its own context, so a second leader loss must not close it.
// Fails on the base (ctxs[newIdx] bug, etcd#22081), passes on the PR head.
func TestReview21126MixedSecondLeaderLoss(t *testing.T) {
	l := reviewLessor()
	defer close(l.donec)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	rl, _ := reviewSubscribe(l, 1, WithRequireLeader(ctx))
	plain, _ := reviewSubscribe(l, 1, ctx)
	l.closeRequireLeader()
	if !isClosed(rl) || isClosed(plain) {
		t.Fatal("first leader loss: expected only the require-leader channel closed")
	}
	l.closeRequireLeader()
	if isClosed(plain) {
		t.Fatal("second leader loss closed the plain subscriber (ctx/ch mispairing)")
	}
}

// Mixed lease [require-leader, plain]: canceling the plain subscriber's ctx must close its channel.
// With the bug, keepAliveCtxCloser looks for its ctx in ka.ctxs, which holds the require-leader ctx.
func TestReview21126MixedCancelPlain(t *testing.T) {
	l := reviewLessor()
	defer close(l.donec)
	rctx, rcancel := context.WithCancel(context.Background())
	defer rcancel()
	pctx, pcancel := context.WithCancel(context.Background())
	_, _ = reviewSubscribe(l, 1, WithRequireLeader(rctx))
	plain, _ := reviewSubscribe(l, 1, pctx)
	l.closeRequireLeader()
	pcancel()
	deadline := time.Now().Add(2 * time.Second)
	for !isClosed(plain) {
		if time.Now().After(deadline) {
			t.Fatal("plain subscriber's channel not closed after its ctx was canceled")
		}
		time.Sleep(10 * time.Millisecond)
	}
	l.mu.Lock()
	_, ok := l.keepAlives[1]
	l.mu.Unlock()
	if ok {
		t.Fatal("entry left with no subscriber after the last one was canceled")
	}
}

// All subscriptions require a leader: the entry must leave keepAlives (else sendKeepAliveLoop
// keeps renewing the lease). Fails on the base, passes on the PR head.
func TestReview21126AllRequireLeaderDeleted(t *testing.T) {
	l := reviewLessor()
	defer close(l.donec)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	a, _ := reviewSubscribe(l, 1, WithRequireLeader(ctx))
	b, _ := reviewSubscribe(l, 1, WithRequireLeader(ctx))
	l.closeRequireLeader()
	if !isClosed(a) || !isClosed(b) {
		t.Fatal("require-leader channels not closed")
	}
	l.mu.Lock()
	_, ok := l.keepAlives[1]
	l.mu.Unlock()
	if ok {
		t.Fatal("entry with no subscribers left in keepAlives")
	}
}

// The delete path does not close ka.donec: the old subscriptions' keepAliveCtxCloser goroutines
// stay blocked until their ctx ends. A new KeepAlive on the same lease id in the meantime gets a
// fresh entry; the old closers, when their ctx ends, must not touch it. Passes on the PR head
// (shows the leftover goroutine is harmless to the new entry).
func TestReview21126DeletedThenResubscribe(t *testing.T) {
	l := reviewLessor()
	defer close(l.donec)
	oldCtx, oldCancel := context.WithCancel(context.Background())
	_, _ = reviewSubscribe(l, 1, WithRequireLeader(oldCtx))
	l.closeRequireLeader()
	newCtx, newCancel := context.WithCancel(context.Background())
	defer newCancel()
	fresh, _ := reviewSubscribe(l, 1, newCtx)
	oldCancel() // the old closer wakes up, finds the fresh entry, matches nothing
	time.Sleep(100 * time.Millisecond)
	if isClosed(fresh) {
		t.Fatal("old closer closed the fresh subscription")
	}
	l.mu.Lock()
	ka, ok := l.keepAlives[1]
	n := 0
	if ok {
		n = len(ka.chs)
	}
	l.mu.Unlock()
	if !ok || n != 1 {
		t.Fatalf("fresh entry disturbed: present=%v subs=%d", ok, n)
	}
}
