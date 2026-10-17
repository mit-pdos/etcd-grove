package clientv3

import (
	"context"
	"testing"
)

// reviewSub builds a subscription the way KeepAlive does: a cancelable context
// tagged with keepAliveCtxKey (pointing at its own address), optionally with
// WithRequireLeader underneath.
func reviewSub(requireLeader bool) (chan *LeaseKeepAliveResponse, context.Context, context.CancelFunc) {
	ch := make(chan *LeaseKeepAliveResponse, 1)
	base := context.Background()
	if requireLeader {
		base = WithRequireLeader(base)
	}
	ctx, cancel := context.WithCancel(base)
	ctx = context.WithValue(ctx, keepAliveCtxKey{}, &ctx)
	return ch, ctx, cancel
}

func reviewClosed(ch chan *LeaseKeepAliveResponse) bool {
	select {
	case _, ok := <-ch:
		return !ok
	default:
		return false
	}
}

// After closeRequireLeader removes A (requires a leader), canceling B's own
// context must close B's channel, and canceling A's context must not touch B.
// With the old ka.ctxs[newIdx] B stays paired with A's context: B's closer
// misses, A's closer closes B's channel.
func TestReviewCtxCloserAfterCloseRequireLeader(t *testing.T) {
	chA, ctxA, cancelA := reviewSub(true)
	chB, ctxB, cancelB := reviewSub(false)
	ka := &keepAlive{
		chs:   []chan<- *LeaseKeepAliveResponse{chA, chB},
		ctxs:  []context.Context{ctxA, ctxB},
		donec: make(chan struct{}),
	}
	l := &lessor{keepAlives: map[LeaseID]*keepAlive{1: ka}, donec: make(chan struct{})}

	l.closeRequireLeader()
	if !reviewClosed(chA) {
		t.Fatalf("A's channel not closed")
	}

	// A's subscriber goes away first: its closer must leave B alone.
	cancelA()
	l.keepAliveCtxCloser(ctxA, 1, ka.donec)
	if reviewClosed(chB) {
		t.Errorf("canceling A's context closed B's channel")
	}
	// B's subscriber goes away: its closer must close B's channel and drop the entry.
	cancelB()
	l.keepAliveCtxCloser(ctxB, 1, ka.donec)
	if !reviewClosed(chB) {
		t.Errorf("canceling B's context did not close B's channel")
	}
	if _, ok := l.keepAlives[1]; ok {
		t.Errorf("entry left after its last subscriber was canceled: %+v", l.keepAlives[1])
	}
}

// #22094 at the PR head: an all-require-leader entry is left empty in the map.
// A cancelable subscriber's closer later reaps it (len(ka.chs)==0); a
// subscriber whose context has no Done channel (WithRequireLeader(Background),
// the documented use) has no closer, so the entry stays.
func TestReviewOrphanReapedOnlyByCtxCloser(t *testing.T) {
	// Cancelable: reaped by keepAliveCtxCloser.
	chA, ctxA, cancelA := reviewSub(true)
	ka := &keepAlive{chs: []chan<- *LeaseKeepAliveResponse{chA}, ctxs: []context.Context{ctxA}, donec: make(chan struct{})}
	l := &lessor{keepAlives: map[LeaseID]*keepAlive{1: ka}, donec: make(chan struct{})}
	l.closeRequireLeader()
	_, orphan := l.keepAlives[1]
	t.Logf("cancelable: orphan entry after closeRequireLeader: %v", orphan)
	cancelA()
	l.keepAliveCtxCloser(ctxA, 1, ka.donec)
	_, still := l.keepAlives[1]
	t.Logf("cancelable: entry after its context's closer ran: %v", still)

	// Not cancelable: nothing reaps it.
	ch := make(chan *LeaseKeepAliveResponse, 1)
	ctx := WithRequireLeader(context.Background())
	if ctx.Done() != nil {
		t.Fatalf("expected a context with no Done channel")
	}
	ka2 := &keepAlive{chs: []chan<- *LeaseKeepAliveResponse{ch}, ctxs: []context.Context{ctx}, donec: make(chan struct{})}
	l2 := &lessor{keepAlives: map[LeaseID]*keepAlive{2: ka2}, donec: make(chan struct{})}
	l2.closeRequireLeader()
	if e, ok := l2.keepAlives[2]; ok {
		t.Errorf("orphan entry with no subscription left in the map (no closer will reap it): chs=%d ctxs=%d", len(e.chs), len(e.ctxs))
	}
}
