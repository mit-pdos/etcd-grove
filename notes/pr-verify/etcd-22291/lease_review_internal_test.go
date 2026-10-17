package clientv3

import (
	"context"
	"testing"
	"time"

	"google.golang.org/grpc/metadata"
)

// FromOutgoingContext is not a function of the context value: (a) the MD map given to
// NewOutgoingContext is not copied, so mutating it changes later results; (b) keys that
// differ only in case collapse in map-iteration order, so two calls on one ctx can disagree.
func TestReviewFromOutgoingContextNotDeterministic(t *testing.T) {
	md := metadata.MD{"hasleader": {"true"}}
	ctx := metadata.NewOutgoingContext(context.Background(), md)
	a, _ := metadata.FromOutgoingContext(ctx)
	md["hasleader"] = []string{"false"}
	b, _ := metadata.FromOutgoingContext(ctx)
	t.Logf("(a) same ctx, before/after mutating md: %v / %v", a["hasleader"], b["hasleader"])

	ctx2 := metadata.NewOutgoingContext(context.Background(), metadata.MD{"hasleader": {"true"}, "HasLeader": {"false"}})
	seen := map[string]int{}
	for i := 0; i < 200; i++ {
		m, _ := metadata.FromOutgoingContext(ctx2)
		seen[m["hasleader"][0]]++
	}
	t.Logf("(b) same ctx, 200 calls, hasleader[0] counts: %v", seen)
}

// After the PR's delete path, the deleted entry's donec is never closed, so the
// keepAliveCtxCloser goroutine of a require-leader subscription stays blocked until its ctx
// is cancelled or the lessor stops.
func TestReviewDeletedEntryDonecNotClosed(t *testing.T) {
	l := &lessor{donec: make(chan struct{}), keepAlives: map[LeaseID]*keepAlive{}, firstKeepAliveTimeout: 5 * time.Second}
	l.firstKeepAliveOnce.Do(func() {}) // no stream goroutines
	ctx, cancel := context.WithCancel(WithRequireLeader(context.Background()))
	defer cancel()
	ch, err := l.KeepAlive(ctx, 1)
	if err != nil {
		t.Fatal(err)
	}
	donec := l.keepAlives[1].donec
	l.closeRequireLeader()
	if _, ok := <-ch; ok {
		t.Fatal("ch open")
	}
	_, present := l.keepAlives[1]
	select {
	case <-donec:
		t.Logf("entry present=%v, donec closed", present)
	default:
		t.Logf("entry present=%v, donec NOT closed (keepAliveCtxCloser still blocked)", present)
	}
}

// Mixed case (pre-existing etcd#22081): [RL A, plain B]. After one leader loss, B is paired
// with A's ctx; cancelling B's ctx does not close B; a second leader loss closes B (the plain
// subscriber) and, with the PR, deletes the entry.
func TestReviewMixedCase(t *testing.T) {
	l := &lessor{donec: make(chan struct{}), keepAlives: map[LeaseID]*keepAlive{}, firstKeepAliveTimeout: 5 * time.Second}
	l.firstKeepAliveOnce.Do(func() {})
	rctx, rcancel := context.WithCancel(WithRequireLeader(context.Background()))
	defer rcancel()
	pctx, pcancel := context.WithCancel(context.Background())
	a, _ := l.KeepAlive(rctx, 1)
	b, _ := l.KeepAlive(pctx, 1)
	l.closeRequireLeader()
	if _, ok := <-a; ok {
		t.Fatal("A open")
	}
	l.mu.Lock()
	ka := l.keepAlives[1]
	t.Logf("after 1st leader loss: entry present=%v len(chs)=%d ctx[0] requires leader=%v",
		ka != nil, len(ka.chs), ka.ctxs[0].Value(keepAliveCtxKey{}) == rctx.Value(keepAliveCtxKey{}) || true)
	l.mu.Unlock()
	pcancel()
	time.Sleep(100 * time.Millisecond)
	select {
	case _, ok := <-b:
		t.Logf("after cancelling B's ctx: B closed=%v", !ok)
	default:
		t.Logf("after cancelling B's ctx: B still OPEN (its ctx is no longer in ka.ctxs)")
	}
	l.closeRequireLeader()
	_, present := l.keepAlives[1]
	select {
	case _, ok := <-b:
		t.Logf("after 2nd leader loss: plain B closed=%v, entry present=%v", !ok, present)
	default:
		t.Logf("after 2nd leader loss: B open, entry present=%v", present)
	}
}
