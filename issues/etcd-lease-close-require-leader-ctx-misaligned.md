---
upstream: unchecked
---

# clientv3: `closeRequireLeader` misaligns a keep-alive's contexts with its channels

**Status**: a bug (a wrong result): after the lease keep-alive stream ends with `ErrNoLeader`,
the surviving `KeepAlive` channels of a lease are paired with the wrong contexts, so canceling a
`KeepAlive` caller's context closes another caller's channel, or none.

**Where**: `client/v3/lease.go:413` (etcd fork `upamanyus/etcd` at `06aa6e6e7`, the pin of
`etc/goose.py`), in `(*lessor).closeRequireLeader`:

```go
newChs[newIdx], newCtxs[newIdx] = ka.chs[i], ka.ctxs[newIdx]
```

The context copied is `ka.ctxs[newIdx]` (the surviving position) instead of `ka.ctxs[i]` (the
channel's own). `closeRequireLeader` runs from `recvKeepAliveLoop` when the stream's error is
`rpctypes.ErrNoLeader`.

**What happens**: with keep-alives `[A (WithRequireLeader), B]` on one lease, `closeRequireLeader`
closes A's channel and keeps `chs = [chB]` with `ctxs = [ctxA]`. When B's context is canceled,
`keepAliveCtxCloser` does not find it and B's channel stays open (B's caller waits for the close
it was promised); if A's context is canceled later, `keepAliveCtxCloser` closes B's channel.
No double close (closing removes the entry), so no panic. Reproduction (in package `clientv3`;
fails at the pin, passes with `ka.ctxs[i]`):

```go
func TestCloseRequireLeaderKeepsContextsAligned(t *testing.T) {
	l := &lessor{donec: make(chan struct{}), keepAlives: make(map[LeaseID]*keepAlive)}
	ctxA := WithRequireLeader(context.Background()) // closed by closeRequireLeader
	ctxB, cancelB := context.WithCancel(context.Background())
	ctxB = context.WithValue(ctxB, keepAliveCtxKey{}, &ctxB) // as KeepAlive wraps it
	chA := make(chan *LeaseKeepAliveResponse, 1)
	chB := make(chan *LeaseKeepAliveResponse, 1)
	ka := &keepAlive{
		chs:   []chan<- *LeaseKeepAliveResponse{chA, chB},
		ctxs:  []context.Context{ctxA, ctxB},
		donec: make(chan struct{}),
	}
	l.keepAlives[1] = ka

	l.closeRequireLeader()

	cancelB()
	done := make(chan struct{})
	go func() { l.keepAliveCtxCloser(ctxB, 1, ka.donec); close(done) }()
	select {
	case <-done:
	case <-time.After(time.Second):
		t.Fatal("keepAliveCtxCloser did not return")
	}
	select {
	case _, ok := <-chB:
		if ok {
			t.Fatal("unexpected value on B's channel")
		}
	default:
		t.Fatalf("B's channel not closed after B's context was canceled; ka.ctxs[0] is A's context: %v",
			ka.ctxs[0] == ctxA)
	}
}
```

At the pin: `B's channel not closed after B's context was canceled; ka.ctxs[0] is A's context: true`.

**Expected**: `KeepAlive`'s documentation: the returned channel is closed when the context is
canceled (or the lease expires / the keep-alive halts); each channel with its own context.

**How the proof handles it**: not yet verified (`client/v3/lease.go` is names-only in the
translation; found while surveying it for the client lease contract, `notes/STATUS.md`, "The
client lease: survey"). `isEtcdLease`'s `KeepAlive` promises nothing of when the channel closes,
so a proof of the lessor's safety would not exclude it; a spec of the close on cancel would.

**Possible fixes**: `ka.ctxs[i]` in place of `ka.ctxs[newIdx]`.

**Found**: 2026-10-18, reading `lease.go` for the client lease contract (`isEtcdLease`).
