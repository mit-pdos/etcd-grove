---
upstream: known
checked: 2026-10-26
links:
  - etcd-io/etcd#22081 issue open: same bug (ka.ctxs[newIdx] for ka.ctxs[i] in closeRequireLeader), reported 2026-07-12; no maintainer review yet
  - etcd-io/etcd#22087 pr open: same fix (ctxs[i]) with a regression test, fixes #22081; marked stale 2026-10-12, not approved; upstream main still has ctxs[newIdx]
  - etcd-io/etcd#21872 pr closed: same diagnosis and fix, closed unmerged (2026-06-01)
  - etcd-io/etcd#22094 issue open: related, not this bug (closeRequireLeader leaves a keepAlives entry with no subscribers; fixes proposed in #22253, #22291, open)
---

# clientv3: `closeRequireLeader` misaligns a keep-alive's contexts with its channels

**Status**: **fixed in the fork** (2026-10-18): `ka.ctxs[i]`, with the reproduction below as a
test (`client/v3/lease_close_require_leader_test.go`, fails without the fix), on `upamanyus/etcd`
`goose-lean` as `a7bd9a16e` (in etc/goose.py's etcd pin since 8a24be2a3; upstream main
unchanged). At upstream's code: a bug (a wrong result): after the lease keep-alive stream ends
with `ErrNoLeader`, the surviving `KeepAlive` channels of a lease are paired with the wrong
contexts, so canceling a `KeepAlive` caller's context closes another caller's channel, or none.

**Where**: `client/v3/lease.go:413` (etcd fork `upamanyus/etcd` at `06aa6e6e7`, the pin of
`etc/goose.py` when found; fixed at the current pin), in `(*lessor).closeRequireLeader`:

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

**How the proof handles it**: `closeRequireLeader` is proved at the fixed pin
(`Proof/go_etcd_io/etcd/client/v3/lessor__closeRequireLeader.lean`), to safety under the lessor's
lock invariant, and the invariant now checks the alignment (2026-10-18): each keep-alive's `chs[i]`
and `ctxs[i]` are a pair `KeepAlive` registered (`kaPaired`, `kaReg`, in
`Proof/go_etcd_io/etcd/client/v3/InvLessor.lean`). The registry is a ghost map from `KeepAlive`'s
`&ctx` (the variable its wrapped context is stored in, held persistently afterwards) to the channel
it made, and a key is added only with the variable's full points-to, so the registered pairs are
`KeepAlive`'s `(ch, ctx)`. `closeRequireLeader`'s compaction must show that each pair it copies,
`(ka.chs[i], ka.ctxs[i])`, is registered (the scan's `crlPreOk`: a channel it left is `chs[i]`);
at upstream's code the pair is `(ka.chs[i], ka.ctxs[newIdx])`, which the invariant does not give
when `newIdx < i`: the proof fails there. Checked by translating the buggy line (the `ctxs` index
`i` turned back to `newIdx` in the translation, temporarily) and adapting the proof to it: one goal
is left, `kaReg γr ka.chs[i] ka.ctxs[newIdx]`, which the invariant does not give. `keepAliveCtxCloser` and `KeepAlive` keep the alignment too (same-index removal,
appends). What is still not stated: that the context `keepAliveCtxCloser` finds is its own `ctx`
(`context.Value`'s trust-boundary spec says only that it returns `nil` or some pointer), so no
spec promises "canceling `ctx` closes the channel `KeepAlive` returned for it"; `isEtcdLease`'s
`KeepAlive` promises nothing of when the channel closes.

**Possible fixes**: `ka.ctxs[i]` in place of `ka.ctxs[newIdx]`.

**Found**: 2026-10-18, reading `lease.go` for the client lease contract (`isEtcdLease`).
