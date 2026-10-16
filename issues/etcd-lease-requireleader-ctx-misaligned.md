---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#22081 issue open: same bug (closeRequireLeader pairs survivors with shifted contexts)
  - etcd-io/etcd#21872 pr closed: the one-line fix (`ka.ctxs[i]`), closed unmerged
  - etcd-io/etcd#22087 pr open: the same one-line fix
  - etcd-io/etcd#22094 issue open: related, a second bug of the same function (issues/etcd-lease-requireleader-orphan-entry.md)
---

# client/v3: `lessor.closeRequireLeader` pairs the surviving keep-alive channels with the wrong contexts

- **Status**: a bug, present at the pin, reproduced (below). Upstream since 2017 (`8024a0d15f`).
- **Where**: `client/v3/lease.go` at `107edf7e4` (`etc/goose.py`'s etcd pin): `closeRequireLeader`
  (lines 383-418), line 413:
  `newChs[newIdx], newCtxs[newIdx] = ka.chs[i], ka.ctxs[newIdx]` (should be `ka.ctxs[i]`).
  Its consumer `keepAliveCtxCloser` (lines 349-380) closes `ka.chs[i]` for the index `i` whose
  `ka.ctxs[i]` matches the cancelled context.
- **What happens**: when the lease stream reports `ErrNoLeader`, `recvKeepAliveLoop` calls
  `closeRequireLeader`, which closes the channels of the `KeepAlive` subscribers whose context has
  `WithRequireLeader` and compacts the two parallel slices. Once one removed subscriber precedes
  a survivor, every later survivor gets its predecessor's context (and the last survivor's context
  is lost). Afterwards, cancelling a survivor's context closes another subscriber's channel, or
  none: the canceller's channel stays open and the lease keeps being renewed for it. For a
  `concurrency.Session` whose keep-alive is such a survivor (sessions sharing a lease through
  `WithLease`, one of them with a require-leader context), `Session.Close`/`Orphan` cancel the
  session's context and then wait on `donec`, which only the keep-alive channel's close releases:
  they block until the client is closed, and the lease is never revoked.

  Reproduction at the pin (an internal test of `client/v3`,
  `issues/etcd-lease-requireleader-ctx-misaligned/close_require_leader_ctx_test.go`; it fails with
  "C's channel still open after C's context was cancelled"):

  ```go
  func TestCloseRequireLeaderCtxMisaligned(t *testing.T) {
  	l := &lessor{keepAlives: make(map[LeaseID]*keepAlive), donec: make(chan struct{})}
  	mk := func(ctx context.Context) (context.Context, chan *LeaseKeepAliveResponse) {
  		ctx = context.WithValue(ctx, keepAliveCtxKey{}, &ctx) // as KeepAlive does
  		return ctx, make(chan *LeaseKeepAliveResponse, 1)
  	}
  	ctxA, cancelA := context.WithCancel(WithRequireLeader(context.Background()))
  	ctxB, cancelB := context.WithCancel(context.Background())
  	ctxC, cancelC := context.WithCancel(context.Background())
  	defer cancelA(); defer cancelB()
  	kA, chA := mk(ctxA); kB, chB := mk(ctxB); kC, chC := mk(ctxC)
  	ka := &keepAlive{chs: []chan<- *LeaseKeepAliveResponse{chA, chB, chC},
  		ctxs: []context.Context{kA, kB, kC}, donec: make(chan struct{})}
  	l.keepAlives[1] = ka
  	l.closeRequireLeader()            // closes chA; ctxs becomes [kA, kB]
  	cancelC()
  	l.keepAliveCtxCloser(kC, 1, ka.donec) // finds no kC: closes nothing
  	select {
  	case _, ok := <-chC:
  		if !ok { return }
  	default:
  	}
  	t.Error("C's channel still open after C's context was cancelled")
  }
  ```
- **Expected**: each surviving channel keeps the context it was registered with; cancelling a
  `KeepAlive` context closes that call's channel (the `Lease.KeepAlive` documentation: the channel
  is closed when the context is canceled).
- **How the proof handles it**: the lessor is not translated (`client/v3.toml` lists no `lessor`
  function); its callers' proofs assume `isEtcdLease` (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:1121`),
  whose `KeepAlive` returns a channel of which nothing is promised (`isChanAny`, line 1140), and
  the specs are partial correctness: `Session.Close.spec` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Session__Close.lean`)
  is met by a `Close` that never returns. `notes/decisions.md`, "Leases without liveness".
- **Possible fixes**: `ka.ctxs[i]` at line 413 (#21872, #22087). Better, one slice of
  `(ch, ctx)` pairs so they cannot drift.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#22081 (`notes/bug-triage/etcd-22081.md`).
