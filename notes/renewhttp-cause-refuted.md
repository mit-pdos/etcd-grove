# `leasehttp.RenewHTTP.spec` and `EtcdServer.leaseTimeToLive.spec` refuted: `context.Cause` (2026-11-13, k8s 7f-4 Addendum T-k)

Found by the T-j axiom review (etcd-grove-81's workflow `wf_34700c38-af3`, finding MAJ-1; its test
`/shared/tmp/coord-81/tj-review/cause/causecx/cause_test.go`); `leaseTimeToLive` added by the sweep
etcd-grove-81 asked for.

**Reach.** Two landed trust-boundary axioms whose Go code sends an HTTP request with the caller's
context over a `*http.Transport`:
- `leasehttp.RenewHTTP.wp_proof` (`Spec/go_etcd_io/etcd/server/v3/lease/leasehttp/RenewHTTP.lean`):
  premise `isContext` until T-f, `srvCtxWeak` until T-j, now `v3rpc.ctxDoneErr`; post: `nil` or
  `applyErrIs err`.
- `EtcdServer.leaseTimeToLive.wp_proof` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`):
  premise `isContext ctx cd ∗ http.netCtxOk ctx`; claims no panic.

net/http's `Transport.roundTrip` works on `ctx, cancel := context.WithCancelCause(req.Context())`
(go1.27.3 `net/http/transport.go:675`) and, once that context is done, returns `context.Cause(ctx)`
(`:698`); `http.Client.Do` wraps it in a `*url.Error`. The transport's child gets its cause from the
request's context: `Cause(parent)` in `propagateCancel`'s already-done arm, or the found parent
`*cancelCtx`'s `cause` when that one is cancelled (`context.go:485-488, 492-506`, and `cancel`, `:550`). No
predicate of the premises constrains a context's cause: Perennial's `isCancelCtx` lock invariant holds
`cause : GoError` with no fact (`Perennial/Proof/context/Base.lean`, `cancelCtxLockInv`), T-j's
`madeCancelCtx` says nothing of stored errors, and Perennial's `context.WithDeadlineCause.spec` gives
`isContext` of a context with any program `cause`. So:
- `RenewHTTP` over `WithDeadlineCause(Background(), d, badErr{})` (an `isContext`, so a `ctxDoneErr`;
  `netCtxOk` from the chain laws) returns a `*url.Error` wrapping `badErr{}`, which `applyErrIs` claims
  is walkable by `errors.Is` without a panic; `badErr.Is` panics, and so does `LeaseRenew`'s
  `errors.Is(err, lease.ErrLeaseNotFound)` on it.
- `leaseTimeToLive` on a follower calls `errors.Is(err, lease.ErrLeaseNotFound)` itself on
  `TimeToLiveHTTP`'s error (fork `673da07c8f` `server/etcdserver/v3_server.go:686`): with the same
  context, and the deadline firing while the leader's lease handler blocks, it panics inside the axiom.

Closed theorems: none is affected in substance. grpc v1.84.0, the fork's server, api and pkg code and
the verified k8s code never make a context with a custom cause (`WithCancelCause`, `WithDeadlineCause`,
`WithTimeoutCause`: none; `context.Cause` is called only by client-go's `WaitFor` and
`WaitForCacheSyncWithContext`, which have no spec), so etcd's contexts carry only context errors as
causes. But the axioms as stated are false.

**The Go tests** (go1.27.3, GOWORK=off):
- `TestRenewHTTPCausePanics` (`examples/premisefix/streamctx/streamctx_test.go`; the review's test):
  past the deadline and with the deadline firing mid-call, `RenewHTTP` returns a `*url.Error` whose
  `Err` is the cause, and `errors.Is(err, lease.ErrLeaseNotFound)` panics (`causeBadErr.Is called`).
- `TestLeaseTimeToLiveFollowerCausePanics` (`examples/etcd/lease/ctxsweep_test.go`): a three-member
  cluster whose leader's lease handler blocks; a follower's `LeaseTimeToLive` over
  `WithDeadlineCause(Background(), now+500ms, causeBadErr{})` panics.

**The fix**: Addendum T-k of `notes/k8s-7f4-freeze.md` (for etcd-grove-81's axiom review).
