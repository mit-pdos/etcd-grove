# `EtcdServer.leaseTimeToLive.spec` refuted: `Value` at net/http's keys (2026-11-13, k8s 7f-4 Addendum T-h6)

Found by etcd-grove-81's context-key sweep (the class of `notes/renewhttp-value-refuted.md`).

**Reach.** The landed trust-boundary axiom `EtcdServer.leaseTimeToLive.wp_proof`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`) takes
`context.isContext ctx cd`, which specifies `ctx.Value` only at `&cancelCtxKey`. On a follower
(`v3_server.go:671-682`) it runs `cctx := context.WithTimeout(ctx, ReqTimeout)` and
`leasehttp.TimeToLiveHTTP(cctx, ...)`, which sends the request over a `*http.Transport`; its
`roundTrip` calls `httptrace.ContextClientTrace(cctx)` (go1.27.3 `net/http/transport.go:614`), a
`Value` call the `*timerCtx` passes on to `ctx`. A context whose `Value` panics at `httptrace`'s
`clientEventContextKey{}`, and delegates everything else to a real `WithCancel` child, meets the
premise, and the call panics; a non-nil value at that key or at the two `nettrace` keys runs the
caller's hooks or resolver. Closed theorems reaching it: those whose collections list the axiom
(`etc/tcb-report.py --roots`); grpc's run contexts hold no such values, so no closed theorem's program
exercises the gap, but the axiom as stated is false.

**The Go test.** `TestLeaseTimeToLiveFollowerValuePanics` (`examples/etcd/lease/ctxsweep_test.go`):
a three-member cluster, `LeaseTimeToLive` on a follower with `sweepPanicTraceCtx` panics with
`Value(httptrace key)`; with the plain context it returns `lease not found`.

**The fix** (decided by etcd-grove-81, 2026-11-13; branch `k8s-7f4`, Addendum T-h6 of
`notes/k8s-7f4-freeze.md`): the premise gains `http.netCtxOk ctx` (`Proof/net/http/NetCtx.lean`: `nil` at
the three keys), as `RenewHTTP`'s; `EtcdServer.LeaseTimeToLive.spec`, the contract `v3rpc.lessorTTLOk`
and `v3rpc.LeaseServer.LeaseTimeToLive.spec` carry it, and grpc's trusted run context `grpcRunCtx`
gives it (`netCtxOk_of_runCtx`).
