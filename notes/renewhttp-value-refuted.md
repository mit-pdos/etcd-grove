# `leasehttp.RenewHTTP.spec` refuted: `Value` at net/http's keys (2026-11-13, k8s 7f-4 Addendum T-h0)

**Reach.** The landed trust-boundary axiom `leasehttp.RenewHTTP.wp_proof`
(`Spec/go_etcd_io/etcd/server/v3/lease/leasehttp/RenewHTTP.lean`), on `lean` from its introduction
with `context.isContext ctx cd` and since T-f (2026-11-12) with `srvCtxWeak ctx cd`. Both predicates
specify `ctx.Value` only at `&cancelCtxKey`. `RenewHTTP` builds a request with `req.WithContext(ctx)`
and sends it over a `*http.Transport`, whose `roundTrip` calls `httptrace.ContextClientTrace(ctx)`
(go1.27.3 `net/http/transport.go:614`, and `:1870`), i.e. `ctx.Value(clientEventContextKey{})`; the
dial and lookup paths read `nettrace.TraceKey{}` and `nettrace.LookupIPAltResolverKey{}`
(`net/dial.go:535, 778`, `net/lookup.go:313, 321`). A context whose `Value` panics at the first key,
and delegates everything else to a real `WithCancel` child, meets every clause of the premise, and
`RenewHTTP` panics; a non-nil value at any of the three keys runs the caller's functions (trace
hooks, the alternative resolver). Closed theorems reaching it: those whose collections list
`leasehttp.RenewHTTP.wp_proof` (`etc/tcb-report.py --roots` on it); etcd's own contexts hold no such
values, so no closed theorem's program exercises the gap, but the axiom as stated is false.

**The Go test.** `TestRenewHTTPValuePanics` (`examples/premisefix/streamctx/streamctx_test.go`):
`panicTraceCtx` (every method delegates, but `Value` at `httptrace.clientEventContextKey` panics);
`RenewHTTP` panics with `Value(httptrace key)`.

**The fix** (decided by etcd-grove-81, 2026-11-13): `RenewHTTP`'s premise gains `http.netCtxOk ctx`,
`context.valueAt ctx k (· = nil)` at the three keys (their types translated, types only:
`net/http/httptrace`, `internal/nettrace`, `etc/goose.py` project `etcd`); the stream path
discharges it from T-a's chain form of grpc's run context extended to name the three keys. In
progress on branch `k8s-7f4` (Addendum T-h, `notes/k8s-7f4-freeze.md`). The wider sweep of
specs whose library code reads `ctx.Value` at keys their premises do not speak of is
etcd-grove-81's separate task.
