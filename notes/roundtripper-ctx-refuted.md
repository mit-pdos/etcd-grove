# `http.WithContext_ok` with rafthttp's round trippers refuted: the request's context (2026-11-13, k8s 7f-4 Addendum T-i)

Found by etcd-grove-81's context-key sweep (item (2); the class of `notes/renewhttp-value-refuted.md`).

**Reach.** Three landed trust-boundary axioms, jointly: `http.WithContext_ok` (`Proof/net/http/Axioms.lean`,
statement `http.WithContext_spec` in `Proof/net/http/Boundary.lean`) took any context and kept nothing
of it (`reqOwn`, `reqStream`); `rafthttp.NewRoundTripper.wp_proof` and
`rafthttp.newStreamRoundTripper.wp_proof` give `http.roundTripperOk`, whose `RoundTrip` triple never
mentioned the request's context, yet promised no panic and, on failure, an error net/http made
(`netErr`) whose `Error()` returns (`errStrOk`). The round trippers are `*http.Transport`s
(`transport.NewTimeoutTransport`, `rafthttp/util.go:47, 59`), whose `roundTrip` reads the request's
context: `httptrace.ContextClientTrace(ctx)` (go1.27.3 `net/http/transport.go:614`; a non-nil
`*ClientTrace` runs the program's hooks), `context.WithCancelCause(req.Context())` (`:675`:
`Value(&cancelCtxKey)`, `Done`, `Err`, `Cause`), on `Done` `return nil, context.Cause(ctx)` (`:698`:
the context's own error comes back), and the dial's `Deadline` and `nettrace` keys (`net/dial.go:535,
778`, `net/lookup.go:313, 321`). Closed theorems reaching the axioms: every collection with
rafthttp's pipeline, snapshot sender or stream reader (16 list `WithContext_ok`). rafthttp's three
callers (`pipeline.go:140`, `snapshot_sender.go:149`, `stream.go:595`) pass only
`context.WithCancel(context.Background())`, so no closed theorem's program exercises the gap, but the
axioms as stated are false.

**The Go tests** (`examples/premisefix/rtctx`, go1.27.3):
- `TestRoundTripValuePanics`: a `WithCancel(Background())` context whose `Value` panics at
  `httptrace`'s `clientEventContextKey{}` makes `RoundTrip` panic.
- `TestRoundTripTraceHook`: a `ClientTrace` in the context: `RoundTrip` calls its `GetConn`, whose
  panic escapes.
- `TestRoundTripProgramErr`: a context whose `Done` is closed and whose `Err` is a program error with
  a panicking `Error()`: `RoundTrip` returns that error itself (not `netErr`, not `errStrOk`).
- `TestRoundTripDeadlineCause`: why the fix is not `isContext ∗ http.netCtxOk`: Perennial's
  `WithDeadlineCause(Background(), d, cause)` makes a context with `isContext`, `nil` at every key,
  and `RoundTrip` on it returns the program's `cause` (Perennial's `cancelCtx` model leaves the
  `cause` field unconstrained, so no context fact of the model rules it out).
- `TestRoundTripBgCancel`: the fixed premise: over a `WithCancel(Background())` context both round
  trippers return a response, a dial error (`*net.OpError`), or `context.Canceled` itself once the
  context is cancelled, in flight or before the call.

**The fix** (Addendum T-i of `notes/k8s-7f4-freeze.md`; for etcd-grove-81's axiom review): the request
records its context (`http.reqCtx r ctx`, persistent, from `WithContext_spec`'s post); `roundTripperOk`'s
`RoundTrip` takes `http.reqCtxBg r`: the request's context is a `*cancelCtx` child of `Background()`
(`context.bgCancelChild`), what `context.WithCancel(context.Background())` returns
(`context.WithCancelBackground.spec`'s post gains it; its axiom becomes a proof from Perennial's
`wp_WithCancel_gen`). `netErr`'s docstring names `context.Canceled`, the cause such a context
yields once cancelled.
