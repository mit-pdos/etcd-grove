/-
`traceutil.Tracer.Start`: the trust boundary (`pkg/v3/traceutil.Tracer` is an otel `trace.Tracer` (names-only)). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext
public import Proof.google_golang_org.grpc.metadata.Incoming
public import Proof.context.ReqKeys
public import Proof.context.LibKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SrvCtxWeak
public import Proof.net.http.NetCtx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `traceutil.Tracer.Start(ctx, name, opts...)` on the tracer the package variable holds: a
context like `ctx` (the same deadline and `Done`, other values: otel's `ContextWithSpan` is a
`context.WithValue`), a context (`context.isContext`) if `ctx` is one (2026-10-12, unit 2: the
request path's `WithTimeout`), carrying `ctx`'s trace (2026-10-14, unit P1b: otel's key is not
`traceutil.TraceKey`) and its incoming gRPC metadata (`metadata.incomingOf`, 2026-10-28, the auth
plan's E3zb: otel's key is not grpc's `mdIncomingKey{}`, so `metadata.FromIncomingContext` reads
`ctx`'s), and a span (`trace.isSpan`); and (2026-11-06, the fix of `trace.SpanFromContext`'s axiom,
`notes/axiom-review/otel-spanfromcontext-todo.md`) a context whose span is a span if `ctx`'s is
(`trace.spanCtxOk`): otel's tracers return `ContextWithSpan(ctx, s)` (a `valueCtx` whose
`Value(currentSpanKey)` is `s`) with the span `s` they return (the SDK's `tracer.Start`, a new SDK
span; the no-op tracer `noop.Tracer.Start`, its no-op `Span`), or (the no-op tracer, when `ctx`'s
span is not recording and has a valid span context) `ctx` itself with `ctx`'s span.
(Sweep repairs 1, B2, 2026-11-08) Its start time (`context.startTimeOk`): otel's key is not
`traceutil.StartTimeKey`, so either context `Start` returns answers `Value(StartTimeKey{})` as `ctx`
does (checked against the noop and the SDK tracer, `examples/sweeprepairs/tracer`).
(Premise fixes 8, 2026-11-11, decided by etcd-grove-81) Its library values (`context.libCtxOk`): at
grpc's keys (`mdIncomingKey{}`, `mdOutgoingKey{}`, `peerKey{}`, not otel's key's type) it answers as
`ctx` does, and at otel's `currentSpanKey` either `ctx`'s value or the span the tracer made, one of
otel's (`trace.otelSpan`) (checked against the noop and the SDK tracers,
`examples/premisefix/tracerctx`). The SDK claims hold with Go's execution tracer off: with it on
(`runtime/trace.Start`, e.g. pprof's `/debug/pprof/trace`), the SDK tracer's `Start` also reads
`ctx.Value(runtime/trace.traceContextKey{})` (`runtime/trace.NewTask`, sdk/trace v1.47.0
`span.go:844-856`), a key the premise does not constrain. Not reachable in the model: the `Tracer`
points-to comes only from `Tracer_init`, the no-op tracer, and `traceutil.Init` has no spec; if it
gets one, add a premise that the runtime/trace key holds `nil` (true of grpc's run context) or
restrict the tracer to the no-op one (k8s 7f-4, Addendum T-h review, m3).
(k8s 7f-4, Revisions 1-2, decided by etcd-grove-81, 2026-11-12) `ctx`'s span is otel's
(`trace.spanValOk ctx`, in the premise: `Value(currentSpanKey)` returns nil or `trace.otelSpan`, a
span whose methods return, `SpanContext` and `IsRecording` among them): the tracers call
`SpanContext()` (and the no-op one `IsRecording()`) on `ctx`'s span, and the no-op tracer can return
`ctx`'s span itself, so without it a context of the program's own whose `Value(currentSpanKey)` is a
span with a panicking `SpanContext` refuted the triple (the former **Open** note of 2026-11-06;
`examples/premisefix/tracerspan`). Revision 1's `trace.spanCtxOk` did not exclude it (`isSpan` covers
only `End`, `AddEvent`, `RecordError`). Callers have it inside `context.libCtxOk`, from grpc's run
context on the request path and from its chain form (`context.libCtxOkC`) on the stream path.
(k8s 7f-4, T-f, 2026-11-12) The context may also be a stream handler's weak one (`srvCtxWeak`:
etcd's `cancellableContext`, whose `Err()` may return `ErrGRPCNoLeader`), and then so is the context
returned: `ContextWithSpan(ctx, s)` is a `valueCtx`, whose `Deadline`/`Done`/`Err` are `ctx`'s and
whose `Value(&cancelCtxKey)` is `ctx`'s (otel's key is not `&cancelCtxKey`), or `ctx` itself (the
no-op tracer). The post's context facts are wands from the premise's (the old triple, from
`txnCtx`: `traceutil.Tracer.Start.spec_txn`, `Proof/go_etcd_io/etcd/pkg/v3/traceutil/StartLaws.lean`).
The premise is a disjunction (`txnCtx ∨ srvCtxWeak`), a known departure from the spec principles
(`notes/decisions.md`, "Tracer.Start's context premise"): `srvCtxWeak` admits program contexts that
`txnCtx` did not, but `isContext`'s arm of `txnCtx` already admitted the same kind, and with
`spanValOk` in the premise neither arm can refute the triple through the span. (k8s 7f-4, T-f')
`srvCtxWeak`'s `Err` clauses take a level token (`levelTok v3rpc.ctxErrLvl`), which the wand carries
unchanged: a `valueCtx`'s `Err()` is `ctx`'s own call, paid with the same token. (k8s 7f-4,
Addendum T-h0) It holds nothing at net/http's keys, in the chain form, if `ctx` does
(`http.netCtxOkC`): `ContextWithSpan(ctx, s)` is a `*valueCtx` at otel's `currentSpanKey`, a key of
another type than `httptrace`'s and `nettrace`'s, whose `context.value()` walk goes on to `ctx`
(Perennial's `ctxValue_valueCtx`), or `ctx` itself (the no-op tracer); what carries the fact to
`LeaseRenew`'s `WithTimeout` child (`ctxValueFrom`) and from there to `RenewHTTP`. -/
abbrev traceutil.Tracer.Start.spec : Prop :=
  ∀ (tr ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString)
    (opts : GoSlice),
  {{ globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr ∗
      (mvcc.txnCtx ctx cd ∨ srvCtxWeak ctx cd) ∗ trace.spanValOk ctx }}
    (App (App (App (Val #(methods tr.ty go!"Start" tr.v)) (Val #(GoInterface.ok ctx))) (Val #name))
      (Val #opts))
  {{ (ctx' : GoInterfaceOk) (sp : GoInterface), RET (PairV #(GoInterface.ok ctx') #sp);
      (∃ vs : GMap GoInterface GoInterface,
        □ (mvcc.txnCtx ctx cd -∗ mvcc.txnCtx ctx' { cd with Values := vs }) ∗
        (context.isContext ctx cd -∗ context.isContext ctx' { cd with Values := vs })) ∗
      □ (srvCtxWeak ctx cd -∗ srvCtxWeak ctx' cd) ∗
      □ (∀ o : Option Loc, traceutil.ctxTraceIs ctx o -∗ traceutil.ctxTraceIs ctx' o) ∗
      ⌜metadata.incomingOf (GoInterface.ok ctx') = metadata.incomingOf (GoInterface.ok ctx)⌝ ∗
      trace.isSpan sp ∗ □ (trace.spanCtxOk ctx -∗ trace.spanCtxOk ctx') ∗
      □ (context.startTimeOk ctx -∗ context.startTimeOk ctx') ∗
      □ (context.libCtxOk ctx -∗ context.libCtxOk ctx') ∗
      □ (http.netCtxOkC ctx -∗ http.netCtxOkC ctx') }}

end spec

end EtcdGrove
end Perennial
