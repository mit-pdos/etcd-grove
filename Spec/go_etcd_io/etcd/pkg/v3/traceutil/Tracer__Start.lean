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
**Open** (2026-11-06, found with that fix): `isSpan sp` and the run's return are not justified for
every `txnCtx`: the tracers call `SpanContext()` (and the no-op one `IsRecording()`) on `ctx`'s span,
and the no-op tracer can return `ctx`'s span itself, so a context of the program's own whose
`Value(currentSpanKey)` is a span with a panicking method refutes it, as it refuted
`SpanFromContext`'s `isContext` arm. The contexts the proofs pass (grpc's run contexts, derived
from them, `Background()`'s children) hold a genuine span or none. -/
abbrev traceutil.Tracer.Start.spec : Prop :=
  ∀ (tr ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString)
    (opts : GoSlice),
  {{ globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr ∗
      mvcc.txnCtx ctx cd }}
    (App (App (App (Val #(methods tr.ty go!"Start" tr.v)) (Val #(GoInterface.ok ctx))) (Val #name))
      (Val #opts))
  {{ (ctx' : GoInterfaceOk) (sp : GoInterface), RET (PairV #(GoInterface.ok ctx') #sp);
      (∃ vs : GMap GoInterface GoInterface, mvcc.txnCtx ctx' { cd with Values := vs } ∗
        (context.isContext ctx cd -∗ context.isContext ctx' { cd with Values := vs })) ∗
      □ (∀ o : Option Loc, traceutil.ctxTraceIs ctx o -∗ traceutil.ctxTraceIs ctx' o) ∗
      □ (context.startTimeOk ctx -∗ context.startTimeOk ctx') ∗
      ⌜metadata.incomingOf (GoInterface.ok ctx') = metadata.incomingOf (GoInterface.ok ctx)⌝ ∗
      trace.isSpan sp ∗ □ (trace.spanCtxOk ctx -∗ trace.spanCtxOk ctx') ∗
      □ (context.startTimeOk ctx -∗ context.startTimeOk ctx') }}

end spec

end EtcdGrove
end Perennial
