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
`notes/axiom-review/otel-spanfromcontext-todo.md`) a context whose span is a span
(`trace.spanCtxOk`). Since 2026-11-06 (the fix of this axiom, found false with that one; the user
approved fixing axioms as needed) it takes `trace.spanCtxOk ctx`: the tracers call `SpanContext()`
(and the no-op one `IsRecording()`) on `ctx`'s span and the no-op tracer can return that span
itself, so a context of the program's own whose `Value(currentSpanKey)` is a span with a
panicking method refuted the run's return and `isSpan sp` (`trace.isParentSpan` covers the two
methods). Faithful: etcd's `traceutil.Tracer` is `noop.NewTracerProvider().Tracer(...)` (`trace.go`;
`traceutil.Init`, which installs another, is not translated), whose `Start` (`trace/noop/noop.go`,
otel v1.47.0) reads `ctx`'s span by `trace.SpanFromContext` (`Value(currentSpanKey)`: `nil` or a
parent span, by `spanCtxOk`), calls its `SpanContext()` and, on a non-zero one, `IsRecording()`,
and returns `ctx` with that span when it is not recording, else `ContextWithSpan(ctx, s)` (a
`valueCtx` whose `Value(currentSpanKey)` is `s`, other keys `ctx`'s) with the span `s`, a no-op
`noop.Span` (its methods empty); either way the span returned is a parent span, so `ctx'` has
`spanCtxOk`. (The SDK's `tracer.Start` likewise reads the span's `SpanContext()` and returns
`ContextWithSpan(ctx, s)` with a new SDK span.) -/
abbrev traceutil.Tracer.Start.spec : Prop :=
  ∀ (tr ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString)
    (opts : GoSlice),
  {{ globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr ∗
      mvcc.txnCtx ctx cd ∗ trace.spanCtxOk ctx }}
    (App (App (App (Val #(methods tr.ty go!"Start" tr.v)) (Val #(GoInterface.ok ctx))) (Val #name))
      (Val #opts))
  {{ (ctx' : GoInterfaceOk) (sp : GoInterface), RET (PairV #(GoInterface.ok ctx') #sp);
      (∃ vs : GMap GoInterface GoInterface, mvcc.txnCtx ctx' { cd with Values := vs } ∗
        (context.isContext ctx cd -∗ context.isContext ctx' { cd with Values := vs })) ∗
      □ (∀ o : Option Loc, traceutil.ctxTraceIs ctx o -∗ traceutil.ctxTraceIs ctx' o) ∗
      ⌜metadata.incomingOf (GoInterface.ok ctx') = metadata.incomingOf (GoInterface.ok ctx)⌝ ∗
      trace.isSpan sp ∗ trace.spanCtxOk ctx' }}

end spec

end EtcdGrove
end Perennial
