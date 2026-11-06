/-
`tracing.Start(ctx, name, attrs...)` (`k8s.io/component-base/tracing`, names-only): a span
(`tracing.isSpan`), and a context derived from `ctx` (OpenTelemetry's `ContextWithSpan` and
utiltrace's `ContextWithTrace`, value contexts: their `Done` and `Err` are the parent's), so a
context the client accepts (`ctxOk`, `ctxErrClient` at the parent's description) gives one too.
Tracing is otherwise a no-op for the store's results. The trust boundary: an axiom,
`Proof/k8s_io/component_base/tracing/Start.lean`. Lean-first (no Rocq counterpart).

Since 2026-11-06 (found false with otel's `trace.SpanFromContext`; the user approved fixing axioms
as needed) it takes `tracing.startCtxOk ci` (no span under otel's key, and the utiltrace key
answering) and returns `tracing.isSpan sp` in place of `⌜sp ≠ null⌝`: `Start` calls
`TracerProvider()` on `ctx`'s span and its tracer's `Start`, and `utiltrace.FromContext` calls
`Value` at `ContextTraceKey{}`, so a context of the program's own (a span with a panicking
`TracerProvider`, or a panicking `Value`) refuted the claim that it returns. Faithful
(`Proof/k8s_io/component_base/tracing/Defs.lean`'s header has the code): with no span,
`trace.SpanFromContext(ctx)` is otel's `noopSpanInstance`, whose `TracerProvider()` is
`noopTracerProvider{}` (`autoInstEnabled` is false unless otel's auto-instrumentation agent
attaches), whose tracer's `Start` reads `ctx`'s span again (none) and returns
`ContextWithSpan(ctx, noopSpanInstance)` and that span; `utiltrace.FromContext` of it asks `ctx`
(`utilTraceCtxOk`); `Nest` and `ContextWithTrace` return. The span's `End` and `AddEvent` call the
no-op span's (empty) and the new `*Trace`'s `LogIfLong` and `Step`, which return.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.component_base.tracing.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev tracing.Start.spec : Prop :=
  ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString) (attrs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing ∗ ctxOk ci cd ∗
      ctxErrClient ci cd ∗ tracing.startCtxOk ci }}
    (App (App (App (Val (@! k8s_io.component_base.tracing.Start)) (Val #(GoInterface.ok ci)))
      (Val #name)) (Val #attrs))
  {{ (ci' : GoInterfaceOk) (sp : Loc), RET (PairV #(GoInterface.ok ci') #sp);
      tracing.isSpan sp ∗ ctxOk ci' cd ∗ ctxErrClient ci' cd }}

end spec

end EtcdGrove
end Perennial
