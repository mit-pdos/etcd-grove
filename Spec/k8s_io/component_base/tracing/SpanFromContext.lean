/-
`tracing.SpanFromContext(ctx)` (names-only; `k8s.io/component-base/tracing/tracing.go`): a new
non-nil `*Span` (`&Span{otelSpan: trace.SpanFromContext(ctx), utilSpan: utiltrace.FromContext(ctx)}`).
(premise-fixes-7) `utiltrace.FromContext` calls `ctx.Value(ContextTraceKey{})`, so `ctx` is not nil;
the span's fields are what otel and `utiltrace` made (`trace.spanValOk`, `utiltrace.traceRes`), so
the `*Span`'s methods (`End`, `AddEvent`, `RecordError`) return.
The trust boundary: an axiom, `Proof/k8s_io/component_base/tracing/SpanFromContext.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys

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
abbrev tracing.SpanFromContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing ∗ trace.spanValOk ctx ∗
      context.valueAt ctx utiltrace.traceKeyAny utiltrace.traceRes }}
    (App (Val (@! k8s_io.component_base.tracing.SpanFromContext)) (Val #(GoInterface.ok ctx)))
  {{ (sp : Loc), RET #sp; ⌜sp ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
