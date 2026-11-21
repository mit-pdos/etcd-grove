/-
Proof of `Spec/k8s_io/component_base/tracing/SpanFromContext.lean` over the real code (component-base
`cd2c1afd246a`, `tracing/tracing.go:88-93`; prove-metrics3, 2026-11-21: until then a trust-boundary
axiom): `&Span{otelSpan: trace.SpanFromContext(ctx), utilSpan: utiltrace.FromContext(ctx)}`. otel's
`SpanFromContext` (`trace/context.go`, v1.47.0) is stepped through here: its own spec takes
`trace.spanCtxOk` (a span under otel's key), where this one's callers give `trace.spanValOk` (nil or
the opaque `trace.otelSpan`); only that it returns is needed.
-/
module

public import Spec.k8s_io.component_base.tracing.SpanFromContext
public import Spec.k8s_io.utils.trace.FromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.component_base.tracing.Assumptions]

theorem tracing.SpanFromContext.wp_proof
    (wp_FromContext : trace.FromContext.spec (GF := GF) (hG := hG)) :
    tracing.SpanFromContext.spec (GF := GF) (hG := hG) := by
  intro ctx
  wp_start as ⟨#Hs, #Ht⟩
  ihave #Hotel : isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace $$ []
  · iPkgInit
  ihave #Hut : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.trace $$ []
  · iPkgInit
  ihave #Hf : (go_opentelemetry_io.otel.trace.traceInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hotel
  iunfold go_opentelemetry_io.otel.trace.traceInit at Hf
  icases Hf with ⟨%x, #Hnoop⟩
  iunfold trace.spanValOk at Hs
  iunfold context.valueAt at Hs
  wp_auto
  -- otel's `SpanFromContext(ctx)`: `ctx.Value(currentSpanKey)`, asserted to `Span`
  wp_func_call
  wp_call
  wp_auto
  wp_apply Hs as %w %-
  cases w with
  | nil =>
    wp_auto
    wp_apply wp_FromContext $$ [] as %t %-
    · iframe #
    ihave %hnn := typedPointsto_not_null _ _ _ $$ «$r0»
    iapply HΦ
    ipureintro; exact hnn
  | ok wi =>
    cases h : go.typeSetContains wi.ty go_opentelemetry_io.otel.trace.Span.ty
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply wp_FromContext $$ [] as %t %-
      · iframe #
      ihave %hnn := typedPointsto_not_null _ _ _ $$ «$r0»
      iapply HΦ
      ipureintro; exact hnn
    · simp only [h, ↓reduceIte]
      wp_auto
      wp_apply wp_FromContext $$ [] as %t %-
      · iframe #
      ihave %hnn := typedPointsto_not_null _ _ _ $$ «$r0»
      iapply HΦ
      ipureintro; exact hnn

end proof

end EtcdGrove
end Perennial
