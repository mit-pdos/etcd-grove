/-
Proof of `Spec/go_opentelemetry_io/otel/trace/SpanFromContext.lean` over the real body (prove-protootel,
2026-11-20; a trust-boundary axiom while otel's `trace` was names-only): `SpanFromContext(ctx)`
(`trace/context.go`, v1.47.0) asks `ctx.Value(currentSpanKey)` and returns it when it is a `Span`,
else `noopSpanInstance`, a `noopSpan{}` (the package's fact, `traceInit`), whose `End`, `AddEvent`
and `RecordError` are empty (`noop.go`).
-/
module

public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_opentelemetry_io.otel

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_opentelemetry_io.otel.trace.Assumptions]

/-- A `noopSpan` as a `Span` is a span: its `End`, `AddEvent` and `RecordError` do nothing. -/
theorem trace.isSpan_noopSpan (x : trace.noopSpan) :
    ⊢ trace.isSpan (GF := GF) (interface.mkOk trace.noopSpan.ty #x) := by
  unfold trace.isSpan
  iexists ⟨trace.noopSpan.ty, #x⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro
    iintro %opts
    wp_start
    iapply HΦ; itrivial
  isplitr
  · imodintro
    iintro %name %opts
    wp_start
    iapply HΦ; itrivial
  · imodintro
    iintro %err %opts
    wp_start
    iapply HΦ; itrivial

theorem trace.SpanFromContext.wp_proof : trace.SpanFromContext.spec (GF := GF) (hG := hG) := by
  intro ctx cd
  wp_start as Hc
  ihave #Hf : (go_opentelemetry_io.otel.trace.traceInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold go_opentelemetry_io.otel.trace.traceInit at Hf
  icases Hf with ⟨%x, #Hv⟩
  ihave #Hnoop := trace.isSpan_noopSpan (GF := GF) x
  -- `ctx.Value(currentSpanKey)`: `nil` or a span, in both cases of the premise
  ihave Hval : iprop(∀ Ψ : val → IProp GF,
      (∀ w : GoInterface, (⌜w = GoInterface.nil⌝ ∨ trace.isSpan w) -∗ Ψ #w) -∗
      WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #trace.spanKeyVal)) {{ Ψ }}) $$ [Hc]
  · icases Hc with (%Hctx | Hsc)
    · subst Hctx
      iintro %Ψ HΨ
      wp_apply (_root_.Perennial.context.ctxValue_Value _root_.Perennial.context.todoCtxVal
        trace.spanKeyVal (· = GoInterface.nil)) $$ [] as %w %hw
      · iapply _root_.Perennial.context.ctxValue_todo
      iapply HΨ
      ileft; ipureintro; exact hw
    · iunfold trace.spanCtxOk at Hsc
      icases Hsc with ⟨%R, #HR, #HV⟩
      iintro %Ψ HΨ
      wp_apply HV as %w %hw
      iapply HΨ
      iapply HR $$ %w %hw
  wp_auto
  wp_apply Hval as %w Hw
  icases Hw with (%hn | #Hs)
  · subst hn
    wp_auto
    iapply HΦ $$ Hnoop
  · cases w with
    | nil =>
      wp_auto
      iapply HΦ $$ Hnoop
    | ok ii =>
      cases h : go.typeSetContains ii.ty trace.Span.ty
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iapply HΦ $$ Hnoop
      · simp only [h, ↓reduceIte]
        wp_auto
        iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
