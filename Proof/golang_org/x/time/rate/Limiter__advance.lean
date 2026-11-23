/-
Proof of `Spec/golang_org/x/time/rate/Limiter__advance.lean` over the real code (x/time/rate v0.16.0,
`rate.go:431-447`; prove-metrics-float, 2026-11-22, as a lemma of `reserveN`'s proof; its own file
since rate-wait, 2026-11-23, for `CancelAt`).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__advance
public import Spec.golang_org.x.time.rate.Limit__tokensFromDuration
public import Perennial.Spec.time.Time__Before
public import Perennial.Spec.time.Time__Sub

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `wp_method_call` of the method `m` of type `t` (it rewrites the first `methods` of the goal),
then the call step. -/
local macro "wp_mcall " t:term:max m:term:max : tactic =>
  `(tactic| (rw [method_unfold (t := $t) (m := $m)]; wp_call))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

theorem rate.Limiter.advance.wp_proof
    (wp_Before : _root_.Perennial.time.Time.Before.spec (GF := GF) (hG := hG))
    (wp_Sub : _root_.Perennial.time.Time.Sub.spec (GF := GF) (hG := hG))
    (wp_tokensFromDuration : rate.Limit.tokensFromDuration.spec (GF := GF) (hG := hG)) :
    rate.Limiter.advance.spec (GF := GF) (hG := hG) := by
  intro rl t l b tk la
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  wp_start as ⟨Hlimit, Hburst, Htokens, Hlast⟩
  wp_auto
  wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Before"
  wp_auto
  wp_apply wp_Before as %bef -
  cases bef <;> wp_auto
  all_goals
    wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Sub"
    wp_auto
    wp_apply wp_Sub as %el -
    wp_mcall (go.GoType.PointerType golang_org.x.time.rate.Limit.ty) go!"tokensFromDuration"
    wp_auto
    wp_apply wp_tokensFromDuration as %delta -
    wp_apply wp_float64_add as %tokens -
    generalize (float64Leb (int64ToFloat64 b) tokens && !float64Eq tokens (int64ToFloat64 b)) = c
    cases c <;> wp_auto <;> (iapply HΦ; iframe)

end proof

end EtcdGrove
end Perennial
