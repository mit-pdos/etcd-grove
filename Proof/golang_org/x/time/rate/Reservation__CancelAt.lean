/-
Proof of `Spec/golang_org/x/time/rate/Reservation__CancelAt.lean` over the real code (x/time/rate
v0.16.0, `rate.go:168-203`; rate-wait, 2026-11-23): under the limiter's mutex (`rate.limiterOk`), over
the specs of `advance`, `tokensFromDuration` and `durationFromTokens` and Perennial's `Time` methods.
Every float operation steps (Perennial's IEEE 754 rules), comparisons are total, and the stores keep
the limiter's fields of their types: nothing about the values is needed.
-/
module

public import Spec.golang_org.x.time.rate.Reservation__CancelAt
public import Spec.golang_org.x.time.rate.Limiter__advance
public import Spec.golang_org.x.time.rate.Limit__tokensFromDuration
public import Spec.golang_org.x.time.rate.Limit__durationFromTokens
public import Perennial.Spec.time.Time__Before
public import Perennial.Spec.time.Time__Sub
public import Perennial.Spec.time.Time__Add
public import Perennial.Spec.time.Time__Equal

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

theorem rate.Reservation.CancelAt.wp_proof
    (wp_Before : _root_.Perennial.time.Time.Before.spec (GF := GF) (hG := hG))
    (wp_Sub : _root_.Perennial.time.Time.Sub.spec (GF := GF) (hG := hG))
    (wp_Add : _root_.Perennial.time.Time.Add.spec (GF := GF) (hG := hG))
    (wp_Equal : _root_.Perennial.time.Time.Equal.spec (GF := GF) (hG := hG))
    (wp_advance : rate.Limiter.advance.spec (GF := GF) (hG := hG))
    (wp_tokensFromDuration : rate.Limit.tokensFromDuration.spec (GF := GF) (hG := hG))
    (wp_durationFromTokens : rate.Limit.durationFromTokens.spec (GF := GF) (hG := hG)) :
    rate.Reservation.CancelAt.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  intro r rv dq t
  wp_start as ⟨Hr, #Hl⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold rate.limiterOk at Hl
  iunfold rate.limiterRaw at Hl
  icases Hl with #Hl
  icases (typedPointsto_not_null_dup _ _ _) $$ Hr with ⟨Hr, %Hrn⟩
  iStructNamedSuffix Hr "R"
  ihave HΦ : (iprop(r.[golang_org.x.time.rate.Reservation, go!"ok"] ↦{dq} rv.ok' ∗
      r.[golang_org.x.time.rate.Reservation, go!"lim"] ↦{dq} rv.lim' ∗
      r.[golang_org.x.time.rate.Reservation, go!"tokens"] ↦{dq} rv.tokens' ∗
      r.[golang_org.x.time.rate.Reservation, go!"timeToAct"] ↦{dq} rv.timeToAct' ∗
      r.[golang_org.x.time.rate.Reservation, go!"limit"] ↦{dq} rv.limit') -∗ Φ #()) $$ [HΦ]
  · iintro ⟨okR, limR, tokensR, timeToActR, limitR⟩
    iapply HΦ
    iapply typedPointsto_combine r _ dq Hrn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply wp_with_defer as %defer defer
  cases hok : rv.ok'
  · wp_auto
    iapply HΦ; iframe
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hl] as ⟨Hlocked, Hinv⟩
  iunfold rate.limiterFields at Hinv
  icases Hinv with ⟨%l, %b, %tk, %la, %le, Hlimit, Hburst, Htokens, Hlast, HlastEvent⟩
  wp_auto
  generalize float64Eq l (W64 9218868437227405311) = isInf
  cases isInf
  case true =>
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hl $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
    · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
    (try wp_auto)
    iapply HΦ; iframe
  case false =>
  wp_auto
  wp_if_destruct
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hl $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
    · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
    (try wp_auto)
    iapply HΦ; iframe
  wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Before"
  wp_auto
  wp_apply wp_Before as %bef -
  cases bef
  case true =>
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hl $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
    · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
    (try wp_auto)
    iapply HΦ; iframe
  case false =>
  wp_auto
  wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Sub"
  (try wp_auto)
  wp_apply wp_Sub as %el -
  (try wp_auto)
  wp_mcall (go.GoType.PointerType golang_org.x.time.rate.Limit.ty) go!"tokensFromDuration"
  (try wp_auto)
  wp_apply wp_tokensFromDuration as %f -
  wp_apply wp_float64_sub as %rt -
  (try wp_auto)
  generalize float64Leb rt (W64 0) = c
  cases c
  case true =>
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hl $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
    · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
    (try wp_auto)
    iapply HΦ; iframe
  case false =>
  wp_auto
  wp_apply wp_advance $$ [$Hlimit $Hburst $Htokens $Hlast] as %tokens ⟨Hlimit, Hburst, Htokens, Hlast⟩
  wp_apply wp_float64_add as %tokens' -
  generalize (float64Leb (int64ToFloat64 b) tokens' && !float64Eq tokens' (int64ToFloat64 b)) = c
  cases c <;> wp_auto
  all_goals
    wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Equal"
    (try wp_auto)
    wp_apply wp_Equal as %eq -
    cases eq
    case false =>
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$Hl $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
      · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
      (try wp_auto)
      iapply HΦ; iframe
    case true =>
      wp_auto
      wp_mcall (go.GoType.PointerType golang_org.x.time.rate.Limit.ty) go!"durationFromTokens"
      (try wp_auto)
      wp_apply wp_durationFromTokens as %dd -
      wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Add"
      (try wp_auto)
      wp_apply wp_Add as %pe -
      (try wp_auto)
      wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Before"
      (try wp_auto)
      wp_apply wp_Before as %bef' -
      cases bef' <;> (try wp_auto)
      all_goals
        wp_apply sync.Mutex.wp_Unlock $$ [$Hl $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
        · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
        (try wp_auto)
        iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
