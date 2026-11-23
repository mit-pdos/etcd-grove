/-
Proof of `Spec/golang_org/x/time/rate/Limiter__reserveN.lean` over the real code (x/time/rate
v0.16.0, `rate.go:380-428`; prove-metrics-float, 2026-11-22), over the specs of the `advance` and
`durationFromTokens` it calls (their own files since rate-wait, 2026-11-23). Every float operation steps (Perennial's IEEE 754 rules,
`wp_float64_<op>`: some result, a NaN included), comparisons are total, and `time.Duration(f)` of
any float is some duration (an out-of-range conversion is implementation-defined in Go, not a
panic): nothing about the float values is needed.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__reserveN
public import Spec.golang_org.x.time.rate.Limiter__advance
public import Spec.golang_org.x.time.rate.Limit__durationFromTokens
public import Perennial.Spec.time.Time__Add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `wp_method_call` of the method `m` of type `t` (it rewrites the first `methods` of the goal,
here the deferred `Unlock` in the `defer` cell), then the call step. -/
local macro "wp_mcall " t:term:max m:term:max : tactic =>
  `(tactic| (rw [method_unfold (t := $t) (m := $m)]; wp_call))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

theorem rate.Limiter.reserveN.wp_proof
    (wp_Add : _root_.Perennial.time.Time.Add.spec (GF := GF) (hG := hG))
    (wp_advance : rate.Limiter.advance.spec (GF := GF) (hG := hG))
    (wp_durationFromTokens : rate.Limit.durationFromTokens.spec (GF := GF) (hG := hG)) :
    rate.Limiter.reserveN.spec (GF := GF) (hG := hG) := by
  -- `Limit`'s value methods resolve through `go_method_resolve_step`, which needs `NotInterface` of
  -- the underlying `float64` (no Perennial instance: notes/perennial-changes.md, "`go.NotInterface`
  -- of the predeclared named types")
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  intro rl t n mfr
  wp_start as #Hl
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold rate.limiterOk at Hl
  iunfold rate.limiterRaw at Hl
  icases Hl with #Hl
  wp_auto
  wp_apply wp_with_defer as %defer defer
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
    iapply HΦ; ipureintro; rfl
  case false =>
    wp_auto
    wp_apply wp_advance $$ [$Hlimit $Hburst $Htokens $Hlast]
      as %tokens ⟨Hlimit, Hburst, Htokens, Hlast⟩
    wp_apply wp_float64_sub as %tokens' -
    generalize (float64Leb tokens' (W64 0) && !float64Eq tokens' (W64 0)) = c
    cases c <;> wp_auto
    -- `tokens < 0`: the wait is `durationFromTokens(-tokens)`
    all_goals try
      wp_apply wp_float64_neg as %nt -
      wp_mcall (go.GoType.PointerType golang_org.x.time.rate.Limit.ty) go!"durationFromTokens"
      wp_auto
      wp_apply wp_durationFromTokens as %wd -
    all_goals
      wp_if_destruct
      all_goals
        (try wp_auto)
        (try wp_if_destruct)
        all_goals
          (try wp_auto)
          -- `ok`: `timeToAct` is `t.Add(waitDuration)`, the limiter's fields are updated
          (try (wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Add"
                (try wp_auto)
                wp_apply wp_Add as %tta -
                (try wp_auto)))
          wp_apply sync.Mutex.wp_Unlock $$ [$Hl $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
          · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
          (try wp_auto)
          iapply HΦ; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
