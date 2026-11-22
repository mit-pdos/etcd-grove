/-
Proof of `Spec/golang_org/x/time/rate/Limiter__reserveN.lean` over the real code (x/time/rate
v0.16.0, `rate.go`: `reserveN`, and the `advance`, `tokensFromDuration` and `durationFromTokens` it
calls; prove-metrics-float, 2026-11-22). Every float operation steps (Perennial's IEEE 754 rules,
`wp_float64_<op>`: some result, a NaN included), comparisons are total, and `time.Duration(f)` of
any float is some duration (an out-of-range conversion is implementation-defined in Go, not a
panic): nothing about the float values is needed.
-/
module

public import Spec.golang_org.x.time.rate.Limiter__reserveN
public import Spec.time.Duration__Seconds_ptr
public import Perennial.Spec.time.Time__Before
public import Perennial.Spec.time.Time__Sub
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

/-- `limit.tokensFromDuration(d)` (`rate.go:451-456`): some `float64` (`d.Seconds() * float64(limit)`,
or `0` for a non-positive `limit`). -/
private theorem wp_tokensFromDuration
    (wp_Seconds : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (l : golang_org.x.time.rate.Limit) (d : _root_.Perennial.time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
      (App (Val (l @!! golang_org.x.time.rate.Limit.ty @!! go!"tokensFromDuration")) (Val #d))
    {{ (f : w64), RET #f; True }} := by
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  wp_start as -
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  generalize float64Leb l (W64 0) = c
  cases c
  · wp_auto
    wp_apply wp_Seconds $$ [$d] as %f d
    wp_apply wp_float64_mul as %g -
    iapply HΦ; itrivial
  · wp_auto
    iapply HΦ; itrivial

/-- `lim.advance(t)` (`rate.go:431-447`), with the limiter's fields it reads held (its mutex
held): some `float64`, the fields unchanged. -/
private theorem wp_advance
    (wp_Before : _root_.Perennial.time.Time.Before.spec (GF := GF) (hG := hG))
    (wp_Sub : _root_.Perennial.time.Time.Sub.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (rl : Loc) (t : _root_.Perennial.time.Time) (l : golang_org.x.time.rate.Limit) (b tk : w64)
    (la : _root_.Perennial.time.Time) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗
        rl.[golang_org.x.time.rate.Limiter, go!"limit"] ↦ l ∗
        rl.[golang_org.x.time.rate.Limiter, go!"burst"] ↦ b ∗
        rl.[golang_org.x.time.rate.Limiter, go!"tokens"] ↦ tk ∗
        rl.[golang_org.x.time.rate.Limiter, go!"last"] ↦ la }}
      (App (Val (rl @!! go.GoType.PointerType golang_org.x.time.rate.Limiter.ty @!! go!"advance"))
        (Val #t))
    {{ (f : w64), RET #f;
        rl.[golang_org.x.time.rate.Limiter, go!"limit"] ↦ l ∗
        rl.[golang_org.x.time.rate.Limiter, go!"burst"] ↦ b ∗
        rl.[golang_org.x.time.rate.Limiter, go!"tokens"] ↦ tk ∗
        rl.[golang_org.x.time.rate.Limiter, go!"last"] ↦ la }} := by
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
    wp_apply (wp_tokensFromDuration wp_Seconds) as %delta -
    wp_apply wp_float64_add as %tokens -
    generalize (float64Leb (int64ToFloat64 b) tokens && !float64Eq tokens (int64ToFloat64 b)) = c
    cases c <;> wp_auto <;> (iapply HΦ; iframe)

/-- `limit.durationFromTokens(tokens)` (`rate.go:458-471`): some duration (`InfDuration` for a
non-positive `limit` or a duration above `MaxInt64`, else `time.Duration` of the float, which Go
converts without a panic whatever its value). -/
private theorem wp_durationFromTokens (l : golang_org.x.time.rate.Limit) (f : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
      (App (Val (l @!! golang_org.x.time.rate.Limit.ty @!! go!"durationFromTokens")) (Val #f))
    {{ (d : _root_.Perennial.time.Duration), RET #d; True }} := by
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  wp_start as -
  wp_auto
  rw [show golang_org.x.time.rate.InfDuration = #(W64 9223372036854775807) from rfl]
  generalize float64Leb l (W64 0) = c
  cases c
  case true =>
    wp_auto
    iapply HΦ; itrivial
  case false =>
    wp_auto
    wp_apply wp_float64_div as %q -
    wp_apply wp_float64_mul as %dur -
    generalize (float64Leb (W64 4890909195324358656) dur && !float64Eq dur (W64 4890909195324358656)) = c
    cases c
    case true =>
      wp_auto
      iapply HΦ; itrivial
    case false =>
      wp_auto
      wp_apply wp_ArbitraryInt as %x -
      iapply HΦ; itrivial

theorem rate.Limiter.reserveN.wp_proof
    (wp_Before : _root_.Perennial.time.Time.Before.spec (GF := GF) (hG := hG))
    (wp_Sub : _root_.Perennial.time.Time.Sub.spec (GF := GF) (hG := hG))
    (wp_Add : _root_.Perennial.time.Time.Add.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG)) :
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
    wp_apply (wp_advance wp_Before wp_Sub wp_Seconds) $$ [$Hlimit $Hburst $Htokens $Hlast]
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
