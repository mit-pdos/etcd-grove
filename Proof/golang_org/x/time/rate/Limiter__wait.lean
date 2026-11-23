/-
Proof of `Spec/golang_org/x/time/rate/Limiter__wait.lean` over the real code (x/time/rate v0.16.0,
`rate.go:251-316`; rate-wait, 2026-11-23): the burst check (`fmt.Errorf` of two `int`s), the
non-blocking `select` on `ctx.Done()` (`isContextDone_nonblocking_receive`: the case fires only once
the context is done, when `ctx.Err()` returns), `ctx.Deadline()`, the token bucket (`reserveN`), the
reservation's `DelayFrom` (inline, as in `Reservation.Delay`'s proof), the timer generator
(`rate.newTimerOk`: the deferred `stop`, `advance`), and the blocking `select` on the timer's channel
(`bag_recv_au`) and `ctx.Done()` (then the reservation's `Cancel`).
-/
module

public import Spec.golang_org.x.time.rate.Limiter__wait
public import Spec.golang_org.x.time.rate.Limiter__reserveN
public import Spec.golang_org.x.time.rate.Reservation__Cancel
public import Perennial.Spec.time.Time__Sub
public import Perennial.Proof.fmt.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode golang_org.x.time

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

theorem rate.Limiter.wait.wp_proof
    (wp_Sub : _root_.Perennial.time.Time.Sub.spec (GF := GF) (hG := hG))
    (wp_reserveN : rate.Limiter.reserveN.spec (GF := GF) (hG := hG))
    (wp_Cancel : rate.Reservation.Cancel.spec (GF := GF) (hG := hG)) :
    rate.Limiter.wait.spec (GF := GF) (hG := hG) := by
  haveI : go.NotInterface go.float64 := ⟨by simp [go.float64]⟩
  intro rl c cd n t nt
  wp_start as ⟨#Hl, #Hc, #Hnt⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hl' := Hl
  iunfold rate.limiterOk at Hl'
  iunfold rate.limiterRaw at Hl'
  icases Hl' with #Hm
  ihave #Hc' := Hc
  iunfold _root_.Perennial.context.isContext at Hc'
  iunfold _root_.Perennial.context.isContextDef at Hc'
  iNamed Hc'
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hm] as ⟨Hlocked, Hinv⟩
  iunfold rate.limiterFields at Hinv
  icases Hinv with ⟨%l, %b, %tk, %la, %le, Hlimit, Hburst, Htokens, Hlast, HlastEvent⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hm $Hlocked Hlimit Hburst Htokens Hlast HlastEvent]
  · inext; iunfold rate.limiterFields; iexists _, _, _, _, _; iframe
  (try wp_auto)
  -- `n > burst && limit != Inf`: an error from `fmt.Errorf`
  wp_if_destruct
  all_goals (try wp_auto)
  generalize (!float64Eq l (W64 9218868437227405311)) = big
  cases big
  case true =>
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl' ⟨Hsl', -⟩
    wp_auto
    wp_apply _root_.Perennial.fmt.wp_Errorf_argsWf _ _ _ ?wf $$ [$Hsl'] as %e #He
    case wf =>
      exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.int _)
        (_root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.int _) _root_.Perennial.fmt.ArgsWf.nil)
    iapply HΦ; itrivial
  all_goals (try wp_auto)
  all_goals
    -- the non-blocking `select` on `ctx.Done()`
    wp_apply HDone as %dch %γd #Hdone
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
        iprop((∀ err : GoInterface, True -∗ Φ #err) ∗ «$res0_ptr» ↦ GoInterface.nil ∗
          defer ↦ func.mk BAnon BAnon #() ∗ lim_ptr ↦ rl ∗ newTimer_ptr ↦ nt ∗ t_ptr ↦ t ∗
          n_ptr ↦ n ∗ ctx_ptr ↦ GoInterface.ok c)
      $$ [] [HΦ «$res0» defer lim newTimer t n ctx] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro ⟨HΦ, «$res0», defer, lim, newTimer, t, n, ctx⟩
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply _root_.Perennial.context.isContextDone_is_chan $$ Hdone
      iapply _root_.Perennial.context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
      isplit
      · iintro ⟨-, #Hcl⟩
        wp_auto
        wp_apply HErrDone $$ [$Hcl] as %err - - -
        iapply HΦ; itrivial
      · iframe
    · iframe
    iintro ⟨HΦ, «$res0», defer, lim, newTimer, t, n, ctx⟩ -
    wp_auto
    rw [show golang_org.x.time.rate.InfDuration = #(W64 9223372036854775807) from rfl]
    wp_auto
    -- `ctx.Deadline()`: the wait limit
    wp_apply HDeadline
    generalize cd.Deadline = dl
    cases dl
    all_goals (try wp_auto)
    all_goals (try (
      wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Sub"
      (try wp_auto)
      wp_apply wp_Sub as %wl -))
    all_goals (try wp_auto)
    all_goals
      -- the token bucket
      wp_apply wp_reserveN $$ [$Hpkg $Hl] as %r %Hr
      (try wp_auto)
      cases hok : r.ok'
      case false =>
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl' ⟨Hsl', -⟩
        wp_auto
        wp_apply _root_.Perennial.fmt.wp_Errorf_argsWf _ _ _ ?wf $$ [$Hsl'] as %e #He
        case wf =>
          exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (.int _) _root_.Perennial.fmt.ArgsWf.nil
        iapply HΦ; itrivial
      case true =>
      wp_auto
      -- `r.DelayFrom(t)`, inline
      icases (typedPointsto_not_null_dup _ _ _) $$ r with ⟨r, %Hrn⟩
      iStructNamedSuffix r "R"
      wp_mcall (go.GoType.PointerType golang_org.x.time.rate.Reservation.ty) go!"DelayFrom"
      wp_auto
      rw [hok]
      wp_auto
      wp_mcall (go.GoType.PointerType _root_.Perennial.time.Time.ty) go!"Sub"
      (try wp_auto)
      wp_apply wp_Sub as %dl -
      (try wp_auto)
      wp_if_destruct
      all_goals (try wp_auto)
      all_goals (try wp_if_destruct)
      all_goals (try (iapply HΦ; itrivial))
      all_goals
        ihave r : r_ptr ↦ r $$ [okR limR tokensR timeToActR limitR]
        · iapply typedPointsto_combine r_ptr _ _ Hrn
          simp only [TypedPointsto.typedPointstoDef, hok]
          iframe
        -- the timer generator
        iunfold rate.newTimerOk at Hnt
        wp_apply (lc := 2) Hnt as %ch %stop %adv %γt ⟨#Hbag, #Hstop, #Hadv⟩
        (try wp_auto)
        wp_apply Hadv
        (try wp_auto)
        wp_apply HDone as %dch' %γd' #Hdone'
        (try wp_auto)
        wp_apply_core chan.wp_select_blocking
        iapply BigAndL.bigAndL_cons.2
        isplit
        · -- `<-ch`: the timer fired
          simp only [chan.blockingClausePre]
          iexists _root_.Perennial.time.Time, inferInstance, inferInstance, inferInstance, inferInstance,
            ch, γt
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply is_bag_is_chan $$ Hbag
          iapply bag_recv_au γt ch _ _ $$ [$Hlc1 $Hlc2] Hbag
          inext
          iintro %tm -
          (try wp_auto)
          wp_apply Hstop as %sb -
          (try wp_auto)
          iapply HΦ; itrivial
        iapply BigAndL.bigAndL_cons.2
        isplit
        · -- `<-ctx.Done()`: the context is done; the reservation is cancelled
          simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch', γd'
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply _root_.Perennial.context.isContextDone_is_chan $$ Hdone'
          iapply _root_.Perennial.context.isContextDone_receive $$ Hdone'
          iintro ⟨-, #Hcl⟩
          (try wp_auto)
          wp_apply wp_Cancel $$ [$Hpkg $r] as r
          · rw [Hr]; iexact Hl
          (try wp_auto)
          wp_apply HErrDone $$ [$Hcl] as %err - - -
          (try wp_auto)
          wp_apply Hstop as %sb -
          (try wp_auto)
          iapply HΦ; itrivial
        iapply BigAndL.bigAndL_nil.2
        itrivial

end proof

end EtcdGrove
end Perennial
