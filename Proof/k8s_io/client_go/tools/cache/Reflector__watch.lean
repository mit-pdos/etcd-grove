/-
Proof of `Spec/k8s_io/client_go/tools/cache/Reflector__watch.lean`, over `handleWatch` (itself over
`handleAnyWatch`'s named hypothesis, gap D4) and the boundary hypotheses of the logger, the clock,
`rand.Float64` and the `apierrors` predicates. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__watch
public import Spec.k8s_io.client_go.tools.cache.handleWatch
public import Spec.k8s_io.client_go.tools.cache.Reflector__LastSyncResourceVersion
public import Spec.k8s_io.client_go.tools.cache.Reflector__setLastSyncResourceVersion
public import Spec.k8s_io.client_go.tools.cache.NewRetryWithDeadline
public import Spec.k8s_io.client_go.tools.cache.retryWithDeadlineImpl__After
public import Spec.k8s_io.client_go.tools.cache.retryWithDeadlineImpl__ShouldRetry
public import Spec.k8s_io.client_go.tools.cache.isExpiredError
public import Spec.k8s_io.client_go.tools.cache.isWatchErrorRetriable
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.github_com.go_logr.logr.Logger__V_ptr
public import Spec.github_com.go_logr.logr.Logger__Info
public import Spec.github_com.go_logr.logr.Logger__Info_ptr
public import Spec.k8s_io.utils.clock.RealClock__Now
public import Spec.k8s_io.utils.clock.RealClock__After
public import Spec.math.rand.Float64
public import Spec.time.Duration__Seconds_ptr
public import Spec.k8s_io.apimachinery.pkg.api.errors.IsTooManyRequests
public import Spec.k8s_io.apimachinery.pkg.api.errors.IsInternalError
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.FloatToInt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache apimodel informer

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

set_option hygiene false in
/-- A log call `logger.V(n).Info(msg, kvs...)`: its arguments' slice, `V` through the logger
variable, `Info`. -/
local macro "log_tac" : tactic => `(tactic| (
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply (wp_V_ptr logger_ptr lg _ _) $$ [logger] as %lg' logger
    · iframe
    (try wp_auto)
    wp_apply (wp_Info lg' _ _ _ _) $$ [Hsl] as -
    · iframe
    (try wp_auto)))

set_option hygiene false in
/-- A log call `logger.Info(msg, kvs...)` through the logger variable. -/
local macro "warn_tac" : tactic => `(tactic| (
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply (wp_Info_ptr logger_ptr lg _ _ _ _ _) $$ [logger Hsl] as ⟨logger, -⟩
    · iframe
    (try wp_auto)))

set_option hygiene false in
/-- Return, the reflector's state at the watch's version `p'.2`. -/
local macro "ret_refl" : tactic => `(tactic| (
    wp_for_post
    (try wp_auto)
    iapply HΦ
    ileft
    iexists p'.2.toNat
    unfold reflSt
    iexists (rvStr p'.2), u2
    iframe
    ipureintro; exact hrv2))

set_option hygiene false in
/-- Continue the loop, the reflector's state at the watch's version `p'.2`. -/
local macro "cont_refl" : tactic => `(tactic| (
    wp_for_post
    iframe
    iexists _, _
    iframe
    ileft
    iexists p'.2.toNat
    unfold reflSt
    iexists (rvStr p'.2), u2
    iframe
    ipureintro; exact hrv2))

set_option hygiene false in
/-- Return on the `Done` channel seen closed. -/
local macro "ret_seen" : tactic => `(tactic| (
    wp_auto
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iright
    iexact Hseen))

theorem Reflector.watch.wp_proof [Float64ToInt64Semantics]
    (wp_handleWatch : handleWatch.spec (GF := GF) (hG := hG))
    (wp_LastSyncResourceVersion : Reflector.LastSyncResourceVersion.spec (GF := GF) (hG := hG))
    (wp_setLastSyncResourceVersion : Reflector.setLastSyncResourceVersion.spec (GF := GF) (hG := hG))
    (wp_NewRetryWithDeadline : NewRetryWithDeadline.spec (GF := GF) (hG := hG))
    (wp_After : retryWithDeadlineImpl.After.spec (GF := GF) (hG := hG))
    (wp_ShouldRetry : retryWithDeadlineImpl.ShouldRetry.spec (GF := GF) (hG := hG))
    (wp_isExpiredError : isExpiredError.spec (GF := GF) (hG := hG))
    (wp_isWatchErrorRetriable : isWatchErrorRetriable.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_V_ptr : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Info_ptr : logr.Logger.Info_ptr.spec (GF := GF) (hG := hG))
    (wp_Now : clock.RealClock.Now.spec (GF := GF) (hG := hG))
    (wp_ClockAfter : clock.RealClock.After.spec (GF := GF) (hG := hG))
    (wp_Float64 : rand.Float64.spec (GF := GF) (hG := hG))
    (wp_Seconds_ptr : time.Duration.Seconds_ptr.spec (GF := GF) (hG := hG))
    (wp_IsTooManyRequests : apierrors.IsTooManyRequests.spec (GF := GF) (hG := hG))
    (wp_IsInternalError : apierrors.IsInternalError.spec (GF := GF) (hG := hG)) :
    Reflector.watch.spec (GF := GF) (hG := hG) := by
  intro r f lw et dh ctx dch γd errCh γa cfg res γf γt γi k hrvu
  wp_start as ⟨#Hfix, #Henv, #Hctx, #Herr, #HerrIs, Hst⟩
  ihave #Hm : (k8s_io.apiserver.pkg.storage.cacher.k8sCacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hm with ⟨%e1, %e2, #He1, #He2⟩
  iunfold errIsOk at HerrIs
  ihave #Hctx2 := Hctx
  iunfold stableCtx at Hctx2
  icases Hctx2 with ⟨#HDone, #HErr, #Hdch⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply HDone
  ipersist r
  ihave #Hklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  ihave #Hlogr : isPkgInit (PROP := IProp GF) pkg_id.github_com.go_logr.logr $$ []
  · iPkgInit
  ihave #Hclk : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  iunfold reflFixed at Hfix
  icases Hfix with ⟨#Hf1, #Hf2, #Hdh⟩
  iunfold delayOk at Hdh
  iunfold reflFixed1 at Hf1
  icases Hf1 with ⟨%c, #Hstore, #Hlw, #Het, #Hgvk, #Hrp, #Huwl, #Hclock⟩
  iunfold reflFixed2 at Hf2
  icases Hf2 with ⟨%name, %td, %ps, %md, %sr, %weh, #Hdhf, #Hname, #Htd, #Hps, #Hmd, #Hsr, #Hweh⟩
  (try wp_auto)
  wp_apply (wp_FromContext (GoInterface.ok ctx)) $$ [$Hklog] as %lg -
  (try wp_auto)
  wp_apply (wp_NewRetryWithDeadline md _ c) as %rt Hrt
  (try wp_auto)
  ihave HI : iprop(∃ (e rt : GoInterface), "err" ∷ err_ptr ↦ e ∗ "retry" ∷ retry_ptr ↦ rt ∗
      "Hrt" ∷ retryOwn rt ∗ "Hst" ∷ ((∃ k', reflSt r γi (some k')) ∨ ctxSeen dch γd))
    $$ [err retry Hrt Hst]
  · iexists _, rt
    iframe
    icases Hst with (H | H)
    · ileft; iexists k; iexact H
    · iright; iexact H
  wp_for HI
  icases Hst with (⟨%k', Hst⟩ | #Hseen)
  · iunfold reflSt at Hst
    icases Hst with ⟨%v, %u, Hown, Hmisc, Hlast, %hrv⟩
    obtain ⟨⟨w0, hk', hv⟩, hpos⟩ := hrv
    subst hv hk'
    have hpos0 : 1 ≤ w0.toNat := hpos _ rfl
    obtain ⟨hne1, hne0⟩ := rvStr_pos w0 hpos0
    iunfold reflMisc at Hmisc
    icases Hmisc with ⟨%pr, %mn, %mx, Hpr, Hmn, Hmx⟩
    wp_apply_core (wp_select_stable ctx dch γd) $$ Hctx
    isplit
    · iintro #Hseen
      wp_auto
      wp_for_post
      (try wp_auto)
      iapply HΦ
      iright
      iexact Hseen
    wp_auto
    wp_apply (wp_Now c) $$ [$Hclk] as %t -
    (try wp_auto)
    wp_apply (wp_Seconds_ptr _ mn) $$ [$Htime $Hmn] as %f1 Hmn
    (try wp_auto)
    wp_apply wp_Float64 as %f2 -
    (try wp_auto)
    wp_apply (wp_Seconds_ptr _ mx) $$ [$Htime $Hmx] as %f3 Hmx
    (try wp_auto)
    wp_apply (wp_Seconds_ptr _ mn) $$ [$Htime $Hmn] as %f4 Hmn
    (try wp_auto)
    wp_apply (wp_LastSyncResourceVersion r (rvStr w0) u) $$ [$Hpkg $Hown] as Hown
    (try wp_auto)
    wp_if_destruct
    · exact absurd Hif hne1
    wp_if_destruct
    · exact absurd Hif hne0
    ihave #Henv2 := Henv
    iunfold reflEnv at Henv2
    icases Henv2 with ⟨#Hinv, #Hfifo, #Hlw, #Hty, #Hkeys⟩
    iunfold lwOk at Hlw
    icases Hlw with ⟨#HList, #HWatch⟩
    wp_apply HWatch $$ [timeoutSeconds]
    · iapply (lo_own_intro _ (some _))
      · rfl
      simp only [ownPtrD, ownBaseD]
      iexists _
      iframe
      ipureintro; rfl
    iintro %wv %werr %σw Hlo Hret Hargerr
    ihave Hret := watchRet_cases γa cfg res _ σw wv werr rfl rfl rfl $$ Hret
    icases Hret with (%hwe | ⟨%he, Hw⟩)
    · obtain ⟨hw, hne⟩ := hwe
      subst hw
      cases werr with
      | nil => exact absurd rfl hne
      | ok werr =>
      (try wp_auto)
      wp_apply (wp_isWatchErrorRetriable _) $$ [$Hpkg] as %cr -
      (try wp_auto)
      wp_if_destruct
      · wp_for_post
        (try wp_auto)
        iapply HΦ
        ileft
        iexists w0.toNat
        unfold reflSt reflMisc
        iexists (rvStr w0), u
        iframe
        ipureintro
        exact ⟨⟨w0, rfl, rfl⟩, hpos⟩
      · wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        (try wp_auto)
        wp_apply (wp_V_ptr logger_ptr lg _ _) $$ [$Hlogr $logger] as %lg' logger
        (try wp_auto)
        wp_apply (wp_Info lg' _ _ _ _) $$ [$Hlogr $Hsl] as -
        (try wp_auto)
        wp_apply Hdh as %d
        (try wp_auto)
        wp_apply (lc := 2) (wp_ClockAfter c d) $$ [$Hclk] as %ach %γach #Hbag
        (try wp_auto)
        wp_apply_core (wp_select_done_bag ctx dch γd ach γach) $$ Hctx Hbag [$Hlc1 $Hlc2]
        isplit
        · iintro #Hseen
          wp_auto
          wp_for_post
          (try wp_auto)
          iapply HΦ
          iright
          iexact Hseen
        · iintro %t'
          wp_auto
          wp_for_post
          iframe
          iexists _, rt
          iframe
          ileft
          iexists w0.toNat
          unfold reflSt reflMisc
          iexists (rvStr w0), u
          iframe
          ipureintro
          exact ⟨⟨w0, rfl, rfl⟩, hpos⟩
    · subst he
      icases Hw with ⟨%γw, %inits, %n0, #Hwat, Hcons, #Hσw, %hstart⟩
      have hst' := hstart
      unfold watchStartOk at hst'
      split at hst'
      · rename_i hc
        simp only [loOf] at hc
        exact absurd hc (fun h => h.elim hne1 hne0)
      obtain ⟨hinits, hiss⟩ := hst'
      subst hinits
      have hn0 := issued_rvStr σw w0 n0 hiss
      subst hn0
      (try wp_auto)
      ipersist propagateRVFromStart
      ihave HL0 : wL r γa γi res 0 (logStart (σw.tbl res).log n0, n0) $$ [Hown Hpr Hmn Hmx Hlast]
      · unfold wL reflMisc
        iexists u, σw
        iframe
        iframe #
        ipureintro
        exact ⟨hpos0, curOk_start res σw n0 ⟨_, hiss⟩⟩
      ihave #Hstep := watch_evStepOk r γa res γf γt γi γw _ $$ Hinv Hkeys
      wp_apply (wp_handleWatch ctx dch γd t wv γa γw res _ [] f γf (infObj γi res) et name td _ c
        errCh 0 (logStart (σw.tbl res).log n0, n0) (wL r γa γi res) (wC r γa γi res))
        $$ [$Hctx $Hwat $Hcons $HL0 $Hfifo $Hty $Herr $Hstep] as %err' Hpost
      · unfold cbOk
        imodintro
        iintro %i %p %rv %b %Φ' HC HΦ'
        iunfold wC at HC
        icases HC with ⟨%v', %u', %σ', Hown', Hmisc', Hlast', #Hσ', %hc⟩
        obtain ⟨hrv, hpos', hcur'⟩ := hc
        subst hrv
        wp_auto
        wp_apply (wp_setLastSyncResourceVersion r v' u' _) $$ [$Hpkg $Hown'] as Hown'
        (try wp_auto)
        unfold rvuTyOk at hrvu
        simp only [hrvu, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iapply HΦ'
        unfold wL
        iexists u', σ'
        iframe
        iframe #
        ipureintro
        exact ⟨hpos', hcur'⟩
      icases Hpost with ⟨%n', %p', Hcons', HL'⟩
      iunfold wL at HL'
      icases HL' with ⟨%u2, %σ2, Hown, Hmisc, Hlast, #Hσ2, %hl2⟩
      obtain ⟨hpos2, hcur2⟩ := hl2
      have hrv2 : rvRel (rvStr p'.2) (some p'.2.toNat) ∧ lastPos (some p'.2.toNat) :=
        ⟨⟨p'.2, rfl, rfl⟩, fun k hk => by cases hk; exact hpos2⟩
      iunfold retryOwn at Hrt
      icases Hrt with ⟨%rl, %rv, %rc, %hrt, Hrl, %hrv⟩
      subst hrt
      (try wp_auto)
      wp_apply (wp_After rl err') $$ [$Hpkg Hrl] as Hrt
      · unfold retryOwn
        iexists rl, rv, rc
        iframe
        ipureintro; exact ⟨rfl, hrv⟩
      (try wp_auto)
      cases err' with
      | nil =>
        (try wp_auto)
        wp_for_post
        iframe
        iexists _, _
        iframe
        ileft
        iexists p'.2.toNat
        unfold reflSt
        iexists (rvStr p'.2), u2
        iframe
        ipureintro; exact hrv2
      | ok e' =>
        (try wp_auto)
        wp_bind (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #(GoInterface.ok e'))) (Val #e2))
        iapply HerrIs
        · itrivial
        inext
        iintro %bis -
        cases bis
        · (try wp_auto)
          wp_apply (wp_isExpiredError _) $$ [$Hpkg] as %bexp -
          (try wp_auto)
          cases bexp
          · (try wp_auto)
            wp_apply (wp_IsTooManyRequests _) $$ [$Herrs] as %b429 -
            (try wp_auto)
            cases b429
            · (try wp_auto)
              wp_apply (wp_IsInternalError _) $$ [$Herrs] as %b500 -
              (try wp_auto)
              cases b500
              · (try wp_auto)
                warn_tac
                ret_refl
              · (try wp_auto)
                wp_apply (wp_ShouldRetry rl) $$ [$Hpkg $Hrt] as %bsr Hrt
                (try wp_auto)
                cases bsr
                · (try wp_auto)
                  warn_tac
                  ret_refl
                · (try wp_auto)
                  log_tac
                  cont_refl
            · (try wp_auto)
              log_tac
              wp_apply Hdh as %d
              (try wp_auto)
              wp_apply (lc := 2) (wp_ClockAfter c d) $$ [$Hclk] as %ach %γach #Hbag
              (try wp_auto)
              wp_apply_core (wp_select_done_bag ctx dch γd ach γach) $$ Hctx Hbag [$Hlc1 $Hlc2]
              isplit
              · iintro #Hseen
                ret_seen
              · iintro %t'
                wp_auto
                cont_refl
          · (try wp_auto)
            log_tac
            ret_refl
        · (try wp_auto)
          ret_refl
  · wp_apply_core (wp_select_seen dch γd) $$ Hseen
    wp_auto
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iright
    iexact Hseen

end proof

end cache
end EtcdGrove
end Perennial
