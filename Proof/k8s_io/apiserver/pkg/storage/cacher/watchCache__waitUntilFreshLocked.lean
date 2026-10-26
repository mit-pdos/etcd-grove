/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/watchCache__waitUntilFreshLocked.lean`. Lean-first (no Rocq counterpart).
Fresh already: no error. Otherwise: the progress requester's `Add` (and the deferred
`Remove`), the clock's `Now`, the deferred read-wait observation (the histogram's `WithContext`
chain, two valid labels), the timeout goroutine (`After`'s channel, then `Broadcast`), and the
loop: the cache's version under the read lock, the timeout's error, or `Wait` on the condition
variable over the read lock (`Cond.wp_Wait_with` at `rlocker_isLockerWith`), which gives the read
lock and the lock's resource back.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__waitUntilFreshLocked
public import Spec.k8s_io.apiserver.pkg.storage.cacher.progress.ConditionalProgressRequester__Add
public import Spec.k8s_io.apiserver.pkg.storage.cacher.progress.ConditionalProgressRequester__Remove
public import Spec.k8s_io.component_base.metrics.HistogramVec__WithContext
public import Spec.time.Duration__Seconds
public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable [store_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]

theorem watchCache.waitUntilFreshLocked.wp_proof
    (wp_Add : ConditionalProgressRequester.Add.spec (GF := GF) (hG := hG))
    (wp_Remove : ConditionalProgressRequester.Remove.spec (GF := GF) (hG := hG))
    (wp_WithContext : kmetrics.HistogramVec.WithContext.spec (GF := GF) (hG := hG))
    (wp_Seconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (wp_TooLarge : storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG)) :
    watchCache.waitUntilFreshLocked.spec (GF := GF) (hG := hG) := by
  intro wc γ Ψ ctx rv
  -- `time.Duration`'s methods resolve (its underlying `int64` is not an interface)
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  wp_start as ⟨#Hwc, Hrl, HP⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold isWC
  icases Hwc with ⟨%s, %c, %cfg, #Hs, #Hwcs, #Hc, #Hcond, #Hcfg, #Hcfgok, #Hguard⟩
  unfold cfgOk
  icases Hcfgok with ⟨%clk, %pr, %gr, #Hclk, #Hclkok, #Hpr, #Hprok, #Hgr, %Hutf⟩
  icases typedPointsto_split _ _ _ $$ Hgr with Hgr'
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hgr' with ⟨#Hgrg, #Hgrr, -⟩
  ihave #Pm : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.metrics $$ []
  · iPkgInit
  ihave #Hm : (k8s_io.apiserver.pkg.storage.cacher.cacherMetricsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pm
  icases Hm with ⟨%hv, #Hhv, %Hlab⟩
  ihave #Pcm : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.metrics $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pprog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.progress $$ []
  · iPkgInit
  ihave #Psto : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  iunfold wcLockP at HP
  icases HP with ⟨%st, HP⟩
  iunfold wcLockPSt at HP
  icases HP with ⟨Hrv, Hown⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_if_destruct
  · -- `rv == 0`
    (try wp_auto)
    iapply HΦ
    iframe Hrl
    iexists st
    unfold wcLockPSt
    iframe
    ipureintro; intro; left; simp_all
  have hpos : uint.Z (W64 0) < uint.Z rv := by
    have h0 := Hif
    have : uint.Z rv ≠ 0 := fun h => h0 (by word)
    word
  (try wp_auto)
  wp_if_destruct
  · -- fresh already
    (try wp_auto)
    iapply HΦ
    iframe Hrl
    iexists st
    unfold wcLockPSt
    iframe
    ipureintro; intro; right; assumption
  (try wp_auto)
  wp_apply (wp_Add pr) $$ []
  · iframe #
  (try wp_auto)
  unfold clockOk
  icases Hclkok with ⟨#HNow, #HSince, #HAfter⟩
  wp_bind (App (Val #(methods clk.ty go!"Now" clk.v)) (Val #()))
  iapply HNow
  inext
  iintro %t0
  (try wp_auto)
  wp_if_destruct
  · -- the timeout goroutine: `<-clock.After(blockTimeout)`, then `cond.Broadcast()`
    (try wp_auto)
    ipersist w
    wp_apply wp_fork
    · (try wp_auto)
      wp_bind (App (Val #(methods clk.ty go!"After" clk.v)) (Val _))
      iapply HAfter
      inext
      iintro %ch #Hch
      (try wp_auto)
      wp_bind (App (Val (chan.receive _root_.Perennial.time.Time.ty)) (Val #ch))
      iunfold chanRecvOk at Hch
      iapply Hch
      inext
      iintro %v %ok
      (try wp_auto)
      wp_apply (sync.Cond.wp_Broadcast c _) $$ []
      · iframe #
      (try wp_auto)
      itrivial
    (try wp_auto)
    ipersist resourceVersion
    ipersist startTime
    ihave IH : iprop(∃ st' : SnapSt,
        "Hrl" ∷ sync.ownRWMutexRLocked (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) ∗
        "Hrv" ∷ structFieldRef watchCache go!"resourceVersion" wc ↦{DFrac.own sync.rfrac} st'.2 ∗
        "Hown" ∷ wcsOwn γ sync.rfrac st') $$ [Hrl Hrv Hown]
    · iexists st; iframe
    wp_for IH
    wp_if_destruct
    · -- not fresh yet: the timeout, or wait
      (try wp_auto)
      wp_bind (App (Val #(methods clk.ty go!"Since" clk.v)) (Val _))
      iapply HSince
      inext
      iintro %d
      (try wp_auto)
      wp_if_destruct
      · -- the timeout: `NewTooLargeResourceVersionError`
        (try wp_auto)
        wp_apply (wp_TooLarge _ _ _) $$ [] as %err %Herr
        wp_for_post
        (try wp_auto)
        (try rw [decide_eq_true hpos])
        (try wp_auto)
        · (try wp_auto)
          wp_bind (App (Val #(methods clk.ty go!"Since" clk.v)) (Val _))
          iapply HSince
          inext
          iintro %d2
          (try wp_auto)
          wp_apply wp_Seconds as %f -
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hlsl, -⟩
          (try wp_auto)
          wp_apply (wp_WithContext hv [go!"group", go!"resource"] ctx) $$ [] as %vc #Hvc
          · iframe #; ipureintro; exact Hlab
          (try wp_auto)
          iunfold kmetrics.histCtxOk at Hvc
          wp_apply Hvc $$ [Hlsl] as %o ⟨-, #Hobs⟩
          · iframe
            ipureintro
            exact prometheus.labelValuesOk_two _ _ _ _ Hutf.1 Hutf.2
          (try wp_auto)
          wp_apply Hobs $$ []
          (try wp_auto)
          wp_apply (wp_Remove pr) $$ []
          · iframe #
          (try wp_auto)
          iapply HΦ
          iframe Hrl
          iexists st'
          unfold wcLockPSt
          iframe
          ipureintro; intro h; exact absurd h Herr
      · -- wait
        (try wp_auto)
        ihave #Hlw := sync.rlocker_isLockerWith (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) $$ Psync
        wp_apply (sync.Cond.wp_Wait_with c (sync.rlockerOf (structFieldRef watchCache go!"RWMutex" wc))
            (sync.ownRWMutex (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ))
            iprop(sync.ownRWMutexRLocked (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) ∗ ▷ wcLockP wc γ sync.rfrac))
          $$ [Hrl Hrv Hown] as ⟨Hrl, HP⟩
        · iframe #
          iframe Hrl
          inext
          iunfold wcLockP
          iexists st'
          unfold wcLockPSt
          iframe
        iunfold wcLockP at HP
        icases HP with ⟨%st'', HP⟩
        iunfold wcLockPSt at HP
        icases HP with ⟨Hrv, Hown⟩
        wp_for_post
        iframe
        iexists st''
        iframe
    · -- fresh: no error
      (try wp_auto)
      (try rw [decide_eq_true hpos])
      (try wp_auto)
      · (try wp_auto)
        wp_bind (App (Val #(methods clk.ty go!"Since" clk.v)) (Val _))
        iapply HSince
        inext
        iintro %d2
        wp_auto
        wp_apply wp_Seconds as %f -
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        (try wp_auto)
        wp_apply (wp_WithContext hv [go!"group", go!"resource"] ctx) $$ [] as %vc #Hvc
        · iframe #; ipureintro; exact Hlab
        (try wp_auto)
        iunfold kmetrics.histCtxOk at Hvc
        wp_apply Hvc $$ [Hlsl] as %o ⟨-, #Hobs⟩
        · iframe
          ipureintro
          exact prometheus.labelValuesOk_two _ _ _ _ Hutf.1 Hutf.2
        (try wp_auto)
        wp_apply Hobs $$ []
        (try wp_auto)
        wp_apply (wp_Remove pr) $$ []
        · iframe #
        (try wp_auto)
        iapply HΦ
        iframe Hrl
        iexists st'
        unfold wcLockPSt
        iframe
        ipureintro; intro _; right; simp_all <;> word
  · exfalso; rename_i h0 h1; simp_all

end proof

end cacher
end EtcdGrove
end Perennial
