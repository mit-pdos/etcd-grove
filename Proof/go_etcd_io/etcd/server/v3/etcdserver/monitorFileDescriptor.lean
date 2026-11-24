/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/monitorFileDescriptor.lean` (`metrics.go`), over
its body (prove-ps2-srvgoroutines, 2026-11-24, etcd-grove#42; until then a trust-boundary axiom): the
ticker loop over the trusted models of etcd's `runtime.FDUsage`/`FDLimit`, the gauges `fdUsed` and
`fdLimit` (the package's fact, `srvApplyLoopInit`), zap, and the `select` on the ticker's channel and
the stop channel `done`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.monitorFileDescriptor
public import Spec.go_etcd_io.etcd.pkg.v3.runtime.FDUsage
public import Spec.go_etcd_io.etcd.pkg.v3.runtime.FDLimit
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Uint64
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem monitorFileDescriptor.wp_proof
    (hNew : time.NewTicker.spec (GF := GF) (hG := hG))
    (hStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (hUse : runtime.FDUsage.spec (GF := GF) (hG := hG))
    (hLim : runtime.FDLimit.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG)) :
    monitorFileDescriptor.spec (GF := GF) (hG := hG) := by
  intro lg done
  wp_start as ⟨#Hlg, #Hstop0⟩
  iunfold stopChan at Hstop0
  icases Hstop0 with ⟨%γs, #Hstop⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave Hsi : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, ⟨-, -, -, -, -, -, ⟨%gu, #Hgu, #Hgus⟩, ⟨%gl, #Hgl, #Hgls⟩⟩⟩
  iunfold gaugeSetSpec at Hgus Hgls
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hNew as %t %tch %γt #Ht0
  · ipureintro; decide
  ihave #Ht' := Ht0
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨#HC, #HI, #HR, #Hbag⟩
  (try wp_auto)
  wp_for
  wp_apply hUse as %used %err ⟨-, #Hue⟩
  (try wp_auto)
  by_cases he : err = GoInterface.nil
  · subst he
    (try wp_auto)
    wp_apply Hgus
    (try wp_auto)
    wp_apply hLim as %limit %err' ⟨-, #Hle⟩
    (try wp_auto)
    by_cases he' : err' = GoInterface.nil
    · subst he'
      (try wp_auto)
      wp_apply (lc := 2) Hgls
      (try wp_auto)
      -- `if used >= limit/5*4 { lg.Warn(...) }`
      wp_if_destruct
      · wp_apply hU64 as %f1 -
        (try wp_auto)
        wp_apply hU64 as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
        isplitr
        · ipureintro; rfl
        iintro %fs ⟨-, -⟩
        (try wp_auto)
        wp_apply hWarn lg _ _ $$ []
        · iframe #
        (try wp_auto)
        wp_apply_core chan.wp_select_blocking
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply is_bag_is_chan $$ Hbag
          iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
          inext
          iintro %tm' -
          wp_auto
          wp_for_post
          iframe
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done, γs
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply ownStopChan_is_chan $$ Hstop
          iapply stop_chan_receive done γs _ _ .Unknown $$ Hstop
          iintro ⟨-, -⟩
          wp_auto
          wp_for_post
          wp_apply hStop
          · iexists tch, γt; iexact Ht0
          iapply HΦ
          itrivial
        iapply BigAndL.bigAndL_nil.2
        itrivial
      · wp_apply_core chan.wp_select_blocking
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply is_bag_is_chan $$ Hbag
          iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
          inext
          iintro %tm' -
          wp_auto
          wp_for_post
          iframe
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done, γs
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply ownStopChan_is_chan $$ Hstop
          iapply stop_chan_receive done γs _ _ .Unknown $$ Hstop
          iintro ⟨-, -⟩
          wp_auto
          wp_for_post
          wp_apply hStop
          · iexists tch, γt; iexact Ht0
          iapply HΦ
          itrivial
        iapply BigAndL.bigAndL_nil.2
        itrivial
    · -- `FDLimit` failed: `lg.Warn(..., zap.Error(err))`, return
      obtain ⟨ei, rfl⟩ : ∃ ei, err' = GoInterface.ok ei := by
        cases err' with
        | nil => exact absurd rfl he'
        | ok ei => exact ⟨ei, rfl⟩
      (try wp_auto)
      wp_apply hErr as %fe -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
      isplitr
      · ipureintro; rfl
      iintro %fs ⟨-, -⟩
      (try wp_auto)
      wp_apply hWarn lg _ _ $$ []
      · iframe #
      (try wp_auto)
      wp_for_post
      wp_apply hStop
      · iexists tch, γt; iexact Ht0
      iapply HΦ
      itrivial
  · -- `FDUsage` failed
    obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by
      cases err with
      | nil => exact absurd rfl he
      | ok ei => exact ⟨ei, rfl⟩
    (try wp_auto)
    wp_apply hErr as %fe -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field)
    isplitr
    · ipureintro; rfl
    iintro %fs ⟨-, -⟩
    (try wp_auto)
    wp_apply hWarn lg _ _ $$ []
    · iframe #
    (try wp_auto)
    wp_for_post
    wp_apply hStop
    · iexists tch, γt; iexact Ht0
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
