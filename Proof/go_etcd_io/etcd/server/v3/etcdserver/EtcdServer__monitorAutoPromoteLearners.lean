/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__monitorAutoPromoteLearners.lean`
(PR `etcd-io/etcd#21744`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__monitorAutoPromoteLearners
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Receive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Perennial.Proof.time.Link
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.monitorAutoPromoteLearners.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hRecv : notify.Notifier.Receive.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hTry : EtcdServer.tryAutoPromoteLearners.spec (GF := GF) (hG := hG)) :
    EtcdServer.monitorAutoPromoteLearners.spec (GF := GF) (hG := hG) := by
  intro s lg fc stc
  wp_start as ⟨#Hmpre, Hlr, Hfcr⟩
  ihave #Hmpre' := Hmpre
  iunfold srvMonitorAutoPromotePre at Hmpre'
  icases Hmpre' with ⟨#Hpre, #Hfcf, #Hstcf, #Hstc, #Hlead, ⟨%mvi, #Hmvi⟩⟩
  ihave #Hpre' := Hpre
  iunfold srvAutoPromotePre at Hpre'
  icases Hpre' with ⟨#Hlgf, %Hlgnn, ⟨%lgMu, #Hlgmu⟩, ⟨%mid, #Hmid⟩, -⟩
  iunfold stopChan at Hstc
  icases Hstc with ⟨%γst, #Hstc'⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply (hLg s lg) $$ [Hlr] as ⟨%_, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  wp_apply (hInfo lg go!"starting auto-promote-learners monitor" slice.nil) $$ []
  · iframe #; ipureintro; exact Hlgnn
  wp_for
  wp_apply (hRecv fc) $$ [Hfcr] as %fch ⟨Hfcr, #Hfch⟩
  · iframe #; iframe Hfcr
  iunfold notifyChan at Hfch
  icases Hfch with ⟨%γfc, #Hfch'⟩
  wp_apply (lc := 2) time.wp_After as %tch %γt #Hbag
  wp_apply_core chan.wp_select_blocking
  -- `case <-s.firstCommitInTerm.Receive():`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, fch, γfc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hfch'
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hfch'
    iintro ⟨-, -⟩
    wp_auto
    wp_apply (hLead s mid) $$ [] as %b -
    · iframe #
    cases b
    · wp_auto
      wp_for_post
      iframe
    · wp_auto
      wp_apply (hTry s lg) $$ [Hlr] as Hlr
      · iframe #; iframe Hlr
      wp_for_post
      iframe
  -- `case <-time.After(monitorVersionInterval):`
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
    wp_apply (hLead s mid) $$ [] as %b -
    · iframe #
    cases b
    · wp_auto
      wp_for_post
      iframe
    · wp_auto
      wp_apply (hTry s lg) $$ [Hlr] as Hlr
      · iframe #; iframe Hlr
      wp_for_post
      iframe
  -- `case <-s.stopping:`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hstc'
    iapply stop_chan_receive _ _ _ _ _ $$ Hstc'
    iintro ⟨-, -⟩
    wp_auto
    wp_apply (hInfo lg go!"server has stopped; stopping auto-promote-learners monitor" slice.nil) $$ []
    · iframe #; ipureintro; exact Hlgnn
    wp_for_post
    iapply HΦ
    iframe Hlr Hfcr
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
