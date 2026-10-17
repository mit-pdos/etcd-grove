/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__recvLoop.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__recvLoop
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Error

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.recvLoop.wp_proof
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.recvLoop.spec (GF := GF) (hG := hG) := by
  intro V G callSl wc γs Dn cd' γr
  wp_start as ⟨#Hwgs, #Hcs, Htok, #Hspsc, Hprod⟩
  ihave #Hwgs' := Hwgs
  iunfold isWGS at Hwgs'
  icases Hwgs' with ⟨%Hwnn, -, #Hfacts, %Hlg, -, -, -, -, -, -, -, #Frespc, #Fdonec, #Ferrc, -, #Flg,
    -, -, -, #Herr, -, #Hdone⟩
  iunfold watchSrvFacts at Hfacts
  icases Hfacts with ⟨-, #Hfacts⟩
  iunfold watchConnFacts at Hfacts
  icases Hfacts with ⟨-, -, -, -, -, -, -, #Heof, -⟩
  iunfold v3rpc.cliWatchStreamIs at Hcs
  iunfold cliBidiStreamIs at Hcs
  icases Hcs with ⟨%ci, %Hci, -, #HRecv, -⟩
  subst Hci
  wp_auto
  ihave HI : iprop(∃ (L : List v3rpc.WatchRespM) (sent : List Loc),
      "Htok" ∷ cliRecvTok (Rep := v3rpc.pbWatchResponse) γs L ∗ "Hprod" ∷ spscProducer γr sent ∗
      "%Hlen" ∷ ⌜sent.length = L.length⌝) $$ [Htok Hprod]
  · iexists [], []
    iframe
    ipureintro; rfl
  wp_for HI
  wp_bind (App (Val #(methods ci.ty go!"Recv" ci.v)) (Val #()))
  iapply HRecv $$ %L Htok
  inext
  iintro %resp %err Hr
  icases Hr with (⟨%Herr0, %m, Hm, HDn, Htok⟩ | ⟨%Hrn, #Heofe, %Hen, Htok, -⟩ | ⟨%Hrn, #Hse, Htok⟩)
  · subst Herr0
    ihave ⟨Htok, #Hlb⟩ := cliRecvTok_lb $$ Htok
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, G.respc,
        γr.chanName, resp
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · ihave #H := Hspsc
        unfold isSpsc
        icases H with ⟨$, -⟩
      iapply spsc_send_au γr G.respc _ _ sent resp _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hm HDn]
      · iframe
        iunfold respcElem
        iexists m, L
        iframe
        have Hk : (((sent.length : Nat) : Int)).toNat = L.length := by simp [Hlen]
        rw [Hk]
        iframe
        isplitl
        · iunfold v3rpc.downLbW; iunfold downLb at Hlb; iexact Hlb
        ipureintro; rfl
      inext
      iintro Hprod
      (try wp_auto)
      wp_for_post
      iframe
      iexists L ++ [m], sent ++ [resp]
      iframe
      ipureintro; simp [Hlen]
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdone
      iapply broadcast_chan_receive $$ Hdone
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · cases err with
    | nil => exact absurd rfl Hen
    | ok ei =>
    iunfold eofOk at Heof
    ihave ⟨%Hok, #Hst⟩ := Heof $$ %(GoInterface.ok ei) Heofe
    wp_auto
    wp_apply wp_zapError as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    wp_auto
    wp_apply +noauto wp_Debug V.lg _ _ $$ []
    · iframe #; ipureintro; exact Hlg
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.errc,
        G.γerr, GoInterface.ok ei
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iapply is_bag_is_chan $$ Herr
      iapply bag_send_au G.γerr G.errc errP _ _ $$ [$Hlc1 $Hlc2] Herr [] 
      · iunfold errP
        isplitr
        · ipureintro; exact Hen
        isplitr
        · iright; iexact Heofe
        iexact Hst
      inext
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdone
      iapply broadcast_chan_receive $$ Hdone
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · ihave #Hse' := Hse
    iunfold cliStreamErr at Hse'
    icases Hse' with ⟨%Hok, #Hst, -⟩
    cases err with
    | nil => exact absurd rfl Hok.1
    | ok ei =>
    wp_auto
    wp_apply wp_zapError as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    wp_auto
    wp_apply +noauto wp_Debug V.lg _ _ $$ []
    · iframe #; ipureintro; exact Hlg
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.errc,
        G.γerr, GoInterface.ok ei
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iapply is_bag_is_chan $$ Herr
      iapply bag_send_au G.γerr G.errc errP _ _ $$ [$Hlc1 $Hlc2] Herr [] 
      · iunfold errP
        isplitr
        · ipureintro; exact Hok.1
        isplitr
        · ileft; iexact Hse
        iexact Hst
      inext
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdone
      iapply broadcast_chan_receive $$ Hdone
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
