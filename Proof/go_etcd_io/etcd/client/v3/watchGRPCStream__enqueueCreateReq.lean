/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__enqueueCreateReq.lean` (etcd-io/etcd#21065).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__enqueueCreateReq

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

theorem watchGRPCStream.enqueueCreateReq.wp_proof :
    watchGRPCStream.enqueueCreateReq.spec (GF := GF) (hG := hG) := by
  intro V G callSl Q sent req
  wp_start as ⟨#HG, #HQ, Hprod, Hel⟩
  ihave #HG' := HG
  iunfold isWGS at HG'
  icases HG' with ⟨%Hwgs, -, #Hsf, %Hlg, #Fowner, #Fremote, #FcallOpts, #Fctx, #FctxKey, #Fcancel,
    #Freqc, #Frespc, #Fdonec, #Ferrc, #Fclosingc, #Flg, #HGctx, #HGcancel, #Hreqb, #Herrb, #Hclb,
    #HGdone⟩
  ihave #HQ' := HQ
  iunfold sendQIs at HQ'
  icases HQ' with ⟨#Fcc, #Fbc, #Hcc, #Hbc⟩
  ihave #HGc := HGctx
  iNamedPrefix HGc "W"
  wp_auto
  wp_apply +noauto WHDone as %dch %dγ #Hdone
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, Q.cc, Q.γc.chanName, req
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · ihave #H := Hcc
      unfold isSpsc
      icases H with ⟨$, -⟩
    iapply spsc_send_au Q.γc Q.cc _ _ sent req _ $$ Hcc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hel]
    · iframe
      iunfold sendElem at Hel; iunfold sendElem; iexact Hel
    inext
    iintro Hprod
    wp_auto
    iapply HΦ
    iexists sent ++ [req]
    iframe
    ipureintro; left; rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ HGdone
    iapply broadcast_chan_receive $$ HGdone
    iintro -
    wp_auto
    iapply HΦ
    iexists sent
    iframe
    ipureintro; right; rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, dγ
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone
    iintro -
    wp_auto
    iapply HΦ
    iexists sent
    iframe
    ipureintro; right; rfl
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
