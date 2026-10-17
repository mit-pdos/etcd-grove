/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__sendLoop.lean` (etcd-io/etcd#21065).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__sendLoop

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

set_option maxHeartbeats 0 in
theorem watchGRPCStream.sendLoop.wp_proof :
    watchGRPCStream.sendLoop.spec (GF := GF) (hG := hG) := by
  intro V G callSl Q wc γs Dn cd' L0 rc0 rb0
  wp_start as ⟨#HG, #HQ, #Hcs, Htok, Hcc0, Hbc0⟩
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
  iunfold v3rpc.cliWatchStreamIs at Hcs
  iunfold cliBidiStreamIs at Hcs
  icases Hcs with ⟨%ci, %Hci, #HSend, -, -, -⟩
  subst Hci
  wp_auto
  ihave HI : iprop(∃ (L : List v3rpc.WatchReqM) (rc rb : List Loc),
      "Htok" ∷ cliSendTok (Req := v3rpc.pbWatchRequest) γs L ∗
      "Hccons" ∷ spscConsumer Q.γc rc ∗ "Hbcons" ∷ spscConsumer Q.γb rb) $$ [Htok Hcc0 Hbc0]
  · iexists L0, rc0, rb0
    iframe
  wp_for HI
  wp_apply +noauto WHDone as %dch %dγ #Hdone
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, Q.cc, Q.γc.chanName
    isplit
    · ipureintro; rfl
    isplit
    · ihave #H := Hcc
      unfold isSpsc
      icases H with ⟨$, -⟩
    iapply spsc_rcv_au Q.γc Q.cc _ _ rc _ $$ Hcc [$Hlc1 $Hlc2] Hccons
    inext
    iintro %req %ok Hrcv
    wp_auto
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hrcv with ⟨Hel, Hccons⟩
    iunfold sendElem at Hel
    icases Hel with ⟨%m, Hm, Hup⟩
    ihave Hup := watchUp_any V.R.γ L.length m $$ Hup
    wp_auto
    wp_bind (App (Val #(methods ci.ty go!"Send" ci.v)) (Val #req))
    iapply HSend $$ %L %req %m [Htok Hm Hup]
    · iframe
    inext
    iintro %err ⟨-, Hres⟩
    icases Hres with (⟨%Herr, Htok⟩ | ⟨#Hse, %L', -, Htok⟩)
    · subst Herr
      wp_auto
      wp_for_post
      iframe
      iexists L ++ [m], rc ++ [req], rb
      iframe
    · ihave #Hse' := Hse
      iunfold cliStreamErr at Hse'
      icases Hse' with ⟨%Hok, -, -⟩
      cases err with
      | nil => exact absurd rfl Hok.1
      | ok ei =>
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, Q.bc, Q.γb.chanName
    isplit
    · ipureintro; rfl
    isplit
    · ihave #H := Hbc
      unfold isSpsc
      icases H with ⟨$, -⟩
    iapply spsc_rcv_au Q.γb Q.bc _ _ rb _ $$ Hbc [$Hlc1 $Hlc2] Hbcons
    inext
    iintro %req %ok Hrcv
    wp_auto
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    simp only [↓reduceIte]
    icases Hrcv with ⟨Hel, Hbcons⟩
    iunfold sendElem at Hel
    icases Hel with ⟨%m, Hm, Hup⟩
    ihave Hup := watchUp_any V.R.γ L.length m $$ Hup
    wp_auto
    wp_bind (App (Val #(methods ci.ty go!"Send" ci.v)) (Val #req))
    iapply HSend $$ %L %req %m [Htok Hm Hup]
    · iframe
    inext
    iintro %err ⟨-, Hres⟩
    icases Hres with (⟨%Herr, Htok⟩ | ⟨#Hse, %L', -, Htok⟩)
    · subst Herr
      wp_auto
      wp_for_post
      iframe
      iexists L ++ [m], rc, rb ++ [req]
      iframe
    · ihave #Hse' := Hse
      iunfold cliStreamErr at Hse'
      icases Hse' with ⟨%Hok, -, -⟩
      cases err with
      | nil => exact absurd rfl Hok.1
      | ok ei =>
      wp_auto
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
    · iapply ownBroadcastChan_is_chan $$ HGdone
    iapply broadcast_chan_receive $$ HGdone
    iintro -
    wp_auto
    wp_for_post
    iapply HΦ
    itrivial
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
    wp_for_post
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
