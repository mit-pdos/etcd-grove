/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watcher__RequestProgress.lean` (unit K2e-9). Lean-first
(no Rocq counterpart). The retry (`<-donec` with no close error: the stream was dropped) is Löb
induction (`iloeb`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__RequestProgress
public import Spec.go_etcd_io.etcd.client.v3.watcher__newWatcherGRPCStream
public import Spec.go_etcd_io.etcd.client.v3.streamKeyFromCtx
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas

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
theorem watcher.RequestProgress.wp_proof
    (wp_key : streamKeyFromCtx.spec (GF := GF) (hG := hG))
    (wp_newStream : watcher.newWatcherGRPCStream.spec (GF := GF) (hG := hG)) :
    watcher.RequestProgress.spec (GF := GF) (hG := hG) := by
  intro V w ctx cs
  iloeb as IH
  wp_start as ⟨#Hw, #Hctx⟩
  ihave #Hw' := Hw
  iunfold isClientWatcher at Hw'
  icases Hw' with ⟨%callSl, %vs, %Hwnn, #Hrem, #Hco, #Hvs, #Hok, #Hlg, #Hmu, #Hf, %Hlgb⟩
  obtain ⟨Hlgnn, Hb⟩ := Hlgb
  ihave #Hf' := Hf
  iunfold watchSrvFacts at Hf'
  icases Hf' with ⟨-, Hcf⟩
  iunfold watchConnFacts at Hcf
  icases Hcf with ⟨-, -, -, -, -, #HeN, #HcA, -, -⟩
  iunfold ctxErrClientAllW at HcA
  ihave #Hce := HcA $$ %ctx %cs Hctx
  iunfold ctxErrClient at Hce
  wp_auto
  wp_apply wp_key as %ckey -
  irename ctx => Hctxp
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold watcherMu at HR
  icases HR with ⟨%m, Hst, HM⟩
  wp_auto
  icases HM with (%Hnil | ⟨%M, HM, #HMs⟩)
  · subst Hnil
    simp only [show (null : Loc) = map.nil from rfl, _root_.decide_true]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst]
    · inext; unfold watcherMu; iexists map.nil; iframe Hst; ileft; ipureintro; rfl
    iunfold errorsNewOk at HeN
    wp_apply HeN as %e %He #Hse
    iapply HΦ
    iexact Hse
  by_cases hm : m = map.nil
  · simp only [hm, _root_.decide_true]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HM]
    · inext; unfold watcherMu; iexists map.nil; iframe Hst; iright; iexists M; iframe HM; iframe #
    iunfold errorsNewOk at HeN
    wp_apply HeN as %e %He #Hse
    iapply HΦ
    iexact Hse
  simp only [hm, _root_.decide_false]
  wp_auto
  wp_apply wp_map_lookup1 go.string go_etcd_io.etcd.client.v3.watchGRPCStream.ty.PointerType m M ckey
    (DFrac.own 1) $$ [$HM] as HM
  wp_join iprop(∃ (G : WgsPrm GF) (M' : GMap GoString Loc), wgs_ptr ↦ G.wgs ∗ m ↦$ M' ∗
      (□ [∗map] _k ↦ x ∈ M', ∃ G' : WgsPrm GF, ⌜G'.wgs = x ∧ G'.w = w⌝ ∗ isWGS V G' callSl) ∗
      ⌜G.w = w⌝ ∗ isWGS V G callSl ∗ w_ptr ↦ w ∗ ctx_ptr ↦ GoInterface.ok ctx ∗
      ctxKey_ptr ↦ ckey ∗ watcherF w go!"streams" ↦ m)
    with [wgs HM w Hctxp ctxKey Hst] as ⟨%G, %M', wgs, HM, #HMs', %HGw, #HG, w, Hctxp, ctxKey, Hst⟩
  · wp_apply wp_newStream V w ctx cs $$ [] as %wgs' ⟨%G, %callSl', %HGeq, #Hco', #HG⟩
    · iframe #; ipureintro; exact Hb
    icombine Hco Hco' gives %Hcs
    obtain ⟨-, rfl⟩ := Hcs
    wp_apply wp_mapInsert go.string m M ckey wgs' $$ [$HM] as HM
    wp_join_done
    iexists G, _
    iframe
    rw [← HGeq.1]
    iframe
    iframe #
    isplitr
    · iintro !>
      iapply BigSepM.bigSepM_insert_elim $$ [] HMs
      iexists G
      iframe #
      ipureintro; exact ⟨rfl, HGeq.2⟩
    ipureintro; exact HGeq.2
  · cases h : M !! ckey with
    | none => exact absurd (by simp [h]; rfl) Hif
    | some x =>
      simp only [h, Option.getD_some] at Hif ⊢
      ihave ⟨%G, %HGx, #HG⟩ := BigSepM.bigSepM_lookup h $$ HMs
      iexists G, M
      rw [HGx.1]
      iframe
      iframe #
      ipureintro; exact HGx.2
  iunfold isWGS at HG
  icases HG with ⟨%Hgnn, #Hcv, #Hsf, %Hlg', #Howner, #Hremote, #Hcallo, #Hgctx, #Hckey, #Hcancel,
    #Hreqc, #Hrespc, #Hdonec, #Herrc, #Hclosingc, #Hglg, #HisCtx, #Hcspec, #Hbreq, #Hberr, #Hbcl,
    #Hbdone, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hst HM]
  · inext
    unfold watcherMu
    iexists m
    iframe Hst
    iright
    iexists M'
    iframe HM
    iframe #
  ihave #Hctx1 := Hctx
  iNamed Hctx1
  wp_apply +noauto HDone as %dch %dγ #Hdone
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, G.reqc, G.γreq,
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.progressRequest.ty) #«$r0_ptr»)
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · iapply is_bag_is_chan $$ Hbreq
    iapply bag_send_au $$ [$Hlc1 $Hlc2] Hbreq []
    · unfold reqP
      iright
      iexists «$r0_ptr»
      ipureintro; rfl
    inext
    wp_auto
    iapply HΦ
    iapply statusErrOk_nil
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
    wp_apply Hce $$ %Broadcast.Pending as %e2 He2 %Hc2 #Hse -
    iapply HΦ
    iexact Hse
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, G.donec, G.γdone
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hbdone
    iapply broadcast_chan_receive $$ Hbdone
    iintro ⟨#Hpub, -⟩
    iunfold closeErrPub at Hpub
    icases Hpub with ⟨%e, #Hce', #Hse⟩
    wp_auto
    cases e with
    | ok i =>
      wp_auto
      iapply HΦ
      iexact Hse
    | nil =>
      wp_auto
      rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty)
        (m := go!"RequestProgress")]
      wp_apply IH $$ [] as %err #Herr
      · iframe #
      iapply HΦ
      iexact Herr
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
