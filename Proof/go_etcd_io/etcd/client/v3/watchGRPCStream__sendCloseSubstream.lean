/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__sendCloseSubstream.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__sendCloseSubstream
public import Perennial.Proof.time.Link

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
theorem watchGRPCStream.sendCloseSubstream.wp_proof :
    watchGRPCStream.sendCloseSubstream.spec (GF := GF) (hG := hG) := by
  intro V P wgs resp v
  wp_start as ⟨#Hws, Hprod, Hresp, Hhdr, %Hv, #Hse⟩
  ihave #Hws' := Hws
  iunfold wsIs at Hws'
  icases Hws' with ⟨#Hro, #Houtc, -, -, #Hspsc, -, -, #Hctx, -, %Hwsp, -⟩
  iunfold wrRO at Hro
  icases Hro with ⟨#Hctxf, -⟩
  ihave #Hctx1 := Hctx
  iNamed Hctx1
  obtain ⟨Hhn, Hevn, Hcr, Hca, Hcrt⟩ := Hv
  iStructNamedPrefix Hhdr "H"
  iclear Hstate HClusterId HMemberId HRaftTerm HLeaderId HunknownFields HsizeCache H_
  ipersist HRevision
  iunfold outcProd at Hprod
  icases Hprod with ⟨%sent, %C, Hprod, Hauth, %HC, Hc2a⟩
  -- the second cursor (K2e-7) stays too: a canceled response
  ihave Hc2e : iprop(|==> (⌜P.γ.cpl = false⌝ ∨ ∃ c2 c2' : w64,
      monoListIdxOwn P.γ.cur2 sent.length c2 ∗ monoListIdxOwn P.γ.cur2 (sent.length + 1) c2' ∗
      watchRespOk (EM := V.EM) P.o.key c2 c2' v (RespModel.mk [] (W64 0) true false (W64 0))))
      $$ [Hc2a]
  · iunfold cur2Auth at Hc2a
    icases Hc2a with (%Hcf | ⟨%C2, Ha2, %HC2⟩)
    · imodintro; ileft; ipureintro; exact Hcf
    obtain ⟨c2, Hc2⟩ : ∃ c, C2[sent.length]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    imod monoListAuthOwn_update_app (GF := GF) [c2] $$ Ha2 with ⟨-, #Hlb2⟩
    ihave #Hj1 := monoListIdxOwn_get (GF := GF) sent.length c2
      (by rw [List.getElem?_append_left (by omega)]; exact Hc2) $$ Hlb2
    ihave #Hj2 := monoListIdxOwn_get (GF := GF) (sent.length + 1) c2
      (by rw [List.getElem?_append_right (by omega)]; simp [HC2]) $$ Hlb2
    imodintro
    iright
    iexists c2, c2
    iframe Hj1 Hj2
    unfold watchRespOk
    isplitr
    · ipureintro; simp
    ileft
    iframe Hse
    ipureintro
    exact ⟨Or.inr (Or.inr Hca), rfl⟩
  imod Hc2e with #Hc2e
  -- the cursor stays where it is: its last position, twice
  obtain ⟨c, Hc⟩ : ∃ c, C[sent.length]? = some c :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  imod monoListAuthOwn_update_app (GF := GF) [c] $$ Hauth with ⟨Hauth, #Hlb⟩
  ihave #Hi1 := monoListIdxOwn_get (GF := GF) sent.length c
    (by rw [List.getElem?_append_left (by omega)]; exact Hc) $$ Hlb
  ihave #Hi2 := monoListIdxOwn_get (GF := GF) (sent.length + 1) c
    (by rw [List.getElem?_append_right (by omega)]; simp [HC]) $$ Hlb
  ihave Hel : rangeWatchElem (GF := GF) (EM := V.EM) P.γ V.pfx P.o P.rev (sent.length : Int) v $$ [HRevision]
  · unfold rangeWatchElem
    iexists (RespModel.mk [] (W64 0) true false (W64 0)), c, c
    simp only [Int.toNat_natCast]
    iframe Hi1 Hi2 Hse
    isplitr
    · unfold eventsAt
      iexists []
      rw [Hevn]
      isplitr
      · iapply ownSlice_nil
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %ev %e %h
      simp at h
    isplitr
    · unfold watchHdrOwn hdrAt
      simp only [↓reduceIte]
      iright
      isplitr
      · ipureintro; exact Hhn
      rw [show (W64 0 : w64) = (zero_val etcdserverpb.ResponseHeader).Revision' from rfl]
      iexact HRevision
    isplitr
    · ipureintro; exact ⟨Hcr, Hca, Hcrt⟩
    isplitr
    · unfold rangeWatchRespOk
      isplitr
      · ipureintro
        refine ⟨List.Pairwise.nil, fun e he => by simp at he, rfl⟩
      imodintro
      iintro %i %e %h
      simp at h
    iexact Hc2e
  (try wp_auto)
  wp_apply +noauto HDone as %dch %dγ #Hdone
  (try wp_auto)
  wp_apply +noauto time.wp_After as %tch %γt #Htch
  wp_auto_lc 3
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists go_etcd_io.etcd.client.v3.WatchResponse, inferInstance, inferInstance, inferInstance,
      inferInstance, P.outc, P.γ.spsc.chanName, v
    isplit
    · ipureintro; exact ⟨rfl, rfl⟩
    isplit
    · ihave #H := Hspsc
      unfold isSpsc
      icases H with ⟨$, -⟩
    iapply spsc_send_au P.γ.spsc P.outc _ _ sent v _ $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [Hprod Hel]
    · iframe
    inext
    iintro Hprod
    (try wp_auto)
    wp_apply wp_spsc_close P.γ.spsc P.outc _ (fun _ => iprop(True)) _ $$ [$Hspsc $Hprod]
    (try wp_auto)
    iapply HΦ; itrivial
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
    (try wp_auto)
    wp_apply wp_spsc_close P.γ.spsc P.outc _ (fun _ => iprop(True)) _ $$ [$Hspsc $Hprod]
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %t -
    (try wp_auto)
    wp_apply wp_spsc_close P.γ.spsc P.outc _ (fun _ => iprop(True)) _ $$ [$Hspsc $Hprod]
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
