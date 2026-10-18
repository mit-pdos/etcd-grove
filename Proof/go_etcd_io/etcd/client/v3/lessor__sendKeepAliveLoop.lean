/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__sendKeepAliveLoop.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__sendKeepAliveLoop
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem lessor.sendKeepAliveLoop.wp_proof
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    lessor.sendKeepAliveLoop.spec (GF := GF) (hG := hG) := by
  intro l addr st γ Dn cd L
  wp_start as ⟨#Hl, #Hst, Htok⟩
  iunfold lessorAt at Hl
  icases Hl with ⟨%dc, %γd, %sc, %scd, %lg, %d, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  iunfold cliBidiStreamIs at Hst
  icases Hst with ⟨%ci, %Hci, #HSend, -, -, #HCtx⟩
  subst Hci
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ipersist l
  ipersist stream
  ihave IH : iprop(∃ L' : List w64, "Htok" ∷ cliSendTok (Req := pbLeaseKeepAliveRequest) γ L') $$ [Htok]
  · iexists L; iframe
  wp_for IH
  (try wp_auto)
  wp_apply time.wp_Now as %now -
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herr⟩
  (try wp_auto)
  ihave Hnil := ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1)
  ihave Hnilcap := ownSliceCap_nil (V := w64) (GF := GF)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List w64) (_ : Int) =>
      iprop(∃ (k0 : Loc) (i0 : w64) (tsl : GoSlice) (ids : List w64),
      "HM" ∷ ([∗map] _id ↦ ka ∈ mm, kaOwn (GF := GF) ka) ∗
      "ka" ∷ ka_ptr ↦ k0 ∗ "id" ∷ id_ptr ↦ i0 ∗ "now" ∷ now_ptr ↦ now ∗
      "tosend" ∷ tosend_ptr ↦ tsl ∗ "Htsl" ∷ tsl ↦* ids ∗
      "Htcap" ∷ ownSliceCap w64 tsl (DFrac.own 1)))
    _ _ _ mref mm (DFrac.own 1) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [HM ka id now tosend Hnil Hnilcap]
  · iexists _, _, slice.nil, []
    simp only [named]
    iframe
    iframe #
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
    iNamed HP
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) ka)
      (m := mm) Hmv).1 $$ HM with ⟨Hka, HMback⟩
    iunfold kaOwn at Hka
    icases Hka with ⟨%chsS, %ctxsS, %chs, %ctxs, %dl, %nk, %kd, %γkd, Hchs, Hchsl, Hchscap,
      Hctxs, Hctxsl, Hctxscap, %Hlen, Hdl, Hnk, #Hkd, Hpend, Htoks, #Hctxok⟩
    wp_apply time.Time.wp_ptr_Before $$ [$Hnk] as %bb Hnk
    ihave HM : iprop([∗map] _id ↦ ka ∈ mm, kaOwn (GF := GF) ka) $$ [HMback Hchs Hchsl Hchscap Hctxs
        Hctxsl Hctxscap Hdl Hnk Hpend Htoks]
    · iapply HMback
      unfold kaOwn
      iexists chsS, ctxsS, chs, ctxs, _, _, kd, γkd
      iframe
      iframe #
      ipureintro; exact Hlen
    wp_if_destruct
    · (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _, _
      simp only [named]
      iframe
    · (try wp_auto)
      wp_apply wp_slice_literal (V := w64) [key]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [Htsl Htcap Hsl1] as %tsl' ⟨Htsl, Htcap, -⟩
      · iframe
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _, _, _
      simp only [named]
      iframe
  iintro HP Hm
  iNamed HP
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herr]
  · inext; unfold lessorInv; iexists mref, mm, stv, scf, e; iframe; iframe #
  (try wp_auto)
  ihave %Hsll := ownSlice_len $$ Htsl
  ihave IH2 : iprop(∃ (n i0 : w64) (L2 : List w64),
      "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ i0 ∗ "Htsl" ∷ tsl ↦* ids ∗
      "Htok" ∷ cliSendTok (Req := pbLeaseKeepAliveRequest) γ L2 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ids.length⌝) $$ [i id Htsl Htok]
  · iexists W64 0, _, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH2
  wp_if_destruct
  · have Hlt : sint.nat n < ids.length := by word
    have Hc : ids[sint.nat n]? = some (ids[sint.nat n]'Hlt) := List.getElem?_eq_getElem Hlt
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z tsl.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index tsl (sint.Z n) _ (DFrac.own 1) (ids[sint.nat n]'Hlt) Hn.1
      $$ [Htsl] as Htsl
    · iframe; ipureintro; exact Hc
    (try wp_auto)
    ihave #HS := HSend $$ %L2 %«$r0_ptr» %(ids[sint.nat n]'Hlt)
    wp_apply HS $$ [Htok «$r0»] as %err ⟨-, Hres⟩
    · iframe
      try (ipureintro; rfl)
    icases Hres with (⟨%Herr, Htok⟩ | ⟨#Hse, %L3, %HL3, Htok⟩)
    · subst Herr
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _, _
      iframe
      ipureintro; constructor <;> word
    · iunfold cliStreamErr at Hse
      icases Hse with ⟨%Hne, -, -⟩
      cases err with
      | nil => exact absurd rfl Hne.1
      | ok ei =>
        (try wp_auto)
        ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
        · iPkgInit
        wp_apply wp_Error as %f1 -
        (try wp_auto)
        wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply wp_Warn lg _ _ $$ []
        · iframe #; ipureintro; exact Hlgnn
        (try wp_auto)
        wp_for_post
        wp_for_post
        iapply HΦ; itrivial
  · ihave #Hsc2 : iprop(context.isContextDef sc scd) $$ [Hscc]
    · iexact Hscc
    unfold context.isContextDef
    iNamed Hsc2
    wp_apply +noauto time.wp_After as %tch %γt #Htch
    (try wp_auto)
    wp_apply HCtx as %cx #Hcx
    ihave #Hcx2 : iprop(context.isContextDef cx cd) $$ [Hcx]
    · iexact Hcx
    iunfold context.isContextDef at Hcx2
    icases Hcx2 with ⟨-, #HDoneX, -⟩
    wp_apply +noauto HDoneX as %ch1 %γ1 #Hdone1
    (try wp_auto)
    wp_apply +noauto HDone as %ch3 %γ3 #Hdone3
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
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
      iintro %tm -
      (try wp_auto)
      wp_for_post
      iframe
      iexists _; iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone1
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone1
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ; itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dc, γd
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdcu
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdcu
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ; itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch3, γ3
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone3
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone3
      iintro -
      (try wp_auto)
      wp_for_post
      iapply HΦ; itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
