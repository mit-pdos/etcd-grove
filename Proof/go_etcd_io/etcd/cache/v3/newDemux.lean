/-
Proof of `Spec/newDemux.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newDemux
public import Spec.go_etcd_io.etcd.cache.v3.newRingBuffer
public import Spec.go_etcd_io.etcd.cache.v3.newNotifier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newDemux.wp_proof
    (wp_newRingBuffer : newRingBuffer.spec (GF := GF) (hG := hG))
    (wp_newNotifier : newNotifier.spec (GF := GF) (hG := hG)) :
    newDemux.spec (GF := GF) (hG := hG) := by
  intro C h ri
  wp_start as %Hh
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := w64) (go.GoType.PointerType watcher.ty) go.int64)
    as %a Ha
  wp_apply (wp_map_make1 (K := Loc) (V := w64) (go.GoType.PointerType watcher.ty) go.int64)
    as %l Hl
  wp_apply wp_newRingBuffer (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty)) h _
    (batchAt (hG := hG)) batchRev $$ [] as %r Hr
  · isplitr
    · ipureintro; exact Hh
    unfold revisionOfSpec
    iintro %p %b
    imodintro
    iintro %Φ' #Hp HΦ'
    unfold batchAt eventsAt
    icases Hp with ⟨⟨%ls, #Hsl, %Hlen, #Hev⟩, %Hb⟩
    obtain ⟨e0, es, rfl⟩ : ∃ e0 es, b = e0 :: es := by
      cases b with
      | nil => exact absurd rfl Hb.1
      | cons e0 es => exact ⟨e0, es, rfl⟩
    obtain ⟨ev0, ls', rfl⟩ : ∃ ev0 ls', ls = ev0 :: ls' := by
      cases ls with
      | nil => simp at Hlen
      | cons ev0 ls' => exact ⟨ev0, ls', rfl⟩
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    wp_auto
    have H0 : (0 : Int) ≤ sint.Z (W64 0) := by word
    have H1 : sint.Z (W64 0) < sint.Z p.len := by
      have := Hsll.1; simp at this; word
    simp only [H0, H1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index p (sint.Z (W64 0)) (ev0 :: ls') DFrac.discard ev0 H0 $$ [] as -
    · iframe Hsl; ipureintro; rfl
    ihave He0 := Hev $$ %0 %ev0 %e0 %rfl %rfl
    iunfold eventAt at He0
    icases He0 with ⟨%keySl, #Htyp, #Hkv, #Hkey, #Hks, #Hmod⟩
    wp_auto
    rw [show e0.rev = batchRev (e0 :: es) from rfl]
    iapply HΦ'
    itrivial
  iNamed Hr
  wp_auto
  wp_apply wp_newNotifier as %n %γn ⟨#Hlb0, Hnh⟩
  wp_alloc d as Hd
  iStructNamed Hd
  ipersist resyncInterval
  ipersist resynced
  have Hok' : RingOk rb (sint.nat h) ([] : List Batch).length := Hok
  ihave Hhist := ownRingBuffer_intro (demuxHistAddr d) (sint.nat h) (batchAt (hG := hG)) batchRev
    [] rb ents Hok' Hrev Hsorted $$ history Hbuf Hitems HrevOf
  iclear Hr
  imod ghostVar_alloc (GF := GF) DemuxCore.init with ⟨%γc, Hc⟩
  icases ghostVar_split γc DemuxCore.init (1 : Qp).half (1 : Qp).half $$ [Hc] with ⟨Hc1, Hc2⟩
  · rw [Qp.half_add_half]; iexact Hc
  imod ghostVar_alloc (GF := GF) () with ⟨%γw, Hwt⟩
  imod ghost_map_alloc (GF := GF) (K := Loc) (V := RegInfo) ∅ with ⟨%γr, Hra, -⟩
  icases ((ghostMapAuth_fractional (GF := GF) γr (∅ : GMap Loc RegInfo)).fractional
    (1 : Qp).half (1 : Qp).half).1 $$ [Hra] with ⟨Hra1, Hra2⟩
  · rw [Qp.half_add_half]; iexact Hra
  imod ghost_map_alloc (GF := GF) (K := Loc) (V := View) ∅ with ⟨%γv, Hva, -⟩
  imod inv_alloc demuxN ⊤ (demuxSlots (hG := hG) C ⟨γc, γw, γr, γv⟩) $$ [Hra2] with #Hslots
  · inext
    unfold demuxSlots
    iright
    iexists ∅
    iframe Hra2
    iapply BigSepM.bigSepM_empty.2; iempintro
  have Hinv0 : DemuxInv (sint.nat h) DemuxCore.init := by
    constructor <;> (try simp [DemuxCore.init]) <;>
      first | word | exact ⟨by simp, by simp [RevSorted], by simp⟩
  have Hun := actOf_lagOf_unmapped (∅ : GMap Loc View) (fun w v hv => by simp at hv)
  imod sync.init_RWMutex (demuxLockInv (hG := hG) d ⟨γc, γw, γr, γv⟩ (sint.nat h) C) (demuxMuAddr d)
    $$ [Hwt Hc1 Hra1 Hva minRev maxRev activeWatchers laggingWatchers Ha Hl Hhist] mu with Htoks
  · inext
    unfold demuxLockInv demuxLockRest
    iframe Hwt
    iexists DemuxCore.init, ∅, ∅, a, l
    simp only [named]
    rw [Hun.1, Hun.2]
    iframe
    isplitr
    · simp only [DemuxCore.init]; iapply certChain_nil
    isplitr
    · iapply (prog_init (GF := GF) (C := C))
    ipureintro
    refine ⟨Hinv0, ⟨fun w => by simp, fun w v hv => by simp at hv, fun w v hv => by simp at hv⟩,
      RegsStart.unmapped (fun w ri hr => by simp at hr) (fun w v hv => by simp at hv)⟩
  wp_auto
  obtain ⟨m, hm⟩ : ∃ m, Int.toNat sync.rwmutex.actualMaxReaders = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by have := sync.actualMaxReaders_pos; omega)).symm⟩
  rw [hm, List.replicate_succ, Nat.add_sub_cancel]
  icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Hw, Hrd⟩
  iapply HΦ $$ %d %(DemuxNames.mk γc γw γr γv) %γn
  isplitr
  · unfold isDemux
    iexists ri, n
    simp only [named]
    iframe #
    ipureintro
    constructor <;> word
  isplitl [Hc2 Hw]
  · unfold demuxWriter demuxHandle
    iframe
    ipureintro; exact Hinv0
  isplitl [Hrd]
  · unfold demuxHandle
    iexact Hrd
  iframe Hlb0
  iapply BigSepL.bigSepL_impl $$ Hnh
  imodintro
  iintro %k %x %_ H
  unfold demuxResyncHandle
  iexists n
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
