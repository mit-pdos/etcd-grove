/- `MemoryStorage.ApplySnapshot` (`storage.go:207`), proved 2026-10-12 (Lean-first). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.ApplySnapshot.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG) := by
  intro ms γs σ sp sv eood Hidle Hbnd
  wp_start as ⟨Hms, Hsnap, #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  iunfold memSnapOwn at Hsn
  icases Hsn with ⟨%sp0, %sv0, Hsnapshot, Hsnap0, %Hsnap_id⟩
  icases ownSnapM_not_null $$ Hsnap with ⟨Hsnap, %Hspnn⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σp, Hinv⟩
  iNamedSuffix Hinv "_inv"
  icases memView_agree γs σ σp $$ Hview Hgs_inv with ⟨%Hvw, Hview, Hgs_inv⟩
  have Hσp : σp = σ := Hvw.2.2.2 Hidle
  subst Hσp
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  have Hss : σp.ss.index' = sv0.Metadata'.Index' := by rw [← Hsnap_id.1]; rfl
  wp_apply wp_EnsureSnapshot sp (some sv) $$ [Hsnap] as %r ⟨Hr, %Hrsp⟩
  · simp only [snapOpt]; iexact Hsnap
  have Hr : r = sp := Hrsp Hspnn
  subst r
  simp only [Option.getD_some]
  ihave Hsnap := ownSnapE_weaken $$ Hr
  wp_apply wp_GetMetadata.1 sp0 (DFrac.own 1) sv0 $$ [Hsnap0] as %pm0 ⟨Hm0, Hmback0⟩
  · iframe Hsnap0
  wp_apply wp_GetIndex pm0 (DFrac.own 1) sv0.Metadata' $$ [Hm0] as Hm0
  · iframe Hm0
  ihave Hsnap0 := Hmback0 $$ Hm0
  wp_apply wp_GetMetadata.1 sp (DFrac.own 1) sv $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
  · iframe Hsnap
  wp_apply wp_GetIndex pm (DFrac.own 1) sv.Metadata' $$ [Hm] as Hm
  · iframe Hm
  ihave Hsnap := Hmback $$ Hm
  rw [← Hss]
  wp_if_destruct
  rotate_left
  wp_if_destruct
  · -- `ErrSnapOutOfDate`: nothing changes
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f
      Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists σp
      iframe Hgs_inv
      isplitl
      · iexists hp, es, dummy, nfi, nli, nen, nte, nsn
        iframe # ∗
        ipureintro; exact Hdummy
      ipureintro; exact Hpb_inv
    iapply HΦ
    iframe Hsnap
    ileft
    isplitr
    · ipureintro; exact ⟨by assumption, Hif, rfl⟩
    unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists sp0, sv0
      iframe
      ipureintro; exact Hsnap_id
    ipureintro; exact Hbounded
  -- the snapshot is applied (either because the storage had none or because it is newer)
  all_goals
    have Hnot : ¬ (σp.ss.index' ≠ W64 0 ∧
        uint.Z sv.Metadata'.Index' ≤ uint.Z σp.ss.index') := by
      intro ⟨h1, h2⟩
      first
        | exact h1 ‹σp.ss.index' = W64 0›
        | exact ‹¬ uint.Z sv.Metadata'.Index' ≤ uint.Z σp.ss.index'› h2
    wp_apply wp_CloneSnapshot.1 sp (DFrac.own 1) sv $$ [Hsnap] as %p' ⟨Hsnap, Hp'⟩
    · iframe Hsnap
    wp_apply wp_GetMetadata.1 sp (DFrac.own 1) sv $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
    · iframe Hsnap
    wp_apply wp_GetTerm pm (DFrac.own 1) sv.Metadata' $$ [Hm] as Hm
    · iframe Hm
    ihave Hsnap := Hmback $$ Hm
    wp_apply wp_GetMetadata.1 sp (DFrac.own 1) sv $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
    · iframe Hsnap
    wp_apply wp_GetIndex pm (DFrac.own 1) sv.Metadata' $$ [Hm] as Hm
    · iframe Hm
    ihave Hsnap := Hmback $$ Hm
    imod cellRO_alloc $$ «$v0» with #cT
    imod cellRO_alloc $$ «$v1» with #cI
    wp_apply wp_slice_literal_ex (V := Loc)
    wp_alloc l0 as Hl0
    wp_auto
    iexists [l0]
    isplitr
    · ipureintro; rfl
    iintro %slp ⟨Hsl, Hsl_cap⟩
    have Hsz : go.arrayLiteralSize [KeyedElement none (ElementLiteralValue
        [KeyedElement (some (KeyField go!"Term")) (ElementExpression go.uint64.PointerType #«$v0_ptr»),
         KeyedElement (some (KeyField go!"Index")) (ElementExpression go.uint64.PointerType #«$v1_ptr»)])] = 1 := rfl
    simp only [Hsz]
    -- the fresh dummy entry, at the snapshot's id, frozen
    imod entOwn_of_struct l0 (raftpb.Entry.mk zeroValDef «$v0_ptr» «$v1_ptr» null slice.nil slice.nil 0) (EntryM.mk sv.Metadata'.Term' sv.Metadata'.Index'
        (zero_val raftpb.EntryType) []) ⊤ rfl $$ [Hl0] with He0
    · iframe Hl0 cT cI
      isplitl []; · iapply cellRO_null
      iapply ownSlice_nil
    imod entOwn_freeze $$ He0 with #He0
    imod ownSlice_persist $$ Hsl with #Hsl
    wp_auto
    imod memView_set γs σp σp (memStorApplied sv) Hidle rfl $$ Hview Hgs_inv
      with ⟨-, Hview, Hgs_inv⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f
      Hsl_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
    · inext
      unfold memstorageInv memstorageFields
      iexists memStorApplied sv
      iframe Hgs_inv
      isplitl
      · iexists hp, _, _, nfi, nli, nen, nte, nsn
        iframe # ∗
        isplitr
        · iunfold entsRO; iunfold entsPts
          iexists [l0]
          iframe Hsl
          iapply (BigSepL2.bigSepL2_cons).2
          iframe He0
          rw [show (memStorApplied sv).ents = [] from rfl]
          iapply entsBig_nil
        ipureintro; exact ⟨rfl, rfl⟩
      ipureintro; simp only [memStorApplied, snapId, List.length_nil]; word
    iapply HΦ
    iframe Hsnap
    iright
    isplitr
    · ipureintro; exact ⟨Hnot, rfl⟩
    unfold ownMemoryStorage memSnapOwn
    iframe # ∗
    isplitl
    · iexists p', sv
      iframe
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    ipureintro; simp only [memStorApplied, snapId, List.length_nil]; word

end proof

end EtcdGrove
end Perennial
