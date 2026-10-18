/- `MemoryStorage.ApplySnapshot` (`storage.go:207`), proved 2026-10-12 (Lean-first). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage

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
  have HN : ↑memSnapN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  intro ms γs σ σt sp sv eood Hidle Hbnd
  wp_start as ⟨Hms, Htok, Hsnap, #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  iunfold memSnapShare at Hsn
  icases Hsn with ⟨#Hsinv, Hok, Hsv⟩
  iunfold memSnapTok at Htok
  icases Htok with ⟨-, -, -, Hak, Hsvt⟩
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
  -- (D17d) the snapshot, taken out with the lock's key and the owner's
  icases memInvGhost_key $$ Hgs_inv with ⟨Hlk, Hgs_back⟩
  imod memSnap_take ms γs 1 ⊤ HN $$ Hsinv [Hlk Hok] with ⟨Hhome, Hrcpt⟩
  · iunfold memSnapKeys; ileft; iframe; ipureintro; rfl
  wp_apply wp_EnsureSnapshot sp (some sv) $$ [Hsnap] as %r ⟨Hr, %Hrsp⟩
  · simp only [snapOpt]; iexact Hsnap
  ihave Hr := ownSnapW_E $$ Hr
  have Hr : r = sp := Hrsp Hspnn
  subst r
  simp only [Option.getD_some]
  ihave Hsnap := ownSnapE_weaken $$ Hr
  iunfold memSnapHome at Hhome
  icases Hhome with ⟨%σ1, Hsn, Hsnh⟩
  icases ghostVar_agree γs.sn _ _ _ _ $$ Hsv Hsnh with %Hag
  obtain ⟨Hs1, Hs2, Hs3⟩ := snapPart_inj Hag
  ihave Hsn := memSnapOwn_congr ms σ1 σp Hs1 Hs2 Hs3 $$ Hsn
  iunfold memSnapOwn at Hsn
  icases Hsn with ⟨%sp0, %sv0, Hsnapshot, Hsnap0, %Hsnap_id⟩
  have Hss : σp.ss.index' = sv0.Metadata'.Index' := by rw [← Hsnap_id.1]; rfl
  (try wp_auto)
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
    imod memSnap_put ms γs 1 σp ⊤ HN $$ Hsinv Hrcpt [Hsnapshot Hsnap0] [Hsnh] with Hk
    · iunfold memSnapOwn
      iexists sp0, sv0
      iframe
      ipureintro; exact Hsnap_id
    · rw [Hag]; iexact Hsnh
    iunfold memSnapKeys at Hk
    icases Hk with (⟨-, Hlk, Hok⟩ | ⟨%Hk, -⟩ | ⟨%Hk, -⟩)
    rotate_left
    · exact absurd Hk (by decide)
    · exact absurd Hk (by decide)
    ihave Hgs_inv := Hgs_back $$ Hlk
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
    unfold ownMemoryStorage memSnapShare memSnapTok
    simp only [named]
    iframe # ∗
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
    -- (D17d) the new snapshot's ghost value, and the snapshot back
    imod memSnap_update γs _ _ _ (memStorApplied sv) $$ Hsv Hsvt Hsnh with ⟨Hsv, Hsvt, Hsnh⟩
    imod memSnap_put ms γs 1 (memStorApplied sv) ⊤ HN $$ Hsinv Hrcpt [Hsnapshot Hp'] Hsnh with Hk
    · iunfold memSnapOwn
      iexists p', sv
      iframe
      ipureintro; exact ⟨rfl, rfl, rfl⟩
    iunfold memSnapKeys at Hk
    icases Hk with (⟨-, Hlk, Hok⟩ | ⟨%Hk, -⟩ | ⟨%Hk, -⟩)
    rotate_left
    · exact absurd Hk (by decide)
    · exact absurd Hk (by decide)
    ihave Hgs_inv := Hgs_back $$ Hlk
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
    unfold ownMemoryStorage memSnapShare memSnapTok
    simp only [named]
    iframe # ∗
    ipureintro; simp only [memStorApplied, snapId, List.length_nil]; word

end proof

end EtcdGrove
end Perennial
