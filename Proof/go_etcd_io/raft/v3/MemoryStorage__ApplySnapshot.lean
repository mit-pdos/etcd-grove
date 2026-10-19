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
  intro ms γs σ σt sp sv eood Hidle Hbnd Hfl Hcap
  wp_start as ⟨Hms, Htok, Hsnap, #Herr⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨#Hinit, #Hmu, Hview, Hsn, %Hbounded⟩
  iunfold memSnapShare at Hsn
  icases Hsn with ⟨#Hsinv, Hok⟩
  iunfold memSnapTok at Htok
  icases Htok with ⟨-, -, -, Hak, Hsvt, Hcbt⟩
  icases ownSnapM_not_null $$ Hsnap with ⟨Hsnap, %Hspnn⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%σp, %c, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memCutInv at Hcut_inv
  iNamed Hcut_inv
  icases ghostVar_agree γs.cb _ _ _ _ $$ Hcb Hcbt with %Hcbe
  subst Hcbe
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
  icases ghostVar_agree γs.sn _ _ _ _ $$ Hsvt Hsnh with %Hag
  obtain ⟨Hs1, Hs2, Hs3⟩ := snapPart_inj Hag
  icases ghostVar_agree γs.sn _ _ _ _ $$ Hsq Hsnh with %HagS
  obtain ⟨HS1, -, -⟩ := snapPart_inj HagS
  ihave Hsn := memSnapOwn_congr ms σ1 σt Hs1 Hs2 Hs3 $$ Hsn
  iunfold memSnapOwn at Hsn
  icases Hsn with ⟨%sp0, %sv0, Hsnapshot, Hsnap0, %Hsnap_id⟩
  have Hss : σt.ss.index' = sv0.Metadata'.Index' := by rw [← Hsnap_id.1]; rfl
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
    imod memSnap_put ms γs 1 σt ⊤ HN $$ Hsinv Hrcpt [Hsnapshot Hsnap0] [Hsnh] with Hk
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
      Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcb Hbd Hsq]
    · inext
      unfold memstorageInv memstorageFields
      iexists σp, σt.prev
      iframe Hgs_inv
      isplitl [HhardState Hents_f Hents Hents_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
      · iexists hp, es, dummy, nfi, nli, nen, nte, nsn
        iframe # ∗
        ipureintro; exact Hdummy
      isplitr
      · ipureintro; exact Hpb_inv
      iunfold memCutInv
      iexists S
      iframe Hcb Hbd Hcfl Hsq Hsrel
      ipureintro; exact ⟨Hcok, Hccap⟩
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
    have Hnot : ¬ (σt.ss.index' ≠ W64 0 ∧
        uint.Z sv.Metadata'.Index' ≤ uint.Z σt.ss.index') := by
      intro ⟨h1, h2⟩
      first
        | exact h1 ‹σt.ss.index' = W64 0›
        | exact ‹¬ uint.Z sv.Metadata'.Index' ≤ uint.Z σt.ss.index'› h2
    -- (D19i part 1) the new boundary is past the cut: the cut is at most the storage's snapshot,
    -- which the new one is past (or is the empty one, and so the cut `0`)
    have HcS : uint.Z σt.prev.index' ≤ uint.Z sv.Metadata'.Index' := by
      have h2 := Hcok.2
      rw [HS1, ← Hs1] at h2
      by_cases h0 : σt.ss.index' = W64 0
      · rw [h0] at h2
        have : uint.Z (W64 0) = 0 := rfl
        have := (word.unsigned_range sv.Metadata'.Index').1
        omega
      · have := not_and.1 Hnot h0
        omega
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
    imod entOwn_of_struct l0 (raftpb.Entry.mk zeroValDef «$v0_ptr» «$v1_ptr» null slice.nil null slice.nil 0) (EntryM.mk sv.Metadata'.Term' sv.Metadata'.Index'
        (zero_val raftpb.EntryType) [] (zero_val w64)) ⊤ rfl $$ [Hl0] with He0
    · iframe Hl0 cT cI
      isplitl []; · iapply cellRO_null
      isplitl []; · iapply ownSlice_nil
      iapply cellRO_null
    imod entOwn_freeze $$ He0 with #He0
    imod ownSlice_persist $$ Hsl with #Hsl
    wp_auto
    -- (D17d) the new snapshot's ghost value, and the snapshot back
    imod memSnap_update γs _ _ _ (memStorApplied sv) $$ Hsq Hsvt Hsnh with ⟨Hsq, Hsvt, Hsnh⟩
    imod ghostVar_update_halves (memStorApplied sv).prev γs.cb _ _ $$ Hcb Hcbt with ⟨Hcb, Hcbt⟩
    imod mono_nat_own_update (uint.Z (memStorApplied sv).prev.index').toNat
      (by simp only [memStorApplied, snapId]; omega) $$ Hbd with ⟨Hbd, -⟩
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
    imod memView_set γs σ σp { memStorApplied sv with fl := σ.fl } Hidle rfl (Int.le_refl _)
      (by simp only [EtcdGrove.stLast, memStorApplied, snapId, List.length_nil]; omega)
      (fun k e h => by simp [memStorApplied] at h)
      $$ Hview Hgs_inv with ⟨-, Hview, Hgs_inv⟩
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hents_f
      Hsl_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hcb Hbd Hsq]
    · inext
      unfold memstorageInv memstorageFields
      iexists { memStorApplied sv with fl := σ.fl }, (memStorApplied sv).prev
      iframe Hgs_inv
      isplitl [HhardState Hents_f Hsl_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot]
      · iexists hp, _, _, nfi, nli, nen, nte, nsn
        iframe # ∗
        isplitr
        · iunfold entsRO; iunfold entsPts
          iexists [l0]
          iframe Hsl
          iapply (BigSepL2.bigSepL2_cons).2
          iframe He0
          rw [show (memCut { memStorApplied sv with fl := σ.fl } (memStorApplied sv).prev).ents = []
            by simp [memCut, memStorApplied]]
          iapply entsBig_nil
        ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · ipureintro; simp only [memStorApplied, snapId, List.length_nil]; word
      iunfold memCutInv
      iexists memStorApplied sv
      iframe Hcb Hbd Hsq
      isplitr
      · ileft; ipureintro; rfl
      isplitr
      · ipureintro
        refine ⟨CutOk.self _, ?_⟩
        simp only [memStorApplied, snapId]; exact Int.le_refl _
      isplitr
      · ipureintro; simp only [memStorApplied, snapId]; exact Hcap
      ileft; ipureintro; exact ⟨rfl, rfl, rfl⟩
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
