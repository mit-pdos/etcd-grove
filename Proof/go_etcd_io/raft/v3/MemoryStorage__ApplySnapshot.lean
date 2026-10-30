/- `MemoryStorage.ApplySnapshot` (`storage.go:218`; U8 v2 step 3). The stored snapshot's index is
`0` or frozen in the map, so below the caller's owned range from `j ≤ s` (`s` the argument's index):
the out-of-date test fails. The caller's range is deleted from the map, the dummy at `s` inserted
frozen, the end moved to `s + 1`, the compaction point to `s` (registered with `J.B s`), and the
snapshot replaced by the clone (taken out of its home with the lock's key). -/
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (D22 S-d4, 2026-10-21) `EnsureSnapshot` of `ApplySnapshot`'s argument (`snapArg`): owned, it may
write its `nil` fields; at a fraction, with every pointer field set, it writes nothing. Either way
the same pointer, holding the same snapshot at the same fraction. -/
private theorem wp_EnsureSnapshot_arg
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (sp : Loc) (dq : DFrac) (sv : SnapshotM) (Hnn : sp ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ snapArg sp dq sv }}
      (App (Val #(functions raftpb.EnsureSnapshot [])) (Val #sp))
    {{ RET #sp; ownSnapM sp dq sv }} := by
  iintro %Φ ⟨#Hinit, Hs⟩ HΦ
  iunfold snapArg at Hs
  icases Hs with (⟨%Hdq, Hs⟩ | Hs)
  · subst Hdq
    wp_apply wp_EnsureSnapshot.1 sp (some sv) $$ [Hs] as %r ⟨Hr, %Hrsp⟩
    · simp only [snapOpt]; iexact Hs
    ihave Hr := ownSnapS_W _ _ _ $$ Hr
    ihave Hr := ownSnapW_E $$ Hr
    have Hr' : r = sp := Hrsp Hnn
    subst Hr'
    simp only [Option.getD_some]
    iapply HΦ
    iapply ownSnapE_weaken $$ Hr
  · wp_apply wp_EnsureSnapshot.2 sp dq sv $$ [$Hs] as Hs
    iapply HΦ
    iapply ownSnapS_M $$ Hs

theorem MemoryStorage.ApplySnapshot.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG) := by
  have HN : ↑memStorN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  intro ms γs J j old sp dq sv sv0 eood Hjs Hs61
  wp_start as ⟨#Hsi, Hold, Hend, #HB, #HSV, #HDL, Hsnap, Hsx, #Herr⟩
  iunfold memStorInvP at Hsi
  icases Hsi with ⟨#Hlock, #HB0, #Hjinv⟩
  ihave #Hsi : memStorInvP ms γs J $$ []
  · iunfold memStorInvP; iframe Hlock HB0 Hjinv
  iunfold memStorLock at Hlock
  icases Hlock with ⟨#Hinit, #Hmu⟩
  icases snapArg_not_null $$ Hsnap with ⟨Hsnap, %Hspnn⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%p, %ents, %M, %sv1, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- the ghost facts: the end, the snapshot's half, the dummy and the stored snapshot below `j`
  iunfold memEnd at Hend
  icases Hend with ⟨Hen, Hek⟩
  icases ghostVar_agree γs.en _ _ _ _ $$ Hen Hen_inv with %He
  icases memSnapExact_agree γs sv0 sv1 $$ Hsx Hsx_inv with %Hsv0
  subst Hsv0
  iunfold memLog at Hold
  icases Hold with ⟨Hold, %Holdb⟩
  icases Hd0_inv with ⟨%e0, #He0, %He0t⟩
  icases memLogL_frozen_ne γs.log j old _ e0 $$ Hold He0 with %Hcj
  ihave %Hsij : ⌜uint.nat sv0.Metadata'.Index' = 0 ∨ uint.nat sv0.Metadata'.Index' < j⌝ $$ [Hold]
  · icases Hsf_inv with (%H | ⟨%e1, #He1, -⟩)
    · ipureintro; exact Or.inl H
    icases memLogL_frozen_ne γs.log j old _ e1 $$ Hold He1 with %H
    ipureintro
    have := Hok_inv.2.2.2.2.1
    omega
  have Hcj' : uint.nat p.index' < j := by have := Hok_inv.1; omega
  -- the snapshot, taken out with the lock's key
  imod memSnap_take ms γs J ⊤ HN $$ Hsi Hlk_inv with Hhome
  wp_apply wp_EnsureSnapshot_arg wp_EnsureSnapshot sp dq sv Hspnn $$ [$Hsnap] as Hsnap
  iunfold memSnapHome at Hhome
  icases Hhome with ⟨Hhk, %sp0, %sv1, Hsnapshot, Hsnap0, Hsxh, -⟩
  icases ghostVar_agree γs.sx _ _ _ _ $$ Hsx_inv Hsxh with %Hag
  subst Hag
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hp, %es, %dummy, %nfi, %nli, %nen, %nte, %nsn, Hfields_inv⟩
  iNamed Hfields_inv
  wp_auto
  wp_apply wp_GetMetadata.1 sp0 (DFrac.own 1) sv0 $$ [Hsnap0] as %pm0 ⟨Hm0, Hmback0⟩
  · iframe Hsnap0
  wp_apply wp_GetIndex pm0 (DFrac.own 1) sv0.Metadata' $$ [Hm0] as Hm0
  · iframe Hm0
  ihave Hsnap0 := Hmback0 $$ Hm0
  wp_apply wp_GetMetadata.1 sp dq sv $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
  · iframe Hsnap
  wp_apply wp_GetIndex pm dq sv.Metadata' $$ [Hm] as Hm
  · iframe Hm
  ihave Hsnap := Hmback $$ Hm
  wp_if_destruct
  rotate_left
  wp_if_destruct
  · exfalso
    rcases Hsij with H | H
    · apply ‹¬ sv0.Metadata'.Index' = W64 0›; word
    · word
  all_goals
    wp_apply wp_CloneSnapshot.1 sp dq sv $$ [Hsnap] as %p' ⟨Hsnap, Hp'⟩
    · iframe Hsnap
    wp_apply wp_GetMetadata.1 sp dq sv $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
    · iframe Hsnap
    wp_apply wp_GetTerm pm dq sv.Metadata' $$ [Hm] as Hm
    · iframe Hm
    ihave Hsnap := Hmback $$ Hm
    wp_apply wp_GetMetadata.1 sp dq sv $$ [Hsnap] as %pm ⟨Hm, Hmback⟩
    · iframe Hsnap
    wp_apply wp_GetIndex pm dq sv.Metadata' $$ [Hm] as Hm
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
    imod entOwn_of_struct l0 (raftpb.Entry.mk zeroValDef «$v0_ptr» «$v1_ptr» null slice.nil slice.nil 0)
        (memDummy sv) ⊤ rfl $$ [Hl0] with He0'
    · simp only [memDummy]
      iframe Hl0 cT cI
      isplitl []; · iapply cellRO_null
      iapply ownSlice_nil
    imod entOwn_freeze $$ He0' with #He0'
    imod ownSlice_persist $$ Hsl with #Hsl
    wp_auto
    -- the ghost state: the caller's range deleted, the dummy at `s` frozen, the end at `s + 1`,
    -- the compaction point at `s` (registered), the snapshot replaced
    imod memLogL_delete γs.log M j old $$ Hlog_inv Hold with ⟨%M1, Hlog, %HM1⟩
    have Hs_abs : M1.lookup (uint.nat sv.Metadata'.Index') = none := by
      rw [HM1]
      by_cases h : j ≤ uint.nat sv.Metadata'.Index' ∧ uint.nat sv.Metadata'.Index' < j + old.length
      · rw [if_pos h]
      · rw [if_neg h]; exact Hok_inv.2.1 _ (by omega)
    imod ghost_map_insert_persist (uint.nat sv.Metadata'.Index') (memDummy sv) Hs_abs $$ Hlog
      with ⟨Hlog, #Hd⟩
    imod ghostVar_update_halves (uint.nat sv.Metadata'.Index' + 1) γs.en _ _ $$ Hen Hen_inv
      with ⟨Hen, Hen_inv⟩
    imod mono_nat_own_update (uint.nat sv.Metadata'.Index') (by omega) $$ Hcp_inv with ⟨Hcp, #Hcplb⟩
    imod memCompJust_register ms γs J (uint.nat sv.Metadata'.Index') ⊤ HN $$ Hsi HB with #Hcjn
    iunfold memSnapExact at Hsx
    imod memSnap_update γs sv0 sv0 sv0 sv $$ Hsx Hsx_inv Hsxh with ⟨Hsx, Hsx_inv, Hsxh⟩
    imod memSnap_put ms γs J ⊤ HN $$ Hsi [Hhk Hsnapshot Hp' Hsxh] with Hlk
    · iunfold memSnapHome
      iframe Hhk
      iexists p', sv
      iframe Hsnapshot Hp' Hsxh
      iright; iframe HSV HDL
    have Hok' : MemOk (entryID.mk sv.Metadata'.Term' sv.Metadata'.Index') []
        ((M1.insert (uint.nat sv.Metadata'.Index') (memDummy sv))) sv := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_nil]; omega
      · intro i hi
        simp only [List.length_nil] at hi
        rw [GMap.lookup_insert_ne _ _ (by omega), HM1]
        by_cases h : j ≤ i ∧ i < j + old.length
        · rw [if_pos h]
        · rw [if_neg h]; exact Hok_inv.2.1 _ (by omega)
      · intro i h1 h2; simp only [List.length_nil] at h1 h2; omega
      · exact Nat.le_refl _
      · simp only [List.length_nil]; omega
      · intro j e h; simp at h
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HhardState Hents_f Hsl_cap Hcs_firstIndex
      Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog Hen_inv Hcp Hsx_inv Hlk]
    · unfold memstorageInv
      iexists entryID.mk sv.Metadata'.Term' sv.Metadata'.Index', [], _, sv
      simp only [named, List.length_nil, Nat.add_zero]
      isplitl [HhardState Hents_f Hsl_cap Hcs_firstIndex Hcs_lastIndex Hcs_entries Hcs_term
        Hcs_snapshot]
      · unfold memstorageFields
        iexists hp, _, memDummy sv, nfi, nli, nen, nte, nsn
        simp only [named]
        iframe
        isplitr
        · iunfold entsRO; iunfold entsPts
          iexists [l0]
          iframe Hsl
          iapply (BigSepL2.bigSepL2_cons).2
          iframe He0'
          simp only [memPhys]
          inext
          iapply entsBig_nil
        ipureintro; exact ⟨rfl, rfl⟩
      iframe Hlog Hen_inv Hcp Hsx_inv Hlk Hcjn
      isplitr
      · iexists memDummy sv
        iframe Hd
        ipureintro; rfl
      isplitr
      · iright
        iexists memDummy sv
        iframe Hd
        ipureintro; rfl
      ipureintro; exact Hok'
    iapply HΦ
    iframe Hsnap
    isplitr
    · iunfold memCompacted
      iright
      iframe Hcplb
      iunfold memCompJust at Hcjn
      icases Hcjn with ⟨%L, #HL, %HLm⟩
      iexists L
      iframe HL
      ipureintro; exact ⟨_, HLm, Nat.le_refl _⟩
    isplitr
    · iunfold memLog
      simp only [memLogL]
      isplitl []
      · iframe Hd
      ipureintro; right; simp only [List.length_singleton]; omega
    isplitl [Hen Hek]
    · iunfold memEnd; iframe Hen Hek
    iunfold memSnapExact
    iexact Hsx

end proof

end EtcdGrove
end Perennial
