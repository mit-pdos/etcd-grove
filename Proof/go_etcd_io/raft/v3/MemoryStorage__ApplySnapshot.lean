/- `MemoryStorage.ApplySnapshot` (`storage.go:218`; U8 v2 step 3). The stored snapshot's index is
`0` or frozen in the map, so below the caller's owned range from `j ≤ s` (`s` the argument's index):
the out-of-date test fails. The caller's range is deleted from the map, the dummy at `s` inserted
frozen, the end moved to `s + 1`, the compaction point to `s` (registered with `J.B s`), and the
snapshot replaced by the clone (taken out of its home with the lock's key), its index's authority
raised to `s` (kvreconf-snapshot-thread, 2026-10-30: `memSnapLb γs s`, no client snapshot half). -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Proof.go_etcd_io.raft.v3.LemmasMemstorage
public import Proof.go_etcd_io.raft.v3.InvMemstorageAt

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

/-- Both triples at once (restart S3, 2026-11-11): the owned range from `j ≤ s`, or (`s = 0`) from
`j = 1` with the dummy at `0` already the snapshot's (`HZ`), which takes the place of inserting it. -/
private theorem wp_ApplySnapshot_gen
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM)) (j : Nat)
    (old : List EntryM) (sp : Loc) (dq : DFrac) (sv : SnapshotM) (eood : GoInterface)
    (w : Option SnapshotM)
    (Hjs : j ≤ uint.nat sv.Metadata'.Index' ∨ (uint.nat sv.Metadata'.Index' = 0 ∧ j = 1))
    (Hs61 : uint.nat sv.Metadata'.Index' < 2^61) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorAt ms γs J o
        iprop(J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index')) ∗
      memLog γs j (DFrac.own 1) old ∗ memEnd γs (j + old.length) ∗
      snapArg sp dq sv ∗ (match w with | none => memSnapLb γs 0 | some s0 => memSnapNone γs s0) ∗
      globalAddr ErrSnapOutOfDate ↦□ eood ∗
      (⌜j ≤ uint.nat sv.Metadata'.Index'⌝ ∨ memLog γs 0 DFrac.discard [memDummy sv]) }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ∗
      memEnd γs (uint.nat sv.Metadata'.Index' + 1) ∗
      (match w with
       | none => memSnapLb γs (uint.nat sv.Metadata'.Index')
       | some _ => memSnapNone γs sv) ∗
      (match o with
       | some (c, _) => memStorFresh ms γs (max c (uint.nat sv.Metadata'.Index')) sv
       | none => emp) }} := by
  have HN : ↑memStorN ⊆ (⊤ : CoPset) := CoPset.subseteq_top
  wp_start as ⟨Hat, Hold, Hend, Hsnap, Htok, #Herr, HZ⟩
  icases memStorAt_split ms γs J o _ $$ Hat with ⟨#Hlock, Hjc, Hho⟩
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
  icases Hinv with ⟨%p, %ents, %M, %sv0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  -- the ghost facts: the end, the snapshot's half, the dummy and the stored snapshot below `j`
  iunfold memEnd at Hend
  icases Hend with ⟨Hen, Hek⟩
  icases ghostVar_agree γs.en _ _ _ _ $$ Hen Hen_inv with %He
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
  imod memSnap_take_at ms γs J o _ ⊤ HN $$ Hjc Hho Hlk_inv with ⟨Hjc, Hlko, Hhome⟩
  wp_apply wp_EnsureSnapshot_arg wp_EnsureSnapshot sp dq sv Hspnn $$ [$Hsnap] as Hsnap
  iunfold memSnapHomeAt at Hhome
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
    · rcases Hjs with h | ⟨h1, h2⟩ <;> word
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
    imod entRZ_of_struct γs.sz l0
        (raftpb.Entry.mk zeroValDef «$v0_ptr» «$v1_ptr» null slice.nil slice.nil 0)
        (memDummy sv) ⊤ rfl (fun _ => by simp [memDummy, entBytesMax]) $$ [Hl0] with #He0'
    · simp only [memDummy]
      iframe Hl0 cT cI
      isplitl []; · iapply cellRO_null
      iapply ownSlice_nil
    imod ownSlice_persist $$ Hsl with #Hsl
    wp_auto
    -- the ghost state: the caller's range deleted, the dummy at `s` frozen, the end at `s + 1`,
    -- the compaction point at `s` (registered), the snapshot replaced
    imod memLogL_delete γs.log M j old $$ Hlog_inv Hold with ⟨%M1, Hlog, %HM1⟩
    -- the dummy at `s` frozen: inserted (`j ≤ s`), or already there (`s = 0`, `HZ`)
    ihave Hins : iprop(|==> ∃ M2 : GMap Nat EntryM, ghostMapAuth γs.log 1 M2 ∗
        (uint.nat sv.Metadata'.Index') ↪[γs.log]□ memDummy sv ∗
        ⌜∀ i, i ≠ uint.nat sv.Metadata'.Index' → M2.lookup i = M1.lookup i⌝) $$ [Hlog HZ]
    · by_cases Hle : j ≤ uint.nat sv.Metadata'.Index'
      · have Hs_abs : M1.lookup (uint.nat sv.Metadata'.Index') = none := by
          rw [HM1]
          by_cases h : j ≤ uint.nat sv.Metadata'.Index' ∧ uint.nat sv.Metadata'.Index' < j + old.length
          · rw [if_pos h]
          · rw [if_neg h]; exact Hok_inv.2.1 _ (by omega)
        imod ghost_map_insert_persist (uint.nat sv.Metadata'.Index') (memDummy sv) Hs_abs $$ Hlog
          with ⟨Hlog, #Hd⟩
        imodintro
        iexists _
        iframe Hlog Hd
        ipureintro
        intro i hi
        exact GMap.lookup_insert_ne _ _ (Ne.symm hi)
      · obtain ⟨H0, -⟩ : uint.nat sv.Metadata'.Index' = 0 ∧ j = 1 := Hjs.resolve_left Hle
        icases HZ with (%Hle' | #HZ)
        · exact absurd Hle' Hle
        iunfold memLog at HZ
        icases HZ with ⟨HZ, -⟩
        iunfold memLogL at HZ
        icases HZ with ⟨#Hd, -⟩
        imodintro
        iexists M1
        rw [H0]
        iframe Hlog Hd
        ipureintro
        intro i _
        rfl
    imod Hins with ⟨%M2, Hlog, #Hd, %HM2⟩
    imod ghostVar_update_halves (uint.nat sv.Metadata'.Index' + 1) γs.en _ _ $$ Hen Hen_inv
      with ⟨Hen, Hen_inv⟩
    imod mono_nat_own_update (uint.nat sv.Metadata'.Index') (by omega) $$ Hcp_inv with ⟨Hcp, #Hcplb⟩
    imod memCompJust_register_at ms γs J o _ (uint.nat sv.Metadata'.Index') ⊤ HN
      (by iintro ⟨#HB, -⟩; iexact HB) $$ Hjc with ⟨#Hcjn, Hjc⟩
    imod memSnap_update γs sv0 sv0 sv $$ Hsx_inv Hsxh with ⟨Hsx_inv, Hsxh⟩
    imod mono_nat_own_update (uint.nat sv.Metadata'.Index') (by omega) $$ Hsl_inv with ⟨Hsl_inv, #Hslb⟩
    -- the unopened snapshot: kept open (`memSnapLb`), or moved to `sv` with the token
    icases Hsn_inv with ⟨%s1, Hs1, -⟩
    ihave Hsn' : iprop(|==> ((∃ s0', ghostVar γs.s0 (1 : Qp).half s0' ∗
        (⌜sv = s0'⌝ ∨ monoNatLbOwn γs.pr 1)) ∗
        (match w with
         | none => memSnapLb γs (uint.nat sv.Metadata'.Index')
         | some _ => memSnapNone γs sv))) $$ [Htok Hs1]
    · cases w with
      | none =>
        simp only
        iunfold memSnapLb at Htok
        icases Htok with ⟨-, #Hpr⟩
        imodintro
        isplitl [Hs1]
        · iexists s1; iframe Hs1; iright; iexact Hpr
        iunfold memSnapLb; iframe Hslb Hpr
      | some s0 =>
        simp only
        iunfold memSnapNone at Htok
        icases Htok with ⟨Hpr0, Hh, -⟩
        imod ghostVar_update_halves sv γs.s0 _ _ $$ Hh Hs1 with ⟨Hh, Hs1⟩
        imodintro
        isplitl [Hs1]
        · iexists sv; iframe Hs1; ileft; ipureintro; rfl
        iunfold memSnapNone; iframe Hpr0 Hh Hslb
    imod Hsn' with ⟨Hsn', Hpost⟩
    rw [← memLkAt_bump γs o (uint.nat sv.Metadata'.Index')]
    icases memValNew_of_bound ms γs J (memBumpAt o (uint.nat sv.Metadata'.Index')) _ sv
      (by iintro ⟨-, #HSV, #HDL⟩; iright; iframe HSV HDL) $$ Hjc with ⟨Hjc, Hvn⟩
    imod memSnap_put_at ms γs J (memBumpAt o (uint.nat sv.Metadata'.Index')) _ ⊤ HN sv p'
      $$ Hjc Hlko Hhk Hsnapshot Hp' Hsxh Hvn with ⟨Hjc, Hlk, Hho⟩
    have Hok' : MemOk (entryID.mk sv.Metadata'.Term' sv.Metadata'.Index') [] M2 sv := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_nil]; omega
      · intro i hi
        simp only [List.length_nil] at hi
        rw [HM2 i (by omega), HM1]
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
      Hcs_lastIndex Hcs_entries Hcs_term Hcs_snapshot Hlog Hen_inv Hcp Hsx_inv Hsl_inv Hsn' Hlk]
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
        · iunfold entsROz; iunfold entsPtsZ
          iexists [l0]
          iframe Hsl
          iapply (BigSepL2.bigSepL2_cons).2
          iframe He0'
          simp only [memPhys]
          inext
          iapply entsBigZ_nil
        ipureintro; exact ⟨rfl, rfl⟩
      iframe Hlog Hen_inv Hcp Hsx_inv Hsl_inv Hlk Hcjn
      isplitl [Hsn']
      · iexact Hsn'
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
    isplitl [Hpost]
    · iexact Hpost
    cases o with
    | none => iempintro
    | some p0 =>
      obtain ⟨c0, sv0'⟩ := p0
      simp only [memBumpAt, memSetAt, Option.map_some]
      iapply memStorFresh_of_at
      iframe Hjc Hho

theorem MemoryStorage.ApplySnapshot.wp_proof
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ms γs J o j old sp dq sv eood Hjs Hs61
    iintro %Φ ⟨#Hinit, Hat, Hold, Hend, Hsnap, #Hlb0, #Herr⟩ HΦ
    wp_apply wp_ApplySnapshot_gen wp_EnsureSnapshot wp_GetMetadata wp_GetIndex wp_GetTerm
      wp_CloneSnapshot ms γs J o j old sp dq sv eood none (Or.inl Hjs) Hs61
      $$ [Hat Hold Hend Hsnap] as ⟨Hs, #Hc, #Hd, He, #Hl, Hf⟩
    · iframe Hat Hold Hend Hsnap Hlb0 Herr
      ileft; ipureintro; exact Hjs
    iapply HΦ
    iframe Hs Hc Hd He Hl
    cases o with
    | none => iexact Hf
    | some p0 => obtain ⟨c0, _⟩ := p0; iexact Hf
  · intro ms γs J o old sp dq sv eood H0
    iintro %Φ ⟨#Hinit, Hat, Hold, Hend, #Hd0, Hsnap, #Hlb0, #Herr⟩ HΦ
    ihave Hat : memStorAt ms γs J o iprop(J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗
        J.DL (uint.nat sv.Metadata'.Index')) $$ [Hat]
    · rw [H0]; iexact Hat
    wp_apply wp_ApplySnapshot_gen wp_EnsureSnapshot wp_GetMetadata wp_GetIndex wp_GetTerm
      wp_CloneSnapshot ms γs J o 1 old sp dq sv eood none (Or.inr ⟨H0, rfl⟩) (by omega)
      $$ [Hat Hold Hend Hsnap]
      as ⟨Hs, #Hc, #Hd, He, #Hl, Hf⟩
    · iframe Hat Hold Hend Hsnap Hlb0 Herr
      iright; iexact Hd0
    rw [H0]
    iapply HΦ
    iframe Hs Hc Hd He Hl
    cases o with
    | none => iexact Hf
    | some p0 => obtain ⟨c0, _⟩ := p0; simp only [Nat.max_zero]; iexact Hf
  · intro ms γs J o j old sp dq sv eood s0 Hjs Hs61
    iintro %Φ ⟨#Hinit, Hat, Hold, Hend, Hsnap, Htok, #Herr⟩ HΦ
    wp_apply wp_ApplySnapshot_gen wp_EnsureSnapshot wp_GetMetadata wp_GetIndex wp_GetTerm
      wp_CloneSnapshot ms γs J o j old sp dq sv eood (some s0) (Or.inl Hjs) Hs61
      $$ [Hat Hold Hend Hsnap Htok] as ⟨Hs, #Hc, #Hd, He, Hl, Hf⟩
    · iframe Hat Hold Hend Hsnap Htok Herr
      ileft; ipureintro; exact Hjs
    iapply HΦ
    iframe Hs Hc Hd He Hl
    cases o with
    | none => iexact Hf
    | some p0 => obtain ⟨c0, _⟩ := p0; iexact Hf
  · intro ms γs J o old sp dq sv eood s0 H0
    iintro %Φ ⟨#Hinit, Hat, Hold, Hend, #Hd0, Hsnap, Htok, #Herr⟩ HΦ
    ihave Hat : memStorAt ms γs J o iprop(J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗
        J.DL (uint.nat sv.Metadata'.Index')) $$ [Hat]
    · rw [H0]; iexact Hat
    wp_apply wp_ApplySnapshot_gen wp_EnsureSnapshot wp_GetMetadata wp_GetIndex wp_GetTerm
      wp_CloneSnapshot ms γs J o 1 old sp dq sv eood (some s0) (Or.inr ⟨H0, rfl⟩) (by omega)
      $$ [Hat Hold Hend Hsnap Htok]
      as ⟨Hs, #Hc, #Hd, He, Hl, Hf⟩
    · iframe Hat Hold Hend Hsnap Htok Herr
      iright; iexact Hd0
    rw [H0]
    iapply HΦ
    iframe Hs Hc Hd He Hl
    cases o with
    | none => iexact Hf
    | some p0 => obtain ⟨c0, _⟩ := p0; simp only [Nat.max_zero]; iexact Hf

end proof

end EtcdGrove
end Perennial
