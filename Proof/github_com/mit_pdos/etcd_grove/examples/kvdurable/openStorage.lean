/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/openStorage.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.openStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getUint64
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getEntry
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- Justifications nothing reads (the storage is detached throughout). -/
private def trivJ : MemJust GF where
  SV _ := iprop(True)
  B _ := iprop(True)
  DL _ := iprop(True)
  SV_pers _ := inferInstance
  B_pers _ := inferInstance
  B_timeless _ := inferInstance
  DL_pers _ := inferInstance

theorem openStorage.wp_proof
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_getSnapshot : getSnapshot.spec (GF := GF) (hG := hG))
    (wp_getEntry : getEntry.spec (GF := GF) (hG := hG))
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Snapshot.GetData.spec (GF := GF) (hG := hG))
    (wp_SMGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_SMGetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_EGetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_EGetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    openStorage.spec (GF := GF) (hG := hG) := by
  intro bp boot b f Hok Hsc
  obtain ⟨⟨Hswf, Hewf, Hnwf⟩, Hp61, Hn61, Hidx, Hpsi, Hsil, Hpc, Hcl, Hst0, Hsterm⟩ := Hok
  have Hb61 : uint.nat f.prev + 1 + f.ents.length ≤ 2 ^ 61 := by word
  wp_start as ⟨#HsInv, #Hboot, Hb⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_NewMemoryStorage as %ms %γs ⟨#Hlock, #Hd0, Hend, Hnone, Hmeta, Hfresh⟩
  try wp_auto
  -- the decode
  ihave Hb := (show (b ↦* encStor f : IProp GF) ⊣⊢ b ↦* (u64Le f.hs.Term' ++ (u64Le f.hs.Vote' ++
      (u64Le f.hs.Commit' ++ (encSnap f.snap ++ (u64Le f.prev ++ (u64Le f.prevTerm ++
      (u64Le (W64 f.ents.length) ++ encEntries f.ents))))))) from .rfl).1 $$ Hb
  wp_apply wp_getUint64 b _ _ _ $$ [$Hb] as %r1 ⟨Hr1, -⟩
  try wp_auto
  wp_apply wp_getUint64 r1 _ _ _ $$ [$Hr1] as %r2 ⟨Hr2, -⟩
  try wp_auto
  wp_apply wp_getUint64 r2 _ _ _ $$ [$Hr2] as %r3 ⟨Hr3, -⟩
  try wp_auto
  wp_apply wp_getSnapshot r3 f.snap _ Hswf $$ [$Hr3] as %sp %r4 ⟨Hsnap, Hr4⟩
  try wp_auto
  wp_apply wp_getUint64 r4 _ _ _ $$ [$Hr4] as %r5 ⟨Hr5, -⟩
  try wp_auto
  wp_apply wp_getUint64 r5 _ _ _ $$ [$Hr5] as %r6 ⟨Hr6, -⟩
  try wp_auto
  wp_apply wp_getUint64 r6 _ _ _ $$ [$Hr6] as %r7 ⟨Hr7, -⟩
  try wp_auto
  rw [decide_eq_false (by word)]
  try wp_auto
  rw [decide_eq_false (by word)]
  try wp_auto
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hr7 with #Hr7
  -- the entries: the rest holds those not read yet, the slice the ones read, frozen
  ihave IH : iprop(∃ (j : w64) (sv rv : GoSlice) (ls : List Loc),
      "i" ∷ i_ptr ↦ j ∗ "ents" ∷ ents_ptr ↦ sv ∗ "rest" ∷ rest_ptr ↦ rv ∗
      "Hsv" ∷ sv ↦* ls ∗ "Hcap" ∷ ownSliceCap Loc sv (DFrac.own 1) ∗
      "#Hls" ∷ ([∗list] l;e ∈ ls;f.ents.take (uint.nat j), entRO l e) ∗
      "#Hrv" ∷ rv ↦*□ encEntries (f.ents.drop (uint.nat j)) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ f.ents.length⌝)
    $$ [i ents rest]
  · iexists W64 0, _, r7, []
    iframe
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe Hr7
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro; exact Nat.zero_le _
  wp_for IH
  have Hnl : uint.nat (W64 f.ents.length) = f.ents.length := by word
  wp_if_destruct
  · have Hin : uint.nat j < f.ents.length := by rw [← Hnl]; word
    obtain ⟨e0, He0⟩ : ∃ e0, f.ents[uint.nat j]? = some e0 :=
      ⟨_, List.getElem?_eq_getElem Hin⟩
    have Hdrop : f.ents.drop (uint.nat j) = e0 :: f.ents.drop (uint.nat j + 1) := by
      rw [List.drop_eq_getElem_cons Hin]
      rw [List.getElem?_eq_getElem Hin] at He0
      rw [Option.some.inj He0]
    have Hwf0 : EntWf e0 := Hewf e0 (List.mem_of_getElem? He0)
    have EC : (rv ↦*□ encEntries (f.ents.drop (uint.nat j)) : IProp GF) ⊣⊢
        rv ↦*□ (encEntry e0 ++ encEntries (f.ents.drop (uint.nat j + 1))) := by
      rw [Hdrop]; exact .rfl
    ihave #Hrv' := EC.1 $$ Hrv
    try wp_auto
    wp_apply wp_getEntry rv e0 _ Hwf0 $$ [$Hrv'] as %l %rest2 ⟨Hl, #Hrest2⟩
    try wp_auto
    wp_apply wp_EGetIndex.1 l (DFrac.own 1) e0 $$ [$Hl] as Hl
    have Hei : e0.Index' = f.prev + W64 1 + j := by
      have := Hidx _ _ He0; word
    rw [decide_eq_true Hei]
    try wp_auto
    imod entOwn_freeze _ _ $$ Hl with #Hl
    wp_apply wp_slice_literal (V := Loc) [l]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsv $Hcap $Hsl2] as %sv' ⟨Hsv, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, sv', rest2, ls ++ [l]
    have Hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
    have Htk : f.ents.take (uint.nat j + 1) = f.ents.take (uint.nat j) ++ [e0] := by
      rw [List.take_add_one, He0]; rfl
    rw [Hj1, Htk]
    iframe
    iframe Hrest2
    isplitl []
    · iapply entsBig_app
      iframe Hls
      iapply BigSepL2.bigSepL2_singleton.2; iexact Hl
    ipureintro; omega
  · have Hjk : uint.nat j = f.ents.length := by rw [← Hnl]; have := Hj; word
    rw [Hjk, List.take_length, List.drop_length] at *
    ihave %Hlsl := entsBig_length $$ Hls
    imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hsv with #Hsv
    ihave #HentsO : entsRO sv f.ents $$ []
    · iunfold entsRO; iunfold entsPts; iexists ls; iframe Hsv Hls
    imod ownSnapS_persist _ _ _ $$ Hsnap with #Hsnap
    ihave #HsM := ownSnapS_M _ _ _ $$ Hsnap
    try wp_auto
    wp_apply wp_GetMetadata.1 sp DFrac.discard f.snap $$ [$HsM] as %pm ⟨#Hpm, -⟩
    wp_apply wp_SMGetIndex pm DFrac.discard f.snap.Metadata' $$ [$Hpm] as -
    try wp_auto
    ihave %Hrvl := ownSlice_len _ _ _ $$ Hrv
    have Hrv0 : rv.len = W64 0 := by
      simp only [encEntries, List.length_nil] at Hrvl; word
    have Hlast : uint.Z (f.prev + W64 f.ents.length) = uint.Z f.prev + f.ents.length := by word
    rw [decide_eq_true Hrv0]
    try wp_auto
    rw [decide_eq_false (by omega)]
    try wp_auto
    rw [decide_eq_false (by rw [Hlast]; word)]
    try wp_auto
    rw [decide_eq_false (by omega)]
    try wp_auto
    rw [decide_eq_false (by rw [Hlast]; word)]
    try wp_auto
    wp_apply wp_GetMetadata.1 sp DFrac.discard f.snap $$ [$HsM] as %pm2 ⟨#Hpm2, -⟩
    wp_apply wp_SMGetTerm pm2 DFrac.discard f.snap.Metadata' $$ [$Hpm2] as -
    try wp_auto
    -- the term checks, refuted by `KdSnapTermOk`
    wp_join (v := #false) at (if: #(decide (f.prev = W64 0)) then _ else _) with [prevTerm]
    · wp_if_destruct
      · rw [decide_eq_true (Hst0 Hif)]
        iframe; ipureintro; rfl
      · wp_join_done
    try wp_auto
    wp_join (v := #false) at (if: #(decide (f.snap.Metadata'.Index' = f.prev)) then _ else _)
      with [prevTerm st]
    · wp_if_destruct
      · have : f.prevTerm = f.snap.Metadata'.Term' := by
          rw [← Hsterm]; unfold imgTermAt; rw [Hif, ite_eq_left (Nat.le_refl _)]
        rw [decide_eq_true this.symm]
        iframe; ipureintro; rfl
      · wp_join_done
    try wp_auto
    wp_join (v := #false) at (if: #(decide (uint.Z f.prev < uint.Z f.snap.Metadata'.Index')) then _ else _)
      with [st ents si prev]
    · wp_if_destruct
      · have Hgt : uint.nat f.prev < uint.nat f.snap.Metadata'.Index' := by word
        obtain ⟨e, He⟩ : ∃ e, f.ents[uint.nat f.snap.Metadata'.Index' - uint.nat f.prev - 1]? = some e :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        icases entsRO_lookup sv f.ents _ e He $$ HentsO with ⟨%ls', %l, #Hls', #Hel, %Hl⟩
        ihave %Hsvl := entsPts_len _ _ _ $$ HentsO
        rw [ite_eq_left ⟨by word, by word⟩]
        wp_apply wp_load_slice_index sv (sint.Z (f.snap.Metadata'.Index' - f.prev - W64 1)) ls'
          DFrac.discard l (by word) $$ [Hls'] with -
        · iframe Hls'; ipureintro
          rw [show (sint.Z (f.snap.Metadata'.Index' - f.prev - W64 1)).toNat =
            uint.nat f.snap.Metadata'.Index' - uint.nat f.prev - 1 by word]
          exact Hl.1
        wp_apply wp_EGetTerm.1 l DFrac.discard e $$ [Hel] with -
        · iframe Hel
        have Ht : e.Term' = f.snap.Metadata'.Term' := by
          rw [← Hsterm]; unfold imgTermAt; rw [ite_eq_right (by omega), He]; rfl
        rw [decide_eq_true Ht]
        iframe; ipureintro; rfl
      · wp_join_done
    try wp_auto
    -- the restore: the storage registered, the stored snapshot opened for writes
    iStructNamedPrefix «$r0» "S"
    imod kdStor_register «$r0_ptr» ms γs ⊤ CoPset.subseteq_top $$ HsInv SMemoryStorage with #Hrec
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Sboot with #Sboot
    imod memSnapNone_open γs $$ Hnone with #Hlb0
    ihave #Hinit := isInitialized_access $$ Hraft
    iunfold isInitialized at Hinit
    iNamed Hinit
    iunfold errorsNewVar at ErrSnapOODNew
    icases ErrSnapOODNew with ⟨%eood, #Heood, -⟩
    ihave #Hmsf : «$r0_ptr».[KStorage, go!"MemoryStorage"] ↦□ ms $$ []
    · iunfold kdStorRec at Hrec; icases Hrec with ⟨#H, -⟩; iexact H
    -- the log's start: the snapshot applied there (`prev > 0`), or the dummy at `0`
    wp_join iprop("prev" ∷ prev_ptr ↦ f.prev ∗ "snap" ∷ snap_ptr ↦ sp ∗
        "si" ∷ si_ptr ↦ f.snap.Metadata'.Index' ∗ "prevTerm" ∷ prevTerm_ptr ↦ f.prevTerm ∗
        "s" ∷ s_ptr ↦ «$r0_ptr» ∗
        ∃ (sv0 : SnapshotM) (e0 : EntryM), "Hfresh" ∷ memStorFresh ms γs (uint.nat f.prev) sv0 ∗
          "Hend" ∷ memEnd γs (uint.nat f.prev + 1) ∗
          "#He0" ∷ memLog γs (uint.nat f.prev) DFrac.discard [e0] ∗ "%He0t" ∷ ⌜e0.Term' = f.prevTerm⌝ ∗
          "#Hcomp" ∷ memCompacted γs (uint.nat f.prev) ∗ "#HslP" ∷ memSnapLb γs (uint.nat f.prev) ∗
          "%Hsv0" ∷ ⌜uint.nat sv0.Metadata'.Index' = uint.nat f.prev⌝ ∗
          "%Hsv0e" ∷ ⌜f.snap.Metadata'.Index' = f.prev →
            sv0 = (if f.snap.Metadata'.Index' = W64 0 then memSnapEmpty else f.snap)⌝)
      at (if: #(decide (uint.Z (W64 0) < uint.Z f.prev)) then _ else _)
      with [prev snap si prevTerm s Hfresh Hend]
      as ⟨prev, snap, si, prevTerm, s, %sv0, %e0, Hfresh, Hend, #He0, %He0t, #Hcomp, #HslP, %Hsv0,
        %Hsv0e⟩
    · wp_if_destruct
      · have Hp0 : 0 < uint.nat f.prev := by word
        wp_if_destruct
        · -- `si = prev`: the file's snapshot
          have Hsi61 : uint.nat f.snap.Metadata'.Index' < 2 ^ 61 := by rw [Hif]; word
          ihave Hend1 : memEnd γs (1 + ([] : List EntryM).length) $$ [Hend]
          · iexact Hend
          wp_apply wp_ApplySnapshot ms γs trivJ (some (0, memSnapEmpty)) 1 [] sp DFrac.discard f.snap
            _ (by rw [Hif]; omega) Hsi61 $$ [Hfresh Hend1]
            as ⟨-, #Hcomp, #Hdum, Hend, #Hslb, Hfresh⟩
          · rw [memStorAt_some]
            iframe Hlock Hfresh Hend1 Hlb0 Heood
            isplitl []
            · iapply memLog_nil
            iunfold snapArg; iright; iexact Hsnap
          have Htp : f.snap.Metadata'.Term' = f.prevTerm := by
            rw [← Hsterm]; unfold imgTermAt; rw [Hif, ite_eq_left (Nat.le_refl _)]
          have Hp0' : f.prev ≠ W64 0 := by intro h; rw [h] at Hp0; exact absurd Hp0 (by decide)
          rw [Nat.zero_max, Hif]
          isplitr
          · ipureintro; rfl
          iframe prev snap si prevTerm s
          iexists f.snap, memDummy f.snap
          iframe Hfresh Hend Hdum Hcomp Hslb
          ipureintro
          refine ⟨Htp, by rw [Hif], fun _ => ?_⟩
          rw [ite_eq_right Hp0']
        · -- `si > prev`: a base snapshot at the log's start
          rename_i pidx
          irename : (pidx ↦ f.prev : IProp GF) => Hpi
          imod cellRO_alloc _ _ $$ Hpi with #cI
          imod cellRO_alloc _ _ $$ «$v1» with #cT
          imod smPts_of_struct «$v0_ptr» ⟨zeroValDef, null, pidx, «$v1_ptr», slice.nil, 0⟩
            (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) f.prev f.prevTerm) ⊤ rfl
            $$ [«$v0»] with Hsm
          · iframe «$v0»; iframe cI cT
            iunfold csOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
          ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
          · iapply ownSlice_nil
          imod ownSnapM_of_struct «$r0_ptr» ⟨zeroValDef, slice.nil, «$v0_ptr», slice.nil, 0⟩
            (SnapshotM.mk [] (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) f.prev f.prevTerm))
            ⊤ rfl $$ [«$r0» Hnil Hsm] with Hbs
          · iframe «$r0» Hnil
            iunfold smOpt; iright; iexact Hsm
          have Hp61' : uint.nat f.prev < 2 ^ 61 := by word
          ihave Hend1 : memEnd γs (1 + ([] : List EntryM).length) $$ [Hend]
          · iexact Hend
          wp_apply wp_ApplySnapshot ms γs trivJ (some (0, memSnapEmpty)) 1 [] «$r0_ptr» (DFrac.own 1)
            (SnapshotM.mk [] (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) f.prev f.prevTerm))
            _ (by simp only; omega) (by simp only; omega) $$ [Hfresh Hend1 Hbs]
            as ⟨-, #Hcomp, #Hdum, Hend, #Hslb, Hfresh⟩
          · rw [memStorAt_some]
            iframe Hlock Hfresh Hend1 Hlb0 Heood
            isplitl []
            · iapply memLog_nil
            iunfold snapArg; ileft; iframe Hbs; ipureintro; rfl
          simp only [Nat.zero_max]
          isplitr
          · ipureintro; trivial
          iframe prev snap si prevTerm s
          iexists _, _
          iframe Hfresh Hend Hdum Hcomp Hslb
          ipureintro
          refine ⟨rfl, rfl, fun h => absurd h Hif⟩
      · -- (`word` here leaves a proof the kernel rejects)
        have Hp0 : f.prev = W64 0 := by
          have h : ¬ (0 < (f.prev.toNat : Int)) := Hif
          apply BitVec.eq_of_toNat_eq; show f.prev.toNat = 0; omega
        isplitr
        · ipureintro; trivial
        rw [Hp0, show uint.nat (W64 0) = 0 from rfl, Nat.zero_add]
        iframe prev snap si prevTerm s
        iexists memSnapEmpty, zero_val EntryM
        iframe Hfresh Hend
        isplitl []
        · iexact Hd0
        isplitl []
        · ipureintro; exact (Hst0 Hp0).symm
        isplitl []
        · iapply memCompacted_zero
        isplitl []
        · iexact Hlb0
        ipureintro
        refine ⟨rfl, fun h => ?_⟩
        rw [h, ite_eq_left rfl]
    -- the entries after the log's start
    ihave ⟨HA, HB⟩ : (if f.ents = [] then emp else
        memLog γs (uint.nat f.prev + 1) (DFrac.own 1) [] ∗
          memEnd γs (uint.nat f.prev + 1 + ([] : List EntryM).length)) ∗
        (if f.ents = [] then memEnd γs (uint.nat f.prev + 1) else emp) $$ [Hend]
    · by_cases Hne : f.ents = []
      · simp only [Hne, ite_true]; iframe Hend
      · simp only [Hne, ite_false, List.length_nil, Nat.add_zero]
        iframe Hend
        iapply memLog_nil
    have Hidx1 : ∀ (j : Nat) (e : EntryM), f.ents[j]? = some e →
        uint.nat e.Index' = uint.nat f.prev + 1 + j := fun j e h => Hidx j e h
    wp_apply wp_Append ms γs (uint.nat f.prev + 1) [] f.ents sv DFrac.discard Hidx1 Hb61
      $$ [HA] as ⟨-, HA⟩
    · iframe HA HentsO Hlock
    ihave ⟨Hlog, Hend⟩ : memLog γs (uint.nat f.prev + 1) (DFrac.own 1) f.ents ∗
        memEnd γs (uint.nat f.prev + 1 + f.ents.length) $$ [HA HB]
    · by_cases Hne : f.ents = []
      · simp only [Hne, ite_true, List.length_nil, Nat.add_zero]
        iframe HB
        iapply memLog_nil
      · simp only [Hne, ite_false]
        iframe HA
    try wp_auto
    -- the snapshot taken again from the log above its start (`si > prev`)
    wp_join iprop("prev" ∷ prev_ptr ↦ f.prev ∗ "snap" ∷ snap_ptr ↦ sp ∗
        "si" ∷ si_ptr ↦ f.snap.Metadata'.Index' ∗ "s" ∷ s_ptr ↦ «$r0_ptr» ∗
        "Hfresh" ∷ memStorFresh ms γs (uint.nat f.prev)
          (if f.snap.Metadata'.Index' = W64 0 then memSnapEmpty else f.snap) ∗
        "#Hfz" ∷ memLog γs (uint.nat f.prev + 1) DFrac.discard
          (f.ents.take (uint.nat f.snap.Metadata'.Index' - uint.nat f.prev)) ∗
        "Hown" ∷ memLog γs (uint.nat f.snap.Metadata'.Index' + 1) (DFrac.own 1)
          (f.ents.drop (uint.nat f.snap.Metadata'.Index' - uint.nat f.prev)) ∗
        "#Hslb" ∷ memSnapLb γs (uint.nat f.snap.Metadata'.Index'))
      at (if: #(decide (uint.Z f.prev < uint.Z f.snap.Metadata'.Index')) then _ else _)
      with [prev snap si s Hfresh Hlog]
      as ⟨prev, snap, si, s, Hfresh, #Hfz, Hown, #Hslb⟩
    · wp_if_destruct
      · sorry
      · have Hsp : f.snap.Metadata'.Index' = f.prev := by
          apply BitVec.eq_of_toNat_eq
          have h1 : ¬ ((f.prev.toNat : Int) < f.snap.Metadata'.Index'.toNat) := Hif
          have h2 : (f.prev.toNat : Int) ≤ f.snap.Metadata'.Index'.toNat := Hpsi
          omega
        isplitr
        · ipureintro; exact True.intro
        obtain rfl := Hsv0e Hsp
        iframe prev snap si s Hfresh
        rw [Hsp, Nat.sub_self, List.take_zero, List.drop_zero]
        iframe Hlog HslP
        iapply memLog_nil
    sorry

end proof

end kvdurable
end EtcdGrove
end Perennial
