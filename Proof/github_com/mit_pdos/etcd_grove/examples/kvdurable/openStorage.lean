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
    sorry

end proof

end kvdurable
end EtcdGrove
end Perennial
