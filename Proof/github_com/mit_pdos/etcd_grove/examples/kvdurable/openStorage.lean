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
  · sorry

end proof

end kvdurable
end EtcdGrove
end Perennial
