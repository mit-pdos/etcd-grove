/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/getSnapshot.lean`. Lean-first (no
Rocq counterpart): the readers in turn (`getUint64`, `getIDs`, the auto-leave byte, `getBytes`),
each on the rest the previous one left, all succeeding on `encSnap s`; then the three records
built (`csPts_of_struct`, the metadata by hand, `ownSnapS_of_struct`: every pointer field set),
the data a slice of `b`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getUint64
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getIDs
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

theorem getSnapshot.wp_proof (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_getIDs : getIDs.spec (GF := GF) (hG := hG))
    (wp_getBytes : getBytes.spec (GF := GF) (hG := hG)) :
    getSnapshot.spec (GF := GF) (hG := hG) := by
  intro b s r Hwf
  wp_start as Hb
  try wp_auto
  ihave Hb := (show (b ↦* (encSnap s ++ r) : IProp GF) ⊣⊢
      b ↦* (u64Le s.Metadata'.Index' ++ (u64Le s.Metadata'.Term' ++
        (encIDs s.Metadata'.ConfState'.Voters' ++ (encIDs s.Metadata'.ConfState'.Learners' ++
        (encIDs s.Metadata'.ConfState'.VotersOutgoing' ++
        (encIDs s.Metadata'.ConfState'.LearnersNext' ++
        (autoB s.Metadata'.ConfState'.AutoLeave' :: (putB s.Data' ++ r)))))))) by
    simp only [encSnap, encConf, List.append_assoc, List.singleton_append]; exact .rfl).1 $$ Hb
  wp_apply wp_getUint64 b _ _ _ $$ [$Hb] as %r1 ⟨Hr1, -⟩
  try wp_auto
  wp_apply wp_getUint64 r1 _ _ _ $$ [$Hr1] as %r2 ⟨Hr2, -⟩
  try wp_auto
  wp_apply wp_getIDs r2 _ _ _ $$ [$Hr2] as %sv %r3 ⟨Hsv, Hr3, -⟩
  try wp_auto
  wp_apply wp_getIDs r3 _ _ _ $$ [$Hr3] as %sl %r4 ⟨Hsl, Hr4, -⟩
  try wp_auto
  wp_apply wp_getIDs r4 _ _ _ $$ [$Hr4] as %so %r5 ⟨Hso, Hr5, -⟩
  try wp_auto
  wp_apply wp_getIDs r5 _ _ _ $$ [$Hr5] as %sn %r6 ⟨Hsn, Hr6, -⟩
  try wp_auto
  ihave %Hl6 := ownSlice_len _ _ _ $$ Hr6
  have Hl6' : sint.Z r6.len = 1 + (8 + s.Data'.length + r.length) := by
    have h := Hl6.1
    simp only [List.length_cons, List.length_append, putB_length] at h
    have := Hl6.2
    have : (((8 + s.Data'.length + r.length) + 1 : Nat) : Int) = sint.Z r6.len := by
      rw [h]; word
    omega
  rw [decide_eq_false (by rw [Hl6']; show ¬ (_ < (1 : Int)); omega)]
  try wp_auto
  rw [ite_eq_left (by rw [Hl6']; refine ⟨by decide, ?_⟩; show (0 : Int) < _; omega)]
  wp_apply wp_load_slice_index r6 (sint.Z (W64 0)) _ _ (autoB s.Metadata'.ConfState'.AutoLeave')
    (by decide) $$ [$Hr6] as Hr6
  · ipureintro; rfl
  try wp_auto
  ihave %Hw6 := ownSlice_wf _ _ _ $$ Hr6
  rw [ite_eq_left (by rw [Hl6']; refine ⟨by decide, ?_, Hl6' ▸ Hw6.2⟩; show (1 : Int) ≤ _; omega)]
  icases (ownSlice_split_all (W64 1) r6 (DFrac.own 1) _
    ⟨by decide, by rw [Hl6']; show (1 : Int) ≤ _; omega⟩).1 $$ Hr6 with ⟨-, Hr6⟩
  simp only [show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons, List.drop_zero]
  iapply wp_fupd
  wp_apply wp_getBytes _ _ _ _ Hwf.2 $$ [$Hr6] as %data %r7 ⟨Hdata, Hr7, -⟩
  try wp_auto
  -- the three records, every pointer field set
  ihave %Hn4 := typedPointsto_not_null $$ «$v4»
  ihave %Hn1 := typedPointsto_not_null $$ «$v1»
  ihave %Hn2 := typedPointsto_not_null $$ «$v2»
  imod cellRO_alloc _ _ $$ «$v4» with #cA
  imod cellRO_alloc _ _ $$ «$v1» with #cI
  imod cellRO_alloc _ _ $$ «$v2» with #cT
  have Hal : decide (autoB s.Metadata'.ConfState'.AutoLeave' = W8 1) =
      s.Metadata'.ConfState'.AutoLeave' := by
    cases s.Metadata'.ConfState'.AutoLeave' <;> simp [autoB]
  rw [Hal]
  imod csPts_of_struct _
      (⟨zeroValDef, sv, sl, so, sn, «$v4_ptr», slice.nil, 0⟩ : raftpb.ConfState)
      s.Metadata'.ConfState' ⊤ rfl $$ [-HΦ Hdata Hr7 «$v0» «$r0»] with Hcs
  · iframe; iexact cA
  rename_i csp
  simp only [decide_eq_true Hn4]
  icases csPts_nn _ _ _ _ $$ Hcs with ⟨Hcs, %Hcsn⟩
  ihave %Hmn := typedPointsto_not_null $$ «$v0»
  icases typedPointsto_split _ _ _ $$ «$v0» with Hm
  simp only [TypedPointsto.typedPointstoDef]
  icases Hm with ⟨state, ConfState, Index, Term, unknownFields, sizeCache, -⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.SnapshotMetadata «$v0_ptr» zeroValDef 0 slice.nil [] ⊤
    $$ [state sizeCache unknownFields Hnil] with #Hpbm
  · iframe
  ihave Hsm : smPtsS «$v0_ptr» (DFrac.own 1) s.Metadata' $$ [ConfState Index Term Hcs]
  · iunfold smPtsS
    iexists csp, «$v1_ptr», «$v2_ptr», []
    isplitr
    · ipureintro; exact ⟨Hmn, Hcsn, Hn1, Hn2⟩
    iframe ConfState Index Term
    iframe cI cT Hpbm
    iunfold csSet; ileft; iexact Hcs
  imod ownSnapS_of_struct «$r0_ptr»
      (⟨zeroValDef, data, «$v0_ptr», slice.nil, 0⟩ : raftpb.Snapshot) s ⊤ rfl
      $$ [«$r0» Hdata Hsm] with Hs
  · iframe
  imodintro
  iapply HΦ
  iframe

end proof

end kvdurable
end EtcdGrove
end Perennial
