/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/getConfState.lean`: the four
`getIDs` in turn, each on the rest the previous one left, then the auto-leave byte, and the conf
state built (`csPts_of_struct`, its `AutoLeave` a fresh cell), as `getSnapshot`'s configuration
part.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getConfState
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getIDs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem getConfState.wp_proof (wp_getIDs : getIDs.spec (GF := GF) (hG := hG)) :
    getConfState.spec (GF := GF) (hG := hG) := by
  intro b dq c r
  wp_start as Hb
  try wp_auto
  ihave Hb := (show (b ↦*{dq} (encConf c ++ r) : IProp GF) ⊣⊢
      b ↦*{dq} (encIDs c.Voters' ++ (encIDs c.Learners' ++ (encIDs c.VotersOutgoing' ++
        (encIDs c.LearnersNext' ++ (autoB c.AutoLeave' :: r))))) by
    simp only [encConf, List.append_assoc, List.singleton_append]; exact .rfl).1 $$ Hb
  wp_apply wp_getIDs b _ _ _ $$ [$Hb] as %sv %r1 ⟨Hsv, Hr1, -⟩
  try wp_auto
  wp_apply wp_getIDs r1 _ _ _ $$ [$Hr1] as %sl %r2 ⟨Hsl, Hr2, -⟩
  try wp_auto
  wp_apply wp_getIDs r2 _ _ _ $$ [$Hr2] as %so %r3 ⟨Hso, Hr3, -⟩
  try wp_auto
  wp_apply wp_getIDs r3 _ _ _ $$ [$Hr3] as %sn %r4 ⟨Hsn, Hr4, -⟩
  try wp_auto
  ihave %Hl4 := ownSlice_len _ _ _ $$ Hr4
  have Hl4' : sint.Z r4.len = 1 + r.length := by
    have h := Hl4.1
    simp only [List.length_cons] at h
    have := Hl4.2
    have : ((r.length + 1 : Nat) : Int) = sint.Z r4.len := by rw [h]; word
    omega
  rw [decide_eq_false (by rw [Hl4']; show ¬ (_ < (1 : Int)); omega)]
  try wp_auto
  rw [ite_eq_left (by rw [Hl4']; refine ⟨by decide, ?_⟩; show (0 : Int) < _; omega)]
  wp_apply wp_load_slice_index r4 (sint.Z (W64 0)) _ _ (autoB c.AutoLeave')
    (by decide) $$ [$Hr4] as Hr4
  · ipureintro; rfl
  try wp_auto
  ihave %Hw4 := ownSlice_wf _ _ _ $$ Hr4
  rw [ite_eq_left (by rw [Hl4']; refine ⟨by decide, ?_, Hl4' ▸ Hw4.2⟩; show (1 : Int) ≤ _; omega)]
  icases (ownSlice_split_all (W64 1) r4 dq _
    ⟨by decide, by rw [Hl4']; show (1 : Int) ≤ _; omega⟩).1 $$ Hr4 with ⟨-, Hr4⟩
  simp only [show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons, List.drop_zero]
  iapply wp_fupd
  try wp_auto
  ihave %Hn4 := typedPointsto_not_null $$ «$v4»
  imod cellRO_alloc _ _ $$ «$v4» with #cA
  have Hal : decide (autoB c.AutoLeave' = W8 1) = c.AutoLeave' := by
    cases c.AutoLeave' <;> simp [autoB]
  rw [Hal]
  imod csPts_of_struct _
      (⟨zeroValDef, sv, sl, so, sn, «$v4_ptr», slice.nil, 0⟩ : raftpb.ConfState)
      c ⊤ rfl $$ [-HΦ Hr4] with Hcs
  · iframe; iexact cA
  simp only [decide_eq_true Hn4]
  imodintro
  iapply HΦ
  iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
