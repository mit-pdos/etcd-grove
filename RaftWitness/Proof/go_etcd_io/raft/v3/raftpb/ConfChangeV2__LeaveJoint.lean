/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChangeV2__LeaveJoint.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__LeaveJoint
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetTransition
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetChanges

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

theorem raftpb.ConfChangeV2.LeaveJoint.wp_proof
    (wp_ConfChangeV2_GetTransition : raftpb.ConfChangeV2.GetTransition.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_GetChanges : raftpb.ConfChangeV2.GetChanges.spec (GF := GF) (hG := hG)) :
    raftpb.ConfChangeV2.LeaveJoint.spec (GF := GF) (hG := hG) := by
  intro c dq m
  wp_start as Hm
  wp_auto
  wp_apply wp_ConfChangeV2_GetTransition.1 $$ [Hm]
  · iframe
  iintro Hm
  wp_auto
  wp_if_destruct
  · wp_apply wp_ConfChangeV2_GetChanges.1 $$ [Hm]
    · iframe
    iintro %chs %ls ⟨Hch, #Hccs, Hback⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hch
    ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hccs
    wp_auto
    have Hnil : chs.len = W64 0 ↔ m.changes = [] := by
      constructor
      · intro h; apply List.eq_nil_of_length_eq_zero; rw [← Hlen2, Hlen.1, h]; rfl
      · intro h; rw [h] at Hlen2; simp only [List.length_nil] at Hlen2; word
    rw [show decide (m.transition = W32 0 ∧ m.changes = []) = decide (chs.len = W64 0) by
      simp only [Hif, Hnil, true_and]]
    iapply HΦ
    iapply Hback $$ Hch
  · rw [show decide (m.transition = W32 0 ∧ m.changes = []) = false by
      simp only [Hif, false_and, decide_false]]
    iapply HΦ $$ Hm

end proof

end EtcdGrove
end Perennial
