/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChangeV2__EnterJoint.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__EnterJoint
public import Spec.fmt.Sprintf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.ConfChangeV2.EnterJoint.wp_proof :
    raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG) := by
  intro c ccs dq Hok
  wp_start as Hccs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hccs
  wp_auto
  wp_if_destruct
  · -- `Transition == Auto`: joint consensus iff more than one change
    have Ht := Hif
    try wp_auto
    wp_if_destruct
    · -- `Auto` with several changes: the first case, `autoLeave = true`
      have Hn := Hif
      try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        iframe
        have Hj : enterJointOf c.Transition' ccs.length = some (true, true) := by
          unfold enterJointOf; rw [ite_eq_left (Or.inr (by word)), ite_eq_left (Or.inl Ht)]
        rw [Hj]
        simp only
        ipureintro; first | rfl | trivial
      · exfalso; exact Hif Ht
    · have Hn := Hif
      iapply HΦ
      iframe
      have Hj : enterJointOf c.Transition' ccs.length = some (false, false) := by
        unfold enterJointOf; rw [ite_eq_right (fun h => h.elim (fun h' => h' Ht) (fun h' => by word))]
      rw [Hj]
      simp only
      ipureintro; first | rfl | trivial
  · -- `Transition != Auto`: joint consensus, the switch
    have Ht := Hif
    wp_if_destruct
    · exfalso; exact Ht Hif
    try wp_auto
    wp_if_destruct
    · -- `JointImplicit`
      have Ht1 := Hif
      try wp_auto
      iapply HΦ
      iframe
      have Hj : enterJointOf c.Transition' ccs.length = some (true, true) := by
        unfold enterJointOf; rw [ite_eq_left (Or.inl Ht), ite_eq_left (Or.inr Ht1)]
      rw [Hj]
      simp only
      ipureintro; first | rfl | trivial
    have Ht1 := Hif
    try wp_auto
    wp_if_destruct
    · -- `JointExplicit`
      have Ht2 := Hif
      try wp_auto
      iapply HΦ
      iframe
      have Hj : enterJointOf c.Transition' ccs.length = some (false, true) := by
        unfold enterJointOf
        rw [ite_eq_left (Or.inl Ht), ite_eq_right (by simp only [not_or]; exact ⟨Ht, Ht1⟩), ite_eq_left Ht2]
      rw [Hj]
      simp only
      ipureintro; first | rfl | trivial
    · -- an unknown transition: `panic(fmt.Sprintf(...))`, excluded by the premise
      have Ht2 := Hif
      exfalso
      apply Hok
      unfold enterJointOf
      rw [ite_eq_left (Or.inl Ht), ite_eq_right (by simp only [not_or]; exact ⟨Ht, Ht1⟩), ite_eq_right Ht2]

end proof

end EtcdGrove
end Perennial
