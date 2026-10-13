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

theorem raftpb.ConfChangeV2.EnterJoint.wp_proof
    (wp_fmt_Sprintf : fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG) := by
  intro c ccs dq
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
          unfold enterJointOf; rw [if_pos (Or.inr (by word)), if_pos (Or.inl Ht)]
        rw [Hj]
        simp only
        ipureintro; first | rfl | trivial
      · exfalso; exact Hif Ht
    · have Hn := Hif
      iapply HΦ
      iframe
      have Hj : enterJointOf c.Transition' ccs.length = some (false, false) := by
        unfold enterJointOf; rw [if_neg (fun h => h.elim (fun h' => h' Ht) (fun h' => by word))]
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
        unfold enterJointOf; rw [if_pos (Or.inl Ht), if_pos (Or.inr Ht1)]
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
        rw [if_pos (Or.inl Ht), if_neg (by simp only [not_or]; exact ⟨Ht, Ht1⟩), if_pos Ht2]
      rw [Hj]
      simp only
      ipureintro; first | rfl | trivial
    · -- an unknown transition: `panic(fmt.Sprintf(...))`
      have Ht2 := Hif
      try wp_auto
      wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk raftpb.ConfChangeV2.ty #c]
      isplitr
      · ipureintro; rfl
      iintro %args ⟨Hargs, -⟩
      wp_apply wp_fmt_Sprintf $$ [$Hargs]
      · ipureintro
        refine _root_.Perennial.fmt.ArgsWf.cons_other _ _ _ ?_ ?_ _root_.Perennial.fmt.ArgsWf.nil
        · simp [raftpb.ConfChangeV2.ty, go.string]
        · simp [_root_.Perennial.fmt.IsIntType, raftpb.ConfChangeV2.ty, go.int, go.int64, go.int32,
            go.int16, go.int8, go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
      iintro %msg -
      try wp_auto
      wp_apply wp_panic
      try wp_auto
      iapply HΦ
      iframe
      have Hj : enterJointOf c.Transition' ccs.length = none := by
        unfold enterJointOf
        rw [if_pos (Or.inl Ht), if_neg (by simp only [not_or]; exact ⟨Ht, Ht1⟩), if_neg Ht2]
      rw [Hj]
      simp only
      ipureintro
      exact ⟨_, rfl⟩

end proof

end EtcdGrove
end Perennial
