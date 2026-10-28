/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChangeV2__EnterJoint.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__EnterJoint
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__GetTransition

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

theorem raftpb.ConfChangeV2.EnterJoint.wp_proof
    (wp_ConfChangeV2_GetTransition : raftpb.ConfChangeV2.GetTransition.spec (GF := GF) (hG := hG)) :
    raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG) := by
  intro c dq m Hok
  wp_start as Hm
  wp_auto
  wp_apply wp_ConfChangeV2_GetTransition.1 $$ [Hm]
  · iframe
  iintro Hm
  wp_auto
  wp_if_destruct
  · -- `Transition == Auto`: joint consensus iff more than one change (`len(c.Changes)`, read
    -- from the field)
    have Ht := Hif
    iNamed Hm
    ihave %Hlen := ownSlice_len _ _ _ $$ Hch
    ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hccs
    wp_auto
    ihave Hm : ownConfChangeV2 c dq m $$ [HT HCh Hch HC]
    · iunfold ownConfChangeV2
      iexists pt, chs, ls, cs, uf
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe cT Hccs Hcs Hpb
    wp_if_destruct
    · -- `Auto` with several changes: the switch's first case, `autoLeave = true`
      have Hn := Hif
      wp_apply wp_ConfChangeV2_GetTransition.1 $$ [Hm]
      · iframe
      iintro Hm
      wp_auto
      wp_if_destruct
      · iapply HΦ
        iframe
        have Hj : enterJointOf m.transition m.changes.length = some (true, true) := by
          unfold enterJointOf; rw [ite_eq_left (Or.inr (by word)), ite_eq_left (Or.inl Ht)]
        rw [Hj]
        ipureintro; rfl
      · exfalso; exact Hif Ht
    · have Hn := Hif
      iapply HΦ
      iframe
      have Hj : enterJointOf m.transition m.changes.length = some (false, false) := by
        unfold enterJointOf
        rw [ite_eq_right (fun h => h.elim (fun h' => h' Ht) (fun h' => by word))]
      rw [Hj]
      ipureintro; rfl
  · -- `Transition != Auto`: joint consensus, the switch
    have Ht := Hif
    wp_apply wp_ConfChangeV2_GetTransition.1 $$ [Hm]
    · iframe
    iintro Hm
    wp_auto
    wp_if_destruct
    · exfalso; exact Ht Hif
    wp_if_destruct
    · -- `JointImplicit`
      have Ht1 := Hif
      iapply HΦ
      iframe
      have Hj : enterJointOf m.transition m.changes.length = some (true, true) := by
        unfold enterJointOf; rw [ite_eq_left (Or.inl Ht), ite_eq_left (Or.inr Ht1)]
      rw [Hj]
      ipureintro; rfl
    have Ht1 := Hif
    wp_if_destruct
    · -- `JointExplicit`
      have Ht2 := Hif
      iapply HΦ
      iframe
      have Hj : enterJointOf m.transition m.changes.length = some (false, true) := by
        unfold enterJointOf
        rw [ite_eq_left (Or.inl Ht), ite_eq_right (by simp only [not_or]; exact ⟨Ht, Ht1⟩),
          ite_eq_left Ht2]
      rw [Hj]
      ipureintro; rfl
    · -- an unknown transition: `panic(fmt.Sprintf(...))`, excluded by the premise
      have Ht2 := Hif
      exfalso
      apply Hok
      unfold enterJointOf
      rw [ite_eq_left (Or.inl Ht), ite_eq_right (by simp only [not_or]; exact ⟨Ht, Ht1⟩),
        ite_eq_right Ht2]

end proof

end EtcdGrove
end Perennial
