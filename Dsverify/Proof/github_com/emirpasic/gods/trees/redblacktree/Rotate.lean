/-
The proofs of gods' red-black tree `replaceNode`, `rotateLeft` and `rotateRight` (`Specs.lean`).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.trees.redblacktree.Specs
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Iter

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.emirpasic.gods.maps.treemap (cmpOk sortedE Entries lookupE putE)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions] [go.BasicIntoValInj]

theorem Tree.replaceNode.wp_proof : Tree.replaceNode.spec (GF := GF) := by
  intro tr rt sz cmp h D old new
  wp_start as ⟨Htr, Hns, %Hpre⟩
  obtain ⟨hnd, hold, hpo, hnew, hpar⟩ := Hpre
  ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
  wp_auto
  wp_if_destruct
  · -- `old` is the root
    ihave Hns := Hback $$ Ho
    by_cases hn0 : new = null
    · simp only [hn0, _root_.decide_true, Bool.not_true]
      wp_auto
      iapply HΦ
      rw [replaceRes_root Hif, if_pos rfl]
      dsimp only
      iframe
    · simp only [hn0, _root_.decide_false, Bool.not_false]
      have hnD : new ∈ D := hnew.resolve_left hn0
      ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
      wp_auto
      ihave Hns := Hback $$ Ho
      ihave ⟨Hn, Hback⟩ := ownNodes_acc h D new hnD hnd $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hn
      iapply HΦ
      rw [replaceRes_root Hif, if_neg hn0]
      dsimp only
      iframe
  · have hpD : (h old).Parent' ∈ D := (hpar.resolve_left Hif).1
    ihave Hns := Hback $$ Ho
    ihave ⟨Hp, Hback⟩ := ownNodes_read h D _ hpD $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    have hif0 := Hif
    wp_if_destruct
    · -- `old` is its parent's left child
      have hL : (h (h old).Parent').Left' = old := Hif.symm
      ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
      wp_auto
      ihave Hns := Hback $$ Ho
      ihave ⟨Hp, Hback⟩ := ownNodes_acc h D _ hpD hnd $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hp
      by_cases hn0 : new = null
      · simp only [hn0, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΦ
        rw [replaceRes_left hif0 hL, if_pos rfl]
        dsimp only
        iframe
      · simp only [hn0, _root_.decide_false, Bool.not_false]
        have hnD : new ∈ D := hnew.resolve_left hn0
        ihave ⟨Ho, Hback⟩ := ownNodes_read' _ D old (h old) hold (upd_ne h _ old _ (Ne.symm hpo)) $$ Hns
        wp_auto
        ihave Hns := Hback $$ Ho
        ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D new hnD hnd $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hn
        iapply HΦ
        rw [replaceRes_left hif0 hL, if_neg hn0]
        dsimp only
        iframe
    · -- its right child
      have hL : ¬ (h (h old).Parent').Left' = old := fun e => Hif e.symm
      ihave ⟨Ho, Hback⟩ := ownNodes_read h D old hold $$ Hns
      wp_auto
      ihave Hns := Hback $$ Ho
      ihave ⟨Hp, Hback⟩ := ownNodes_acc h D _ hpD hnd $$ Hns
      wp_auto
      ihave Hns := Hback $$ Hp
      by_cases hn0 : new = null
      · simp only [hn0, _root_.decide_true, Bool.not_true]
        wp_auto
        iapply HΦ
        rw [replaceRes_right hif0 hL, if_pos rfl]
        dsimp only
        iframe
      · simp only [hn0, _root_.decide_false, Bool.not_false]
        have hnD : new ∈ D := hnew.resolve_left hn0
        ihave ⟨Ho, Hback⟩ := ownNodes_read' _ D old (h old) hold (upd_ne h _ old _ (Ne.symm hpo)) $$ Hns
        wp_auto
        ihave Hns := Hback $$ Ho
        ihave ⟨Hn, Hback⟩ := ownNodes_acc _ D new hnD hnd $$ Hns
        wp_auto
        ihave Hns := Hback $$ Hn
        iapply HΦ
        rw [replaceRes_right hif0 hL, if_neg hn0]
        dsimp only
        iframe


end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
