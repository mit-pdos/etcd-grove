/-
The proofs of the fix-up's helpers: `nodeColor`, `sibling`, `uncle`, `grandparent` (`Specs.lean`).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.trees.redblacktree.Specs
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Iter

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions]

theorem nodeColor.wp_proof : nodeColor.spec (GF := GF) := by
  intro h D x
  wp_start as ⟨Hns, %Hx⟩
  wp_auto
  wp_if_destruct
  · dsimp only [black]
    wp_auto
    iapply HΦ; iexact Hns
  · have hxD : x ∈ D := Hx.resolve_left Hif
    ihave ⟨Hn, Hback⟩ := ownNodes_read h D x hxD $$ Hns
    wp_auto
    rw [if_neg Hif]
    iapply HΦ; iapply Hback; iexact Hn

theorem Node.sibling.wp_proof : Node.sibling.spec (GF := GF) := by
  intro h D p
  wp_start as ⟨Hns, %Hp⟩
  obtain ⟨hpD, hpn, hgD, hgn⟩ := Hp
  ihave ⟨Hp, Hback⟩ := ownNodes_read h D p hpD $$ Hns
  wp_auto
  simp only [hpn, _root_.decide_false]
  wp_auto
  simp only [hgn, _root_.decide_false]
  wp_auto
  ihave Hns := Hback $$ Hp
  ihave ⟨Hg, Hback⟩ := ownNodes_read h D _ hgD $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hg
  wp_if_destruct
  · ihave ⟨Hp, Hback⟩ := ownNodes_read h D p hpD $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    ihave ⟨Hg, Hback⟩ := ownNodes_read h D _ hgD $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hg
    rw [if_pos Hif]
    iapply HΦ; iexact Hns
  · ihave ⟨Hp, Hback⟩ := ownNodes_read h D p hpD $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hp
    ihave ⟨Hg, Hback⟩ := ownNodes_read h D _ hgD $$ Hns
    wp_auto
    ihave Hns := Hback $$ Hg
    rw [if_neg Hif]
    iapply HΦ; iexact Hns

theorem Node.uncle.wp_proof (wp_sibling : Node.sibling.spec (GF := GF)) :
    Node.uncle.spec (GF := GF) := by
  intro h D n
  wp_start as ⟨Hns, %Hp⟩
  obtain ⟨hnD, hnn, hpD, hpn, hgD, hgn⟩ := Hp
  wp_auto
  simp only [hnn, _root_.decide_false]
  wp_auto
  ihave ⟨Hn, Hback⟩ := ownNodes_read h D n hnD $$ Hns
  wp_auto
  simp only [hpn, _root_.decide_false]
  wp_auto
  ihave Hns := Hback $$ Hn
  ihave ⟨Hp, Hback⟩ := ownNodes_read h D _ hpD $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hp
  simp only [hgn, _root_.decide_false]
  wp_auto
  ihave ⟨Hn, Hback⟩ := ownNodes_read h D n hnD $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hn
  wp_apply (wp_sibling h D (h n).Parent') $$ [$Hns]
  · ipureintro; exact ⟨hpD, hpn, hgD, hgn⟩
  iintro Hns
  wp_auto
  iapply HΦ; iexact Hns

theorem Node.grandparent.wp_proof : Node.grandparent.spec (GF := GF) := by
  intro h D n
  wp_start as ⟨Hns, %Hp⟩
  obtain ⟨hnD, hnn, hpD, hpn⟩ := Hp
  wp_auto
  simp only [hnn, _root_.decide_false, Bool.not_false]
  wp_auto
  ihave ⟨Hn, Hback⟩ := ownNodes_read h D n hnD $$ Hns
  wp_auto
  simp only [hpn, _root_.decide_false, Bool.not_false]
  wp_auto
  ihave Hns := Hback $$ Hn
  ihave ⟨Hp, Hback⟩ := ownNodes_read h D _ hpD $$ Hns
  wp_auto
  ihave Hns := Hback $$ Hp
  iapply HΦ; iexact Hns

end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
