/-
The proof of gods' red-black tree `NewWith` (`Specs.lean`).
-/
module

public import Dsverify.Spec.github_com.emirpasic.gods.trees.redblacktree.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.emirpasic.gods.trees.redblacktree

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.emirpasic.gods.maps.treemap (cmpOk sortedE Entries lookupE putE)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [redblacktree.Assumptions]

theorem NewWith.wp_proof : NewWith.spec (GF := GF) := by
  intro cmp enc
  wp_start as #Hcmp
  wp_auto
  iapply HΦ
  iapply (isTree_of _ enc cmp .leaf (fun _ => zero_val Node) [] [] ⟨List.Pairwise.nil, rfl, Or.inl rfl⟩)
  isplitl [«$r0»]
  · iapply (treeRaw_of _ enc cmp .leaf (fun _ => zero_val Node) [] (W64 0) ⟨trivial, .nil, .nil⟩)
    iframe
    simp only [ownNodes_nil]; itrivial
  iexact Hcmp

end proof

end Perennial.github_com.emirpasic.gods.trees.redblacktree
