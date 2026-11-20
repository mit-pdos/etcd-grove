/-
`value.defaultMapZip`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.defaultMapZip
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.lexicalKeyOrderedMapZip
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.unorderedMapZip
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.defaultMapZip.wp_proof
    (h_lexicalKeyOrderedMapZip : value.lexicalKeyOrderedMapZip.spec (GF := GF))
    (h_unorderedMapZip : value.unorderedMapZip.spec (GF := GF)) :
    value.defaultMapZip.spec (GF := GF) := fun al lm rm ol or_ order fn I Q => by
  wp_start as ⟨Ha, Hl, Hr, %Hord, #Hfn, HI⟩
  wp_auto
  rcases Hord with rfl | rfl
  · rw [show decide ((W64 0 : w64) = W64 1) = false by decide]
    wp_auto
    wp_apply h_unorderedMapZip al lm rm ol or_ fn I Q $$ [Ha Hl Hr HI] as %b Hb
    · iframe; iexact Hfn
    wp_end
  · rw [show decide ((W64 1 : w64) = W64 1) = true by decide]
    wp_auto
    wp_apply h_lexicalKeyOrderedMapZip al lm rm ol or_ fn I Q $$ [Ha Hl Hr HI] as %b Hb
    · iframe; iexact Hfn
    wp_end

end proof

end smd
end EtcdGrove
end Perennial
