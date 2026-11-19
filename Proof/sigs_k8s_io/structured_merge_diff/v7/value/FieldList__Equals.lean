/-
`value.FieldList.Equals`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
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

theorem value.FieldList.Equals.wp_proof
    (h_Equals : value.Equals.spec (GF := GF)) :
    value.FieldList.Equals.spec (GF := GF) := fun f g fl gl => by
  wp_start as ⟨#Hf, #Hg⟩
  icases isFieldList_val $$ Hf with ⟨%fs, #Hfs, #HfL⟩
  icases isFieldList_val $$ Hg with ⟨%gs, #Hgs, #HgL⟩
  ihave %Hfl := isFieldsL_length $$ HfL
  ihave %Hgl := isFieldsL_length $$ HgL
  ihave %Hfsl := ownSlice_len $$ Hfs
  ihave %Hgsl := ownSlice_len $$ Hgs
  wp_auto
  wp_if_destruct
  · rename_i ik_ptr
    ihave HI : (∃ (j : w64) (k : w64), "i" ∷ i_ptr ↦ j ∗ "ik" ∷ ik_ptr ↦ k ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z f.len ∧
          fl.take (sint.nat j) = gl.take (sint.nat j)⌝ : IProp GF) $$ [-HΦ «$res0» f rhs]
    · iexists _, _; iframe; ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]; rfl
    wp_for HI
    sorry
  · sorry

end proof

end smd
end EtcdGrove
end Perennial
