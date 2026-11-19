/-
`fieldpath.SetNodeMap.Empty`: a member of the recursion cluster `fieldpath.EmptyRec` (`EmptyRec.lean`); its proof is the
projection of the cluster's (its body is `SetNodeMap__EmptyBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EmptyBody
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsTrie

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.SetNodeMap.Empty.wp_proofBody :
    fieldpath.SetNodeMap.Empty.specBody (GF := GF) := by
  unfold fieldpath.SetNodeMap.Empty.specBody fieldpath.EmptyRec.specI fieldpath.Set.Empty.specI
    fieldpath.SetNodeMap.Empty.specI
  iintro #IH
  iintro %l %D
  wp_start as #Hn
  unfold isNodes
  icases Hn with ⟨%m, #Hl, Hm⟩
  icases (fpC.isNodesV_view m D).1 $$ Hm with ⟨%ns, %nl, #Hns, #Hnl, %hok⟩
  iStructNamed Hl
  wp_auto
  ihave %hlen := ownSlice_len $$ Hns
  ihave %hnl := fpC.nodesL_length $$ Hnl
  ihave HI : (i_ptr ↦ W64 0 ∗ ∃ x : fieldpath.setNode, n_ptr ↦ x : IProp GF) $$ [i n]
  · iframe
  wp_for HI
  icases HI with ⟨i, %x, n⟩
  wp_auto
  wp_if_destruct
  · have hP : sint.Z (W64 0) < sint.Z m.members'.len := by
      by_cases h : sint.Z (W64 0) < sint.Z m.members'.len
      · exact h
      · exact absurd Hif (by simp [intoVal_eq_iff]; word)
    list_elem ns 0 as nd
    rw [if_pos ⟨by decide, hP⟩]
    wp_apply (wp_load_slice_index m.members' (sint.Z (W64 0)) ns DFrac.discard nd (by decide)) $$ [Hns] as -
    · iframe #; ipureintro; exact Hnd_lookup
    icases fpC.nodesL_lookup ns nl 0 nd Hnd_lookup $$ Hnl with ⟨%pe, %S, %hS, #Hpe, #HS⟩
    icases IH with ⟨#HE, -⟩
    wp_apply HE $$ %nd.set' %S [] as %b %hb
    · iframe #
    have hmem : (pe, S) ∈ nl := List.mem_of_getElem? hS
    have hbf : b = false := by
      cases b
      · rfl
      · obtain ⟨-, ⟨q, hq⟩, -⟩ := hok.1.2 pe S hmem
        exact absurd hq ((fpC.isEmpty_iff S).1 (hb.1 rfl) q)
    subst hbf
    wp_auto
    wp_for_post
    wp_end
    ipureintro
    rw [fpC.nl_isEmpty nl hok.1 D hok.2]
    simp only [Bool.false_eq_true, false_iff]
    intro h; rw [h] at hmem; simp at hmem
  · have hP : ¬ sint.Z (W64 0) < sint.Z m.members'.len := by
      intro h; exact Hif (by simp [intoVal_eq_iff]; word)
    simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_end
    ipureintro
    rw [fpC.nl_isEmpty nl hok.1 D hok.2]
    simp only [true_iff]
    have : ns.length = 0 := by word
    rw [← List.length_eq_zero_iff, ← hnl, this]

end proof

end smd
end EtcdGrove
end Perennial
