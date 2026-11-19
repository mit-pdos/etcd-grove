/-
`fieldpath.Set.Empty`: a member of the recursion cluster `fieldpath.EmptyRec` (`EmptyRec.lean`); its proof is the
projection of the cluster's (its body is `Set__EmptyBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EmptyBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Size
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

theorem fieldpath.Set.Empty.wp_proofBody
    (h_PathElementSet_Size : fieldpath.PathElementSet.Size.spec (GF := GF)) :
    fieldpath.Set.Empty.specBody (GF := GF) := by
  unfold fieldpath.Set.Empty.specBody fieldpath.EmptyRec.specI fieldpath.Set.Empty.specI
    fieldpath.SetNodeMap.Empty.specI
  iintro #IH
  iintro %p %S
  wp_start as #Hs
  icases (fpC.isSet_view p S).1 $$ Hs with ⟨%v, #Hp, #Hm, #Hc, %hne⟩
  iStructNamed Hp
  wp_auto
  wp_apply (h_PathElementSet_Size _ DFrac.discard S.tops) $$ [] as %r ⟨-, %hr⟩
  · unfold isPESet; iexists v.Members'; iframe; iframe #
  have hz := FSet_hasCard_zero_law_holds _ _ hr.2
  rw [FSet.isEmpty_iff'] at hz
  wp_if_destruct
  · wp_end
    ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rw [fpC.isEmpty_split S hne]
    rintro ⟨h, -⟩
    have := hz.2 h
    word
  · icases IH with ⟨-, #HN⟩
    wp_apply HN $$ %(p.[fieldpath.Set', go!"Children"]) %S.deep [] as %b %hb
    · unfold isNodes; iexists v.Children'; iframe; iframe #
    wp_end
    ipureintro
    rw [hb, fpC.isEmpty_split S hne]
    have h0 : (sint.Z r).toNat = 0 := by word
    have := hz.1 h0
    exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩

end proof

end smd
end EtcdGrove
end Perennial
