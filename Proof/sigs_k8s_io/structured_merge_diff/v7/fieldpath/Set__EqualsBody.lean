/-
`fieldpath.Set.Equals`: a member of the recursion cluster `fieldpath.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `Set__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EqualsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Equals
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard

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

theorem fieldpath.Set.Equals.wp_proofBody
    (h_PathElementSet_Equals : fieldpath.PathElementSet.Equals.spec (GF := GF)) :
    fieldpath.Set.Equals.specBody (GF := GF) := by
  unfold fieldpath.Set.Equals.specBody fieldpath.EqualsRec.specI
    fieldpath.Set.Equals.specI fieldpath.SetNodeMap.Equals.specI
  iintro #IH
  iintro %p %p2 %A %B
  wp_start as ⟨#Hs, #Hs2⟩
  icases (fpC.isSet_view p A).1 $$ Hs with ⟨%v, #Hp, #Hm, #Hc, %hne⟩
  icases (fpC.isSet_view p2 B).1 $$ Hs2 with ⟨%v2, #Hp2, #Hm2, #Hc2, %hne2⟩
  iStructNamed Hp
  iStructNamed Hp2
  wp_auto
  wp_apply (h_PathElementSet_Equals (p.[fieldpath.Set', go!"Members"])
    (p2.[fieldpath.Set', go!"Members"]) DFrac.discard DFrac.discard A.tops B.tops) as %a ⟨-, -, %ha⟩
  · iframe #
    isplit
    · unfold isPESet; iexists v.Members'; iframe #
    · unfold isPESet; iexists v2.Members'; iframe #
  cases a
  · wp_auto
    iapply HΦ
    ipureintro
    rw [fpK.set_eq_iff A B hne hne2]
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h; exact absurd (ha.2 h) (by simp)
  · wp_auto
    icases IH with ⟨-, #HN⟩
    wp_apply HN $$ %(p.[fieldpath.Set', go!"Children"]) %(p2.[fieldpath.Set', go!"Children"])
      %A.deep %B.deep [] as %b %hb
    · iframe #
      isplit
      · unfold isNodes; iexists v.Children'; iframe #
      · unfold isNodes; iexists v2.Children'; iframe #
    iapply HΦ
    ipureintro
    rw [fpK.set_eq_iff A B hne hne2, hb, ← ha]
    simp

end proof

end smd
end EtcdGrove
end Perennial
