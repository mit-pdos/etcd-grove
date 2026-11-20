/-
`fieldpath.Set.Size`: a member of the recursion cluster `fieldpath.SizeRec` (`SizeRec.lean`); its proof is the
projection of the cluster's (its body is `Set__SizeBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__SizeBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Size
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

theorem fieldpath.Set.Size.wp_proofBody
    (h_PathElementSet_Size : fieldpath.PathElementSet.Size.spec (GF := GF)) :
    fieldpath.Set.Size.specBody (GF := GF) := by
  unfold fieldpath.Set.Size.specBody fieldpath.SizeRec.specI
    fieldpath.Set.Size.specI fieldpath.SetNodeMap.Size.specI
  iintro #IH
  iintro %p %S
  wp_start as #Hs
  icases (fpC.isSet_view p S).1 $$ Hs with ⟨%v, #Hp, #Hm, #Hc, %hne⟩
  iStructNamed Hp
  wp_auto
  wp_apply (h_PathElementSet_Size (p.[fieldpath.Set', go!"Members"]) DFrac.discard S.tops) as %a ⟨-, %ha⟩
  · iframe #
    unfold isPESet
    iexists v.Members'
    iframe #
  icases IH with ⟨-, #HN⟩
  wp_apply HN $$ %(p.[fieldpath.Set', go!"Children"]) %S.deep [] as %b %hb
  · iframe #
    unfold isNodes
    iexists v.Children'
    iframe #
  iapply HΦ
  ipureintro
  intro n hn hlt
  obtain rfl := (FSet.hasCard_iff _ _).1 hn
  have hsum := fpK.set_card S hne
  have hta := (FSet.hasCard_iff _ _).1 ha.2
  have hbd := hb S.deep.card ((FSet.hasCard_iff _ _).2 rfl) (by omega)
  word

end proof

end smd
end EtcdGrove
end Perennial
