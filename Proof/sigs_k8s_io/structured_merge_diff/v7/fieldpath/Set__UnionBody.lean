/-
`fieldpath.Set.Union`: a member of the recursion cluster `fieldpath.UnionRec` (`UnionRec.lean`); its proof is the
projection of the cluster's (its body is `Set__UnionBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__UnionBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Union
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet

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

theorem fieldpath.Set.Union.wp_proofBody
    (h_PathElementSet_Union : fieldpath.PathElementSet.Union.spec (GF := GF)) :
    fieldpath.Set.Union.specBody (GF := GF) := by
  unfold fieldpath.Set.Union.specBody fieldpath.UnionRec.specI
    fieldpath.Set.Union.specI fieldpath.SetNodeMap.Union.specI
  iintro #IH
  iintro %p %p2 %A %B
  wp_start as ⟨#Hs, #Hs2⟩
  icases (fpC.isSet_view p A).1 $$ Hs with ⟨%v, #Hp, #Hm, #Hc, %hne⟩
  icases (fpC.isSet_view p2 B).1 $$ Hs2 with ⟨%v2, #Hp2, #Hm2, #Hc2, %hne2⟩
  iStructNamedSuffix Hp "1"
  iStructNamedSuffix Hp2 "2"
  wp_auto
  wp_apply (h_PathElementSet_Union (p.[fieldpath.Set', go!"Members"])
    (p2.[fieldpath.Set', go!"Members"]) DFrac.discard DFrac.discard A.tops B.tops) as %rm ⟨-, -, Hrm⟩
  · iframe #
    isplit
    · unfold isPESet; iexists v.Members'; iframe #
    · unfold isPESet; iexists v2.Members'; iframe #
  unfold ownPESet
  icases Hrm with ⟨%mv, Hrmp, Hmv⟩
  wp_auto
  icases IH with ⟨-, #HN⟩
  wp_apply HN $$ %(p.[fieldpath.Set', go!"Children"]) %(p2.[fieldpath.Set', go!"Children"])
    %A.deep %B.deep [] as %rc Hrc
  · iframe #
    isplit
    · unfold isNodes; iexists v.Children'; iframe #
    · unfold isNodes; iexists v2.Children'; iframe #
  unfold isNodes
  icases Hrc with ⟨%cv, #Hrcp, #Hcv⟩
  iapply wp_fupd
  wp_auto
  ipersist «$r0»
  ihave Hmv' := ownPESetV_persist_law_holds _ _ $$ Hmv
  imod Hmv'
  imodintro
  iapply HΦ
  iapply (fpS.isSet_of_parts _ _ (PathSet.union A B) _ _ (fpS.tops_union A B) (fpS.deep_union A B)
    (fpS.ne_union hne hne2))
  iframe #
  iexact Hmv'

end proof

end smd
end EtcdGrove
end Perennial
