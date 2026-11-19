/-
`fieldpath.Set.Insert`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Descend

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

theorem fieldpath.Set.Insert.wp_proof
    (wp_PathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (wp_SetNodeMap_Descend : fieldpath.SetNodeMap.Descend.spec (GF := GF)) :
    fieldpath.Set.Insert.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
