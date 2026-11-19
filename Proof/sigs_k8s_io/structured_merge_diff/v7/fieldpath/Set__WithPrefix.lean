/-
`fieldpath.Set.WithPrefix`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet

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

theorem fieldpath.Set.WithPrefix.wp_proof
    (wp_SetNodeMap_Get : fieldpath.SetNodeMap.Get.spec (GF := GF))
    (wp_NewSet : fieldpath.NewSet.spec (GF := GF)) :
    fieldpath.Set.WithPrefix.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
