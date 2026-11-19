/-
`typed.removeItemsWithSchema`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removeItemsWithSchemaBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchemaBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doScalar

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
variable [package_sem : typed.Assumptions]

theorem typed.removeItemsWithSchema.wp_proofBody
    (h_resolveSchema : typed.resolveSchema.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF))
    (h_NewValueInterface : value.NewValueInterface.spec (GF := GF))
    (h_removingWalker_doScalar : typed.removingWalker.doScalar.spec (GF := GF)) :
    typed.removeItemsWithSchema.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
