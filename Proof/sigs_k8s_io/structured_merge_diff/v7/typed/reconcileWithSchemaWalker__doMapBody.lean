/-
`typed.reconcileWithSchemaWalker.doMap`: a member of the recursion cluster `typed.reconcileWithSchemaWalkerRec` (`reconcileWithSchemaWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `reconcileWithSchemaWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.isUntypedDeducedMap

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

theorem typed.reconcileWithSchemaWalker.doMap.wp_proofBody
    (h_NewSet : fieldpath.NewSet.spec (GF := GF))
    (h_Set_Size : fieldpath.Set.Size.spec (GF := GF))
    (h_isUntypedDeducedMap : typed.isUntypedDeducedMap.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.doMap.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
