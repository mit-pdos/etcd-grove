/-
`typed.validatingObjectWalker.visitMapItems`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__visitMapItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__prepareDescent

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

theorem typed.validatingObjectWalker.visitMapItems.wp_proofBody
    (h_mapUnstructuredString_IterateUsing : value.mapUnstructuredString.IterateUsing.spec (GF := GF))
    (h_Map_FindField : schema.Map.FindField.spec (GF := GF))
    (h_ValidationErrors_WithPrefix : typed.ValidationErrors.WithPrefix.spec (GF := GF))
    (h_validatingObjectWalker_finishDescent : typed.validatingObjectWalker.finishDescent.spec (GF := GF))
    (h_validatingObjectWalker_prepareDescent : typed.validatingObjectWalker.prepareDescent.spec (GF := GF)) :
    typed.validatingObjectWalker.visitMapItems.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
