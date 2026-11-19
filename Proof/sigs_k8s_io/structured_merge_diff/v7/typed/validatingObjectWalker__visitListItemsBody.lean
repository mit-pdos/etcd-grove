/-
`typed.validatingObjectWalker.visitListItems`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__visitListItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
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

theorem typed.validatingObjectWalker.visitListItems.wp_proofBody
    (h_MakePathElementSet : fieldpath.MakePathElementSet.spec (GF := GF))
    (h_PathElementSet_Has : fieldpath.PathElementSet.Has.spec (GF := GF))
    (h_PathElementSet_Insert : fieldpath.PathElementSet.Insert.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_AtUsing : value.listUnstructured.AtUsing.spec (GF := GF))
    (h_listUnstructured_AtUsing_ptr : value.listUnstructured.AtUsing_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (h_validatingObjectWalker_finishDescent : typed.validatingObjectWalker.finishDescent.spec (GF := GF))
    (h_validatingObjectWalker_prepareDescent : typed.validatingObjectWalker.prepareDescent.spec (GF := GF)) :
    typed.validatingObjectWalker.visitListItems.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
