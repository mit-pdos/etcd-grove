/-
`typed.compareWalker.doMap`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__derefMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doLeaf

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

theorem typed.compareWalker.doMap.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Empty : value.mapUnstructuredString.Empty.spec (GF := GF))
    (h_compareWalker_derefMap : typed.compareWalker.derefMap.spec (GF := GF))
    (h_compareWalker_doLeaf : typed.compareWalker.doLeaf.spec (GF := GF)) :
    typed.compareWalker.doMap.specBody (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
