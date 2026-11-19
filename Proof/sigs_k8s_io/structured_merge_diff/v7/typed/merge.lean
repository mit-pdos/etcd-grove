/-
`typed.merge`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.merge
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Perennial.Spec.sync.Pool__Get
public import Perennial.Spec.sync.Pool__Put
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__merge
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface

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

theorem typed.merge.wp_proof
    (hTypeRef_Equals : schema.TypeRef.Equals.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hPool_Get : sync.Pool.Get.spec (GF := GF))
    (hPool_Put : sync.Pool.Put.spec (GF := GF))
    (hNewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF))
    (hmergingWalker_merge : typed.mergingWalker.merge.spec (GF := GF))
    (hNewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    typed.merge.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
