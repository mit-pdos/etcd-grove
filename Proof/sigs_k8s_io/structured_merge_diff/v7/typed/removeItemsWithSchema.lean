/-
`typed.removeItemsWithSchema`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doList
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

theorem typed.removeItemsWithSchema.wp_proof
    (hNewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF))
    (hresolveSchema : typed.resolveSchema.spec (GF := GF))
    (hNewValueInterface : value.NewValueInterface.spec (GF := GF))
    (hremovingWalker_doMap : typed.removingWalker.doMap.spec (GF := GF))
    (hremovingWalker_doList : typed.removingWalker.doList.spec (GF := GF))
    (hremovingWalker_doScalar : typed.removingWalker.doScalar.spec (GF := GF)) :
    typed.removeItemsWithSchema.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
