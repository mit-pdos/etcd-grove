/-
`typed.TypedValue.Compare`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__Equals
public import Perennial.Spec.sync.Pool__Get
public import Perennial.Spec.sync.Pool__Put
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator

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

theorem typed.TypedValue.Compare.wp_proof
    (h_NewSet : fieldpath.NewSet.spec (GF := GF))
    (h_TypeRef_Equals : schema.TypeRef.Equals.spec (GF := GF))
    (h_sync_Pool_Get : _root_.Perennial.sync.Pool.Get.spec (GF := GF))
    (h_sync_Pool_Put : _root_.Perennial.sync.Pool.Put.spec (GF := GF))
    (h_compareWalker_compare : typed.compareWalker.compare.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF)) :
    typed.TypedValue.Compare.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
