/-
`typed.TypedValue.walker`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__walker
public import Perennial.Spec.sync.Pool__Get
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

theorem typed.TypedValue.walker.wp_proof
    (h_sync_Pool_Get : _root_.Perennial.sync.Pool.Get.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF)) :
    typed.TypedValue.walker.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
