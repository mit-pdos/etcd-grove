/-
`value.NewValueInterface`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__reuse
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

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
variable [package_sem : value.Assumptions]

theorem value.NewValueInterface.wp_proof
    (h_heapAllocator_allocValueUnstructured : value.heapAllocator.allocValueUnstructured.spec (GF := GF))
    (h_valueUnstructured_reuse : value.valueUnstructured.reuse.spec (GF := GF)) :
    value.NewValueInterface.spec (GF := GF) := fun i x => by
  wp_start as Hi
  icases valuePkg_globals $$ Hpkg with ⟨%ha, %er, #Hha, -⟩
  wp_auto
  wp_apply h_heapAllocator_allocValueUnstructured ha as %q Hq
  wp_apply h_valueUnstructured_reuse q i x $$ [Hq Hi] as %v ⟨%rfl, Hv⟩
  · iframe
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
