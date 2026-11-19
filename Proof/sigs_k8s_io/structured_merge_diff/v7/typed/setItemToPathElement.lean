/-
`typed.setItemToPathElement`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `errors.New`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.setItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr

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

theorem typed.setItemToPathElement.wp_proof
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF)) :
    typed.setItemToPathElement.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
