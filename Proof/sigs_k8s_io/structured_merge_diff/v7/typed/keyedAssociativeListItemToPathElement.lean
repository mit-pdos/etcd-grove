/-
`typed.keyedAssociativeListItemToPathElement`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).

Callees without a spec file here (other packages', the standard library's, or the
walker's own interface calls through a bundle): `errors.New`, `fmt.Errorf`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.keyedAssociativeListItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.getAssociativeKeyDefault
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Sort
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

theorem typed.keyedAssociativeListItemToPathElement.wp_proof
    (hgetAssociativeKeyDefault : typed.getAssociativeKeyDefault.spec (GF := GF))
    (hFieldList_Sort : value.FieldList.Sort.spec (GF := GF))
    (hNewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    typed.keyedAssociativeListItemToPathElement.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
