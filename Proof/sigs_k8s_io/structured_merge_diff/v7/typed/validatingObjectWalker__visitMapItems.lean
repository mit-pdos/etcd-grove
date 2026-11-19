/-
`typed.validatingObjectWalker.visitMapItems`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitMapItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__String
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finishDescent

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

theorem typed.validatingObjectWalker.visitMapItems.wp_proof
    (hMap_FindField : schema.Map.FindField.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hValidationErrors_WithPrefix : typed.ValidationErrors.WithPrefix.spec (GF := GF))
    (hPathElement_String : fieldpath.PathElement.String.spec (GF := GF))
    (hvalidatingObjectWalker_prepareDescent : typed.validatingObjectWalker.prepareDescent.spec (GF := GF))
    (hvalidatingObjectWalker_validate : typed.validatingObjectWalker.validate.spec (GF := GF))
    (hvalidatingObjectWalker_finishDescent : typed.validatingObjectWalker.finishDescent.spec (GF := GF)) :
    typed.validatingObjectWalker.visitMapItems.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
