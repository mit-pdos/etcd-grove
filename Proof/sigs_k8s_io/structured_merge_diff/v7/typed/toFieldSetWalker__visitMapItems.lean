/-
`typed.toFieldSetWalker.visitMapItems`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__visitMapItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__FindField
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__finishDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert

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

theorem typed.toFieldSetWalker.visitMapItems.wp_proof
    (hMap_FindField : schema.Map.FindField.spec (GF := GF))
    (htoFieldSetWalker_prepareDescent : typed.toFieldSetWalker.prepareDescent.spec (GF := GF))
    (htoFieldSetWalker_toFieldSet : typed.toFieldSetWalker.toFieldSet.spec (GF := GF))
    (htoFieldSetWalker_finishDescent : typed.toFieldSetWalker.finishDescent.spec (GF := GF))
    (hSet_Insert : fieldpath.Set.Insert.spec (GF := GF)) :
    typed.toFieldSetWalker.visitMapItems.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
