/-
`typed.reconcileWithSchemaWalker.doList`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker__visitListItems

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

theorem typed.reconcileWithSchemaWalker.doList.wp_proof
    (hNewSet : fieldpath.NewSet.spec (GF := GF))
    (hreconcileWithSchemaWalker_visitListItems : typed.reconcileWithSchemaWalker.visitListItems.spec (GF := GF)) :
    typed.reconcileWithSchemaWalker.doList.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
