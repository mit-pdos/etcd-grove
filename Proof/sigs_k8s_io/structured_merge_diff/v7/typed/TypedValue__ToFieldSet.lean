/-
`typed.TypedValue.ToFieldSet`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__toFieldSetWalker
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__finished
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__toFieldSet

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

theorem typed.TypedValue.ToFieldSet.wp_proof
    (h_TypedValue_toFieldSetWalker : typed.TypedValue.toFieldSetWalker.spec (GF := GF))
    (h_toFieldSetWalker_finished : typed.toFieldSetWalker.finished.spec (GF := GF))
    (h_toFieldSetWalker_toFieldSet : typed.toFieldSetWalker.toFieldSet.spec (GF := GF)) :
    typed.TypedValue.ToFieldSet.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
