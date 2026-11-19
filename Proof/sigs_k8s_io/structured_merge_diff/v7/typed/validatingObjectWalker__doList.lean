/-
`typed.validatingObjectWalker.doList`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listValue
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.errorf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__visitListItems

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

theorem typed.validatingObjectWalker.doList.wp_proof
    (hlistValue : typed.listValue.spec (GF := GF))
    (herrorf : typed.errorf.spec (GF := GF))
    (hvalidatingObjectWalker_visitListItems : typed.validatingObjectWalker.visitListItems.spec (GF := GF)) :
    typed.validatingObjectWalker.doList.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
