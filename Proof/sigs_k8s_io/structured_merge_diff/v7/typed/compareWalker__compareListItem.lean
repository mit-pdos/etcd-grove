/-
`typed.compareWalker.compareListItem`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareListItem
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__prepareDescent
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__finishDescent

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

theorem typed.compareWalker.compareListItem.wp_proof
    (hcompareWalker_prepareDescent : typed.compareWalker.prepareDescent.spec (GF := GF))
    (hcompareWalker_compare : typed.compareWalker.compare.spec (GF := GF))
    (hcompareWalker_finishDescent : typed.compareWalker.finishDescent.spec (GF := GF)) :
    typed.compareWalker.compareListItem.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
