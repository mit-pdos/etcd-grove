/-
`typed.compareWalker.doMap`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__derefMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doLeaf
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItems

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

theorem typed.compareWalker.doMap.wp_proof
    (hcompareWalker_derefMap : typed.compareWalker.derefMap.spec (GF := GF))
    (hcompareWalker_doLeaf : typed.compareWalker.doLeaf.spec (GF := GF))
    (hcompareWalker_visitMapItems : typed.compareWalker.visitMapItems.spec (GF := GF)) :
    typed.compareWalker.doMap.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
