/-
`value.FloatCompare`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FloatCompare
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

theorem value.FloatCompare.wp_proof :
    value.FloatCompare.spec (GF := GF) := fun a b => by
  wp_start
  wp_auto
  generalize (float64Leb b a && !float64Eq a b) = c1
  cases c1
  · wp_auto
    generalize (float64Leb a b && !float64Eq a b) = c2
    cases c2 <;> wp_auto <;> wp_end
  · wp_auto; wp_end

end proof

end smd
end EtcdGrove
end Perennial
