/-
`merge.Conflicts.Equals_ptr`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts__Equals_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts__Equals

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
variable [package_sem : merge.Assumptions]

theorem merge.Conflicts.Equals_ptr.wp_proof
    (h_Conflicts_Equals : merge.Conflicts.Equals.spec (GF := GF)) :
    merge.Conflicts.Equals_ptr.spec (GF := GF) := fun p dq s1 s2 a b => by
  wp_start as ⟨Hp, Ha, Hb⟩
  wp_auto
  wp_apply (h_Conflicts_Equals s1 s2 a b) $$ [$Ha $Hb] as %r %hr
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
