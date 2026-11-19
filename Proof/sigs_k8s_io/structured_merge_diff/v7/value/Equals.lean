/-
`value.Equals`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsing
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

theorem value.Equals.wp_proof
    (h_EqualsUsing : value.EqualsUsing.spec (GF := GF)) :
    value.Equals.spec (GF := GF) := fun a b dq1 dq2 x y => by
  wp_start as ⟨Hx, Hy⟩
  icases valuePkg_globals $$ Hpkg with ⟨%ha, %er, #Hha, -⟩
  wp_auto
  wp_apply h_EqualsUsing _ a b dq1 dq2 x y $$ [Hx Hy] as %r ⟨-, Hx, Hy, %Hr⟩
  · iframe; iapply isAlloc_heap_intro
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
