/-
`schema.Schema.Resolve`:
not proved yet (`sorry`): Draft of the `schema` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__resolveNoOverrides
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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
variable [package_sem : schema.Assumptions]

theorem schema.Schema.Resolve.wp_proof
    (h_Schema_resolveNoOverrides : schema.Schema.resolveNoOverrides.spec (GF := GF)) :
    schema.Schema.Resolve.spec (GF := GF) := by
  intro sc S tr ot
  wp_start as ⟨#HS, #Htr, %Hnd⟩
  wp_auto
  ihave %Her := LawProofs.isTypeRefOpt_er tr ot $$ Htr
  wp_apply wp_with_defer as %defer Hdefer
  wp_if_destruct
  all_goals try (exfalso; exact Hif Her)
  wp_apply h_Schema_resolveNoOverrides sc S tr ot $$ [] as %a %ok Hr
  · iframe #; ipureintro; exact Hnd
  iapply HΦ
  iexact Hr

end proof

end smd
end EtcdGrove
end Perennial
