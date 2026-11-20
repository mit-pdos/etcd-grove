/-
`value.listUnstructured.AtUsing_ptr`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing
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

theorem value.listUnstructured.AtUsing_ptr.wp_proof
    (h_listUnstructured_AtUsing : value.listUnstructured.AtUsing.spec (GF := GF)) :
    value.listUnstructured.AtUsing_ptr.spec (GF := GF) := fun p vs al n x => by
  wp_start as ⟨Hl, Ha, %Hx⟩
  icases isListV_ptr $$ Hl with ⟨%sl, #Hp, Hl⟩
  wp_auto
  wp_apply h_listUnstructured_AtUsing sl vs al n x $$ [Hl Ha] as %v Hv
  · iframe; ipureintro; exact Hx
  wp_end

end proof

end smd
end EtcdGrove
end Perennial
