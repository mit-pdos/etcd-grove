/-
`value.emptyRange.Item`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.emptyRange__Item
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

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

theorem value.emptyRange.Item.wp_proof :
    value.emptyRange.Item.spec (GF := GF) := fun q vs n x => by
  wp_start as ⟨Hr, %Hx⟩
  iunfold ownRange at Hr
  icases Hr with (⟨%q', %h⟩ | ⟨%q', %sl, %w, %iw, %h, -⟩)
  · obtain ⟨-, rfl, -⟩ := h
    simp at Hx
  · exfalso; simp [emptyRange_ne_listUnstructuredRange] at h

end proof

end smd
end EtcdGrove
end Perennial
