/-
`value.valueUnstructured.AsFloat_ptr`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsFloat_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsFloat

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

theorem value.valueUnstructured.AsFloat_ptr.wp_proof
    (h_valueUnstructured_AsFloat : value.valueUnstructured.AsFloat.spec (GF := GF)) :
    value.valueUnstructured.AsFloat_ptr.spec (GF := GF) := fun _ => by
  wp_start_folded as %h
  exact h.elim

end proof

end smd
end EtcdGrove
end Perennial
