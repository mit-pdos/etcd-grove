/-
`value.FieldList.Compare`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Compare
public import Perennial.Spec.strings.Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Compare

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

theorem value.FieldList.Compare.wp_proof
    (h_strings_Compare : _root_.Perennial.strings.Compare.spec (GF := GF))
    (h_Compare : value.Compare.spec (GF := GF)) :
    value.FieldList.Compare.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
