/-
`value.CompareUsing`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.IntCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.BoolCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FloatCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListCompareUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapCompareUsing

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

theorem value.CompareUsing.wp_proof
    (wp_IntCompare : value.IntCompare.spec (GF := GF))
    (wp_BoolCompare : value.BoolCompare.spec (GF := GF))
    (wp_FloatCompare : value.FloatCompare.spec (GF := GF))
    (wp_ListCompareUsing : value.ListCompareUsing.spec (GF := GF))
    (wp_MapCompareUsing : value.MapCompareUsing.spec (GF := GF))
    (h_valueM : isValF_methods.law (GF := GF))
    (h_allocM : isAlloc_methods.law (GF := GF)) :
    value.CompareUsing.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
