/-
`value.CompareUsingRec`: the cluster's Löb induction (Draft: `sorry`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListCompareUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapCompareUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsingRec

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

/-- Löb induction over the members' bodies (with `value.CompareUsingRec.specI`'s members read back as their
specs). -/
theorem value.CompareUsingRec.wp_proof
    (h_CompareUsing_body : value.CompareUsing.specBody (GF := GF))
    (h_ListCompareUsing_body : value.ListCompareUsing.specBody (GF := GF))
    (h_MapCompareUsing_body : value.MapCompareUsing.specBody (GF := GF)) :
    value.CompareUsingRec.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
