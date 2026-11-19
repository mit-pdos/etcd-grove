/-
`fieldpath.ManagedFields.Equals`: not proved yet (`sorry`): Draft (notes/smd-plan.md), proved after the
freeze over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__APIVersion
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Applied
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.ManagedFields.Equals.wp_proof
    (h_Set_Equals : fieldpath.Set.Equals.spec (GF := GF))
    (h_versionedSet_APIVersion : fieldpath.versionedSet.APIVersion.spec (GF := GF))
    (h_versionedSet_Applied : fieldpath.versionedSet.Applied.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF)) :
    fieldpath.ManagedFields.Equals.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
