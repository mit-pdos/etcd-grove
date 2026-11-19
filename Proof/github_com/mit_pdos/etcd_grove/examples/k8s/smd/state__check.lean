/-
`state__check`: its earlier proof was over the old model's predicates; not re-proved yet (`sorry`)
until the specs are frozen (notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__check
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__AsValue_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields__Equals_ptr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem state.check.wp_proof
    (wp_AsValue_ptr : smd.typed.TypedValue.AsValue_ptr.spec (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_Equals : smd.value.Equals.spec (GF := GF))
    (wp_MFEquals_ptr : smd.fieldpath.ManagedFields.Equals_ptr.spec (GF := GF)) :
    state.check.spec (GF := GF) := by
  sorry

end proof

end k8s_smd
end EtcdGrove
end Perennial
