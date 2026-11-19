/-
`state__typedObj`: its earlier proof was over the old model's predicates; not re-proved yet (`sorry`)
until the specs are frozen (notes/smd-plan.md). Lean-first (2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__typedObj
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.AsTyped

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

theorem state.typedObj.wp_proof
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_AsTyped : smd.typed.AsTyped.spec (GF := GF)) :
    state.typedObj.spec (GF := GF) := by
  sorry

end proof

end k8s_smd
end EtcdGrove
end Perennial
