/-
Proof of `Spec/k8s_io/client_go/util/consistency/NewNoopConsistencyStore.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.NewNoopConsistencyStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

theorem NewNoopConsistencyStore.wp_proof :
    NewNoopConsistencyStore.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_alloc_anon
  wp_auto
  wp_alloc_anon
  wp_auto
  iapply HΦ; itrivial

end proof

end consistency
end EtcdGrove
end Perennial
