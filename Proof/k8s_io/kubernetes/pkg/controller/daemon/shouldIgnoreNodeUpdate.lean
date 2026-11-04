/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/shouldIgnoreNodeUpdate.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: two `Semantic.DeepEqual`s.

Still to add as hypotheses (callees without a spec yet): `conversion.Equalities.DeepEqual` (names only, `equality.Semantic`'s package fact) over the labels maps and taints slices.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.shouldIgnoreNodeUpdate

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel informer informers cache workqueue k8s_io.kubernetes.pkg.controller.daemon

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

theorem shouldIgnoreNodeUpdate.wp_proof :
    shouldIgnoreNodeUpdate.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
