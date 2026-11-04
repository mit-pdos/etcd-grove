/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/daemon/metrics/Register.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: `Once.Do` of the registering closure.

Still to add as hypotheses (callees without a spec yet): `sync.Once.Do` (Perennial), `kubeRegistry.MustRegister` (component-base, names only: a boundary spec with the name-unclaimed resource).
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.daemon.metrics.Register

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [met_sem : k8s_io.kubernetes.pkg.controller.daemon.metrics.Assumptions]

theorem dsmetrics.Register.wp_proof :
    dsmetrics.Register.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end dsctl
end EtcdGrove
end Perennial
