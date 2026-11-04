/-
Package initialization of `k8s_io.api.extensions.v1beta1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace k8s_io.api.extensions.v1beta1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.api.extensions.v1beta1`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrInvalidLengthGenerated.init,
        ErrIntOverflowGenerated.init,
        ErrUnexpectedEndOfGroupGenerated.init,
        SchemeGroupVersion.init,
        SchemeBuilder.init,
        localSchemeBuilder.init,
        AddToScheme.init,
        map_DaemonSet.init,
        map_DaemonSetCondition.init,
        map_DaemonSetList.init,
        map_DaemonSetSpec.init,
        map_DaemonSetStatus.init,
        map_DaemonSetUpdateStrategy.init,
        map_Deployment.init,
        map_DeploymentCondition.init,
        map_DeploymentList.init,
        map_DeploymentRollback.init,
        map_DeploymentSpec.init,
        map_DeploymentStatus.init,
        map_DeploymentStrategy.init,
        map_HTTPIngressPath.init,
        map_HTTPIngressRuleValue.init,
        map_IPBlock.init,
        map_Ingress.init,
        map_IngressBackend.init,
        map_IngressList.init,
        map_IngressLoadBalancerIngress.init,
        map_IngressLoadBalancerStatus.init,
        map_IngressPortStatus.init,
        map_IngressRule.init,
        map_IngressRuleValue.init,
        map_IngressSpec.init,
        map_IngressStatus.init,
        map_IngressTLS.init,
        map_NetworkPolicy.init,
        map_NetworkPolicyEgressRule.init,
        map_NetworkPolicyIngressRule.init,
        map_NetworkPolicyList.init,
        map_NetworkPolicyPeer.init,
        map_NetworkPolicyPort.init,
        map_NetworkPolicySpec.init,
        map_ReplicaSet.init,
        map_ReplicaSetCondition.init,
        map_ReplicaSetList.init,
        map_ReplicaSetSpec.init,
        map_ReplicaSetStatus.init,
        map_RollbackConfig.init,
        map_RollingUpdateDaemonSet.init,
        map_RollingUpdateDeployment.init,
        map_Scale.init,
        map_ScaleSpec.init,
        map_ScaleStatus.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.api.extensions.v1beta1
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.api.extensions.v1beta1.Assumptions]

namespace k8s_io.api.extensions.v1beta1

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.extensions.v1beta1 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.extensions.v1beta1 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk ErrInvalidLengthGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrIntOverflowGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnexpectedEndOfGroupGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeGroupVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk localSchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk AddToScheme.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSet.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonSetUpdateStrategy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Deployment.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentRollback.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeploymentStrategy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HTTPIngressPath.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HTTPIngressRuleValue.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IPBlock.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Ingress.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressBackend.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressLoadBalancerIngress.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressLoadBalancerStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressPortStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressRule.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressRuleValue.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_IngressTLS.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NetworkPolicy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NetworkPolicyEgressRule.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NetworkPolicyIngressRule.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NetworkPolicyList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NetworkPolicyPeer.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NetworkPolicyPort.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NetworkPolicySpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSet.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicaSetStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RollbackConfig.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RollingUpdateDaemonSet.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RollingUpdateDeployment.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Scale.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScaleSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScaleStatus.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.extensions.v1beta1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.extensions.v1beta1 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.api.extensions.v1beta1

end init

end Perennial
