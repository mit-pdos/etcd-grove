/-
Package initialization of `k8s_io.kubernetes.pkg.apis.core.validation`
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
namespace k8s_io.kubernetes.pkg.apis.core.validation
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.kubernetes.pkg.apis.core.validation`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([pdPartitionErrorMsg.init,
        fileModeErrorMsg.init,
        emptyDirModeErrorMsg.init,
        BannedOwners.init,
        nodeDeclaredFeatureRegexp.init,
        iscsiInitiatorIqnRegex.init,
        iscsiInitiatorEuiRegex.init,
        iscsiInitiatorNaaRegex.init,
        allowedEphemeralContainerFields.init,
        validOS.init,
        ValidatePodName.init,
        ValidateServiceName.init,
        ValidateNodeName.init,
        ValidateNamespaceName.init,
        ValidateLimitRangeName.init,
        ValidateResourceQuotaName.init,
        ValidateSecretName.init,
        ValidateServiceAccountName.init,
        ValidateEndpointsName.init,
        ValidateClassName.init,
        ValidatePriorityClassName.init,
        ValidateResourceClaimName.init,
        ValidateResourceClaimTemplateName.init,
        ValidatePodGroupName.init,
        validVolumeDownwardAPIFieldPathExpressions.init,
        supportedHostPathTypes.init,
        allowedTemplateObjectMetaFields.init,
        ValidatePersistentVolumeName.init,
        supportedAccessModes.init,
        supportedReclaimPolicy.init,
        supportedVolumeModes.init,
        resizeStatusSet.init,
        supportedPortProtocols.init,
        validEnvDownwardAPIFieldPathExpressions.init,
        validContainerResourceFieldPathExpressions.init,
        validContainerResourceFieldPathPrefixesWithDownwardAPIHugePages.init,
        validContainerResourceDivisorForCPU.init,
        validContainerResourceDivisorForMemory.init,
        validContainerResourceDivisorForHugePages.init,
        validContainerResourceDivisorForEphemeralStorage.init,
        supportedBindMountOptions.init,
        supportedHTTPSchemes.init,
        supportedHTTPProtocols.init,
        supportedGRPCProbeModes.init,
        supportedStopSignalsLinux.init,
        supportedStopSignalsWindows.init,
        supportedPullPolicies.init,
        supportedResizeResources.init,
        supportedResizePolicies.init,
        supportedContainerRestartPolicies.init,
        supportedContainerRestartPolicyOperators.init,
        supportedContainerRestartRuleActions.init,
        supportedContainerRestartRuleActionsWithRestartAllContainers.init,
        validFSGroupChangePolicies.init,
        nodeFieldSelectorValidators.init,
        sysctlContainSlashRegexp.init,
        validSELinuxChangePolicies.init,
        updatablePodSpecFields.init,
        supportedSessionAffinityType.init,
        supportedServiceType.init,
        supportedServiceInternalTrafficPolicy.init,
        supportedServiceIPFamily.init,
        supportedServiceIPFamilyPolicy.init,
        validExternalTrafficPolicies.init,
        supportedTrafficDistribution.init,
        ValidateConfigMapName.init,
        ctrlRegex.init,
        validNetBiosRegex.init,
        dnsLabelFormat.init,
        dnsSubdomainFormat.init,
        validWindowsUserDomainDNSRegex.init,
        invalidUserNameCharsRegex.init,
        invalidUserNameDotsSpacesRegex.init,
        validLogStreams.init,
        supportedLoadBalancerIPMode.init,
        supportedScheduleActions.init,
        supportedPodTopologySpreadNodePolicies.init,
        betaToGALabel.init,
        validSupplementalGroupsPolicies.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.kubernetes.pkg.apis.core.validation
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.kubernetes.pkg.apis.core.validation.Assumptions]

namespace k8s_io.kubernetes.pkg.apis.core.validation

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.kubernetes.pkg.apis.core.validation get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.validation }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk pdPartitionErrorMsg.init (by mem_tac))
  wp_apply (opaqueInitsOk fileModeErrorMsg.init (by mem_tac))
  wp_apply (opaqueInitsOk emptyDirModeErrorMsg.init (by mem_tac))
  wp_apply (opaqueInitsOk BannedOwners.init (by mem_tac))
  wp_apply (opaqueInitsOk nodeDeclaredFeatureRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk iscsiInitiatorIqnRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk iscsiInitiatorEuiRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk iscsiInitiatorNaaRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk allowedEphemeralContainerFields.init (by mem_tac))
  wp_apply (opaqueInitsOk validOS.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidatePodName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateServiceName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateNodeName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateNamespaceName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateLimitRangeName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateResourceQuotaName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateSecretName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateServiceAccountName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateEndpointsName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateClassName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidatePriorityClassName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateResourceClaimName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateResourceClaimTemplateName.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidatePodGroupName.init (by mem_tac))
  wp_apply (opaqueInitsOk validVolumeDownwardAPIFieldPathExpressions.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedHostPathTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk allowedTemplateObjectMetaFields.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidatePersistentVolumeName.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedAccessModes.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedReclaimPolicy.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedVolumeModes.init (by mem_tac))
  wp_apply (opaqueInitsOk resizeStatusSet.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedPortProtocols.init (by mem_tac))
  wp_apply (opaqueInitsOk validEnvDownwardAPIFieldPathExpressions.init (by mem_tac))
  wp_apply (opaqueInitsOk validContainerResourceFieldPathExpressions.init (by mem_tac))
  wp_apply (opaqueInitsOk validContainerResourceFieldPathPrefixesWithDownwardAPIHugePages.init (by mem_tac))
  wp_apply (opaqueInitsOk validContainerResourceDivisorForCPU.init (by mem_tac))
  wp_apply (opaqueInitsOk validContainerResourceDivisorForMemory.init (by mem_tac))
  wp_apply (opaqueInitsOk validContainerResourceDivisorForHugePages.init (by mem_tac))
  wp_apply (opaqueInitsOk validContainerResourceDivisorForEphemeralStorage.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedBindMountOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedHTTPSchemes.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedHTTPProtocols.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedGRPCProbeModes.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedStopSignalsLinux.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedStopSignalsWindows.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedPullPolicies.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedResizeResources.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedResizePolicies.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedContainerRestartPolicies.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedContainerRestartPolicyOperators.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedContainerRestartRuleActions.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedContainerRestartRuleActionsWithRestartAllContainers.init (by mem_tac))
  wp_apply (opaqueInitsOk validFSGroupChangePolicies.init (by mem_tac))
  wp_apply (opaqueInitsOk nodeFieldSelectorValidators.init (by mem_tac))
  wp_apply (opaqueInitsOk sysctlContainSlashRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk validSELinuxChangePolicies.init (by mem_tac))
  wp_apply (opaqueInitsOk updatablePodSpecFields.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedSessionAffinityType.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedServiceType.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedServiceInternalTrafficPolicy.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedServiceIPFamily.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedServiceIPFamilyPolicy.init (by mem_tac))
  wp_apply (opaqueInitsOk validExternalTrafficPolicies.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedTrafficDistribution.init (by mem_tac))
  wp_apply (opaqueInitsOk ValidateConfigMapName.init (by mem_tac))
  wp_apply (opaqueInitsOk ctrlRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk validNetBiosRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk dnsLabelFormat.init (by mem_tac))
  wp_apply (opaqueInitsOk dnsSubdomainFormat.init (by mem_tac))
  wp_apply (opaqueInitsOk validWindowsUserDomainDNSRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk invalidUserNameCharsRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk invalidUserNameDotsSpacesRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk validLogStreams.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedLoadBalancerIPMode.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedScheduleActions.init (by mem_tac))
  wp_apply (opaqueInitsOk supportedPodTopologySpreadNodePolicies.init (by mem_tac))
  wp_apply (opaqueInitsOk betaToGALabel.init (by mem_tac))
  wp_apply (opaqueInitsOk validSupplementalGroupsPolicies.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.kubernetes.pkg.apis.core.validation get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.validation }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.kubernetes.pkg.apis.core.validation

end init

end Perennial
