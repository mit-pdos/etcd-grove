/-
Package initialization of `k8s_io.api.core.v1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.k8s_io.client_go.Base
public import Proof.k8s_io.apimachinery.pkg.api.resource.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init
public import Proof.k8s_io.apimachinery.pkg.util.intstr.Init
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
namespace k8s_io.api.core.v1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.api.core.v1`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrInvalidLengthGenerated.init,
        ErrIntOverflowGenerated.init,
        ErrUnexpectedEndOfGroupGenerated.init,
        SchemeGroupVersion.init,
        SchemeBuilder.init,
        AddToScheme.init,
        «_».init,
        map_AWSElasticBlockStoreVolumeSource.init,
        map_Affinity.init,
        map_AppArmorProfile.init,
        map_AttachedVolume.init,
        map_AvoidPods.init,
        map_AzureDiskVolumeSource.init,
        map_AzureFilePersistentVolumeSource.init,
        map_AzureFileVolumeSource.init,
        map_Binding.init,
        map_CSIPersistentVolumeSource.init,
        map_CSIVolumeSource.init,
        map_Capabilities.init,
        map_CephFSPersistentVolumeSource.init,
        map_CephFSVolumeSource.init,
        map_CinderPersistentVolumeSource.init,
        map_CinderVolumeSource.init,
        map_ClientIPConfig.init,
        map_ClusterTrustBundleProjection.init,
        map_ComponentCondition.init,
        map_ComponentStatus.init,
        map_ComponentStatusList.init,
        map_ConfigMap.init,
        map_ConfigMapEnvSource.init,
        map_ConfigMapKeySelector.init,
        map_ConfigMapList.init,
        map_ConfigMapNodeConfigSource.init,
        map_ConfigMapProjection.init,
        map_ConfigMapVolumeSource.init,
        map_Container.init,
        map_ContainerExtendedResourceRequest.init,
        map_ContainerImage.init,
        map_ContainerPort.init,
        map_ContainerResizePolicy.init,
        map_ContainerRestartRule.init,
        map_ContainerRestartRuleOnExitCodes.init,
        map_ContainerState.init,
        map_ContainerStateRunning.init,
        map_ContainerStateTerminated.init,
        map_ContainerStateWaiting.init,
        map_ContainerStatus.init,
        map_ContainerUser.init,
        map_DaemonEndpoint.init,
        map_DownwardAPIProjection.init,
        map_DownwardAPIVolumeFile.init,
        map_DownwardAPIVolumeSource.init,
        map_EmptyDirVolumeSource.init,
        map_EndpointAddress.init,
        map_EndpointPort.init,
        map_EndpointSubset.init,
        map_Endpoints.init,
        map_EndpointsList.init,
        map_EnvFromSource.init,
        map_EnvVar.init,
        map_EnvVarSource.init,
        map_EphemeralContainer.init,
        map_EphemeralContainerCommon.init,
        map_EphemeralVolumeSource.init,
        map_Event.init,
        map_EventList.init,
        map_EventSeries.init,
        map_EventSource.init,
        map_EvictionResponder.init,
        map_ExecAction.init,
        map_FCVolumeSource.init,
        map_FileKeySelector.init,
        map_FlexPersistentVolumeSource.init,
        map_FlexVolumeSource.init,
        map_FlockerVolumeSource.init,
        map_GCEPersistentDiskVolumeSource.init,
        map_GRPCAction.init,
        map_GitRepoVolumeSource.init,
        map_GlusterfsPersistentVolumeSource.init,
        map_GlusterfsVolumeSource.init,
        map_HTTPGetAction.init,
        map_HTTPHeader.init,
        map_HostAlias.init,
        map_HostIP.init,
        map_HostPathVolumeSource.init,
        map_ISCSIPersistentVolumeSource.init,
        map_ISCSIVolumeSource.init,
        map_ImageVolumeSource.init,
        map_ImageVolumeStatus.init,
        map_KeyToPath.init,
        map_Lifecycle.init,
        map_LifecycleHandler.init,
        map_LimitRange.init,
        map_LimitRangeItem.init,
        map_LimitRangeList.init,
        map_LimitRangeSpec.init,
        map_LinuxContainerUser.init,
        map_LoadBalancerIngress.init,
        map_LoadBalancerStatus.init,
        map_LocalObjectReference.init,
        map_LocalVolumeSource.init,
        map_ModifyVolumeStatus.init,
        map_NFSVolumeSource.init,
        map_Namespace.init,
        map_NamespaceCondition.init,
        map_NamespaceList.init,
        map_NamespaceSpec.init,
        map_NamespaceStatus.init,
        map_Node.init,
        map_NodeAddress.init,
        map_NodeAffinity.init,
        map_NodeAllocatableMappedResources.init,
        map_NodeAllocatableOverheadResources.init,
        map_NodeAllocatableResourceClaimStatus.init,
        map_NodeCondition.init,
        map_NodeConfigSource.init,
        map_NodeConfigStatus.init,
        map_NodeDaemonEndpoints.init,
        map_NodeFeatures.init,
        map_NodeList.init,
        map_NodePodPreemptionPolicy.init,
        map_NodeProxyOptions.init,
        map_NodeRuntimeHandler.init,
        map_NodeRuntimeHandlerFeatures.init,
        map_NodeSelector.init,
        map_NodeSelectorRequirement.init,
        map_NodeSelectorTerm.init,
        map_NodeSpec.init,
        map_NodeStatus.init,
        map_NodeSwapStatus.init,
        map_NodeSystemInfo.init,
        map_ObjectFieldSelector.init,
        map_ObjectReference.init,
        map_PersistentVolume.init,
        map_PersistentVolumeClaim.init,
        map_PersistentVolumeClaimCondition.init,
        map_PersistentVolumeClaimList.init,
        map_PersistentVolumeClaimSpec.init,
        map_PersistentVolumeClaimStatus.init,
        map_PersistentVolumeClaimTemplate.init,
        map_PersistentVolumeClaimVolumeSource.init,
        map_PersistentVolumeList.init,
        map_PersistentVolumeSource.init,
        map_PersistentVolumeSpec.init,
        map_PersistentVolumeStatus.init,
        map_PhotonPersistentDiskVolumeSource.init,
        map_Pod.init,
        map_PodAffinity.init,
        map_PodAffinityTerm.init,
        map_PodAntiAffinity.init,
        map_PodAttachOptions.init,
        map_PodCertificateProjection.init,
        map_PodCondition.init,
        map_PodDNSConfig.init,
        map_PodDNSConfigOption.init,
        map_PodExecOptions.init,
        map_PodExtendedResourceClaimStatus.init,
        map_PodIP.init,
        map_PodList.init,
        map_PodLogOptions.init,
        map_PodOS.init,
        map_PodPortForwardOptions.init,
        map_PodProxyOptions.init,
        map_PodReadinessGate.init,
        map_PodResourceClaim.init,
        map_PodResourceClaimStatus.init,
        map_PodSchedulingGate.init,
        map_PodSchedulingGroup.init,
        map_PodSecurityContext.init,
        map_PodSignature.init,
        map_PodSpec.init,
        map_PodStatus.init,
        map_PodTemplate.init,
        map_PodTemplateList.init,
        map_PodTemplateSpec.init,
        map_PodVolumeHealth.init,
        map_PortStatus.init,
        map_PortworxVolumeSource.init,
        map_Preconditions.init,
        map_PreferAvoidPodsEntry.init,
        map_PreferredSchedulingTerm.init,
        map_Probe.init,
        map_ProbeHandler.init,
        map_ProjectedVolumeSource.init,
        map_QuobyteVolumeSource.init,
        map_RBDPersistentVolumeSource.init,
        map_RBDVolumeSource.init,
        map_RangeAllocation.init,
        map_ReplicationController.init,
        map_ReplicationControllerCondition.init,
        map_ReplicationControllerList.init,
        map_ReplicationControllerSpec.init,
        map_ReplicationControllerStatus.init,
        map_ResourceClaim.init,
        map_ResourceFieldSelector.init,
        map_ResourceHealth.init,
        map_ResourceQuota.init,
        map_ResourceQuotaList.init,
        map_ResourceQuotaSpec.init,
        map_ResourceQuotaStatus.init,
        map_ResourceRequirements.init,
        map_ResourceStatus.init,
        map_SELinuxOptions.init,
        map_ScaleIOPersistentVolumeSource.init,
        map_ScaleIOVolumeSource.init,
        map_ScopeSelector.init,
        map_ScopedResourceSelectorRequirement.init,
        map_SeccompProfile.init,
        map_Secret.init,
        map_SecretEnvSource.init,
        map_SecretKeySelector.init,
        map_SecretList.init,
        map_SecretProjection.init,
        map_SecretReference.init,
        map_SecretVolumeSource.init,
        map_SecurityContext.init,
        map_SerializedReference.init,
        map_Service.init,
        map_ServiceAccount.init,
        map_ServiceAccountList.init,
        map_ServiceAccountTokenProjection.init,
        map_ServiceList.init,
        map_ServicePort.init,
        map_ServiceProxyOptions.init,
        map_ServiceSpec.init,
        map_ServiceStatus.init,
        map_SessionAffinityConfig.init,
        map_SleepAction.init,
        map_StorageOSPersistentVolumeSource.init,
        map_StorageOSVolumeSource.init,
        map_Sysctl.init,
        map_TCPSocketAction.init,
        map_Taint.init,
        map_Toleration.init,
        map_TopologySelectorLabelRequirement.init,
        map_TopologySelectorTerm.init,
        map_TopologySpreadConstraint.init,
        map_TypedLocalObjectReference.init,
        map_TypedObjectReference.init,
        map_Volume.init,
        map_VolumeDevice.init,
        map_VolumeHealthCondition.init,
        map_VolumeHealthStatus.init,
        map_VolumeMount.init,
        map_VolumeMountStatus.init,
        map_VolumeNodeAffinity.init,
        map_VolumeProjection.init,
        map_VolumeResourceRequirements.init,
        map_VolumeSource.init,
        map_VolumeStatus.init,
        map_VsphereVirtualDiskVolumeSource.init,
        map_WeightedPodAffinityTerm.init,
        map_WindowsSecurityContextOptions.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.api.core.v1
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.api.core.v1.Assumptions]

namespace k8s_io.api.core.v1

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.core.v1 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.core.v1 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.util.intstr.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.types.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.api.resource.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk ErrInvalidLengthGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrIntOverflowGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnexpectedEndOfGroupGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeGroupVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk AddToScheme.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk map_AWSElasticBlockStoreVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Affinity.init (by mem_tac))
  wp_apply (opaqueInitsOk map_AppArmorProfile.init (by mem_tac))
  wp_apply (opaqueInitsOk map_AttachedVolume.init (by mem_tac))
  wp_apply (opaqueInitsOk map_AvoidPods.init (by mem_tac))
  wp_apply (opaqueInitsOk map_AzureDiskVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_AzureFilePersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_AzureFileVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Binding.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CSIPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CSIVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Capabilities.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CephFSPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CephFSVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CinderPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CinderVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ClientIPConfig.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ClusterTrustBundleProjection.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ComponentCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ComponentStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ComponentStatusList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ConfigMap.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ConfigMapEnvSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ConfigMapKeySelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ConfigMapList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ConfigMapNodeConfigSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ConfigMapProjection.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ConfigMapVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Container.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerExtendedResourceRequest.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerImage.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerPort.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerResizePolicy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerRestartRule.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerRestartRuleOnExitCodes.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerState.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerStateRunning.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerStateTerminated.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerStateWaiting.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ContainerUser.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DaemonEndpoint.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DownwardAPIProjection.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DownwardAPIVolumeFile.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DownwardAPIVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EmptyDirVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EndpointAddress.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EndpointPort.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EndpointSubset.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Endpoints.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EndpointsList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EnvFromSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EnvVar.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EnvVarSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EphemeralContainer.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EphemeralContainerCommon.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EphemeralVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Event.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EventList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EventSeries.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EventSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_EvictionResponder.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ExecAction.init (by mem_tac))
  wp_apply (opaqueInitsOk map_FCVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_FileKeySelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_FlexPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_FlexVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_FlockerVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_GCEPersistentDiskVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_GRPCAction.init (by mem_tac))
  wp_apply (opaqueInitsOk map_GitRepoVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_GlusterfsPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_GlusterfsVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HTTPGetAction.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HTTPHeader.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HostAlias.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HostIP.init (by mem_tac))
  wp_apply (opaqueInitsOk map_HostPathVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ISCSIPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ISCSIVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ImageVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ImageVolumeStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_KeyToPath.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Lifecycle.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LifecycleHandler.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LimitRange.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LimitRangeItem.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LimitRangeList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LimitRangeSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LinuxContainerUser.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LoadBalancerIngress.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LoadBalancerStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LocalObjectReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LocalVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ModifyVolumeStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NFSVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Namespace.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NamespaceCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NamespaceList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NamespaceSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NamespaceStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Node.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeAddress.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeAffinity.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeAllocatableMappedResources.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeAllocatableOverheadResources.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeAllocatableResourceClaimStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeConfigSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeConfigStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeDaemonEndpoints.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeFeatures.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodePodPreemptionPolicy.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeProxyOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeRuntimeHandler.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeRuntimeHandlerFeatures.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeSelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeSelectorRequirement.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeSelectorTerm.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeSwapStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_NodeSystemInfo.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ObjectFieldSelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ObjectReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolume.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeClaim.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeClaimCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeClaimList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeClaimSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeClaimStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeClaimTemplate.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeClaimVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PersistentVolumeStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PhotonPersistentDiskVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Pod.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodAffinity.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodAffinityTerm.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodAntiAffinity.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodAttachOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodCertificateProjection.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodDNSConfig.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodDNSConfigOption.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodExecOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodExtendedResourceClaimStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodIP.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodLogOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodOS.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodPortForwardOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodProxyOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodReadinessGate.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodResourceClaim.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodResourceClaimStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodSchedulingGate.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodSchedulingGroup.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodSecurityContext.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodSignature.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodTemplate.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodTemplateList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodTemplateSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PodVolumeHealth.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PortStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PortworxVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Preconditions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PreferAvoidPodsEntry.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PreferredSchedulingTerm.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Probe.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ProbeHandler.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ProjectedVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_QuobyteVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RBDPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RBDVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RangeAllocation.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicationController.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicationControllerCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicationControllerList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicationControllerSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ReplicationControllerStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceClaim.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceFieldSelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceHealth.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceQuota.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceQuotaList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceQuotaSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceQuotaStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceRequirements.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ResourceStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SELinuxOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScaleIOPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScaleIOVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScopeSelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ScopedResourceSelectorRequirement.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SeccompProfile.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Secret.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SecretEnvSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SecretKeySelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SecretList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SecretProjection.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SecretReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SecretVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SecurityContext.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SerializedReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Service.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServiceAccount.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServiceAccountList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServiceAccountTokenProjection.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServiceList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServicePort.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServiceProxyOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServiceSpec.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServiceStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SessionAffinityConfig.init (by mem_tac))
  wp_apply (opaqueInitsOk map_SleepAction.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StorageOSPersistentVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StorageOSVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Sysctl.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TCPSocketAction.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Taint.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Toleration.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TopologySelectorLabelRequirement.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TopologySelectorTerm.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TopologySpreadConstraint.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TypedLocalObjectReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TypedObjectReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Volume.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeDevice.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeHealthCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeHealthStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeMount.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeMountStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeNodeAffinity.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeProjection.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeResourceRequirements.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VolumeStatus.init (by mem_tac))
  wp_apply (opaqueInitsOk map_VsphereVirtualDiskVolumeSource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_WeightedPodAffinityTerm.init (by mem_tac))
  wp_apply (opaqueInitsOk map_WindowsSecurityContextOptions.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.api.core.v1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.api.core.v1 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.api.core.v1

end init

end Perennial
