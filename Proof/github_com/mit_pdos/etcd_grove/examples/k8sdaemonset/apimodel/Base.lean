/-
Package initialization instances of the model API server (`examples/k8sdaemonset/apimodel`; phase
3 of `notes/k8s-daemonset-plan.md`) and of the packages it imports that have none yet: client-go's
`kubernetes` and its 56 typed group packages (`rest`'s is in the watch cache's `Base.lean`,
which `tools/cache` needs since phase 4), `discovery`, the apply configurations of
`core`, `apps` and `autoscaling`, and the API groups `policy`, `authentication`, `autoscaling`
(all names only: the typed interfaces the model implements name them,
`notes/k8s-apimodel-goose.md`). Their facts are `True`.

The model's fact (`apimodelInit`): its error variables hold some error each (`errStorage`,
`errRead`) and `errAmbiguous` some string; the specs do not depend on their values. (Its
initialization, `errors.New` calls and a string, is not proved yet: no `Init.lean`.)
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.client_go.Base
public import Proof.math.rand.Base
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel
public import GeneratedProof.k8s_io.api.authentication.v1
public import GeneratedProof.k8s_io.api.autoscaling.v1
public import GeneratedProof.k8s_io.api.policy.v1
public import GeneratedProof.k8s_io.api.policy.v1beta1
public import GeneratedProof.k8s_io.client_go.applyconfigurations.apps.v1
public import GeneratedProof.k8s_io.client_go.applyconfigurations.autoscaling.v1
public import GeneratedProof.k8s_io.client_go.applyconfigurations.core.v1
public import GeneratedProof.k8s_io.client_go.discovery
public import GeneratedProof.k8s_io.client_go.kubernetes
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.admissionregistration.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.admissionregistration.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.admissionregistration.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.apiserverinternal.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.apps.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.apps.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.apps.v1beta2
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.authentication.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.authentication.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.authentication.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.authorization.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.authorization.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.authorization.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.autoscaling.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.autoscaling.v2
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.batch.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.batch.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.certificates.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.certificates.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.certificates.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.coordination.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.coordination.v1alpha2
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.coordination.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.core.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.discovery.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.discovery.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.events.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.events.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.extensions.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta2
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta3
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.lifecycle.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.networking.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.networking.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.node.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.node.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.node.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.policy.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.policy.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.rbac.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.rbac.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.rbac.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.resource.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.resource.v1alpha3
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.resource.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.resource.v1beta2
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.scheduling.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.scheduling.v1alpha3
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.scheduling.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.storage.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.storage.v1alpha1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.storage.v1beta1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.storagemigration.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.typed.storagemigration.v1beta1
public import GeneratedProof.k8s_io.client_go.rest

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance k8s_io_api_authentication_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.api.authentication.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_api_authentication_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.api.authentication.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_api_autoscaling_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.api.autoscaling.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_api_autoscaling_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.api.autoscaling.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_api_policy_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.api.policy.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_api_policy_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.api.policy.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_api_policy_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.api.policy.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_api_policy_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.api.policy.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_applyconfigurations_apps_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.applyconfigurations.apps.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_applyconfigurations_apps_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.applyconfigurations.apps.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_applyconfigurations_autoscaling_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.applyconfigurations.autoscaling.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_applyconfigurations_autoscaling_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.applyconfigurations.autoscaling.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_applyconfigurations_core_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.applyconfigurations.core.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_applyconfigurations_core_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.applyconfigurations.core.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_discovery_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.discovery :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_discovery_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.discovery :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_admissionregistration_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.admissionregistration.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_admissionregistration_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.admissionregistration.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_admissionregistration_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.admissionregistration.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_admissionregistration_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.admissionregistration.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_admissionregistration_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.admissionregistration.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_admissionregistration_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.admissionregistration.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_apiserverinternal_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apiserverinternal.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_apiserverinternal_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apiserverinternal.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_apps_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apps.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_apps_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apps.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_apps_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apps.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_apps_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apps.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_apps_v1beta2_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apps.v1beta2 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_apps_v1beta2_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.apps.v1beta2 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_authentication_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authentication.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_authentication_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authentication.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_authentication_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authentication.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_authentication_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authentication.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_authentication_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authentication.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_authentication_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authentication.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_authorization_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authorization.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_authorization_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authorization.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_authorization_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authorization.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_authorization_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authorization.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_authorization_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authorization.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_authorization_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.authorization.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_autoscaling_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.autoscaling.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_autoscaling_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.autoscaling.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_autoscaling_v2_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.autoscaling.v2 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_autoscaling_v2_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.autoscaling.v2 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_batch_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.batch.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_batch_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.batch.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_batch_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.batch.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_batch_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.batch.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_certificates_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.certificates.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_certificates_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.certificates.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_certificates_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.certificates.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_certificates_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.certificates.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_certificates_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.certificates.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_certificates_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.certificates.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_coordination_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.coordination.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_coordination_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.coordination.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_coordination_v1alpha2_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.coordination.v1alpha2 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_coordination_v1alpha2_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.coordination.v1alpha2 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_coordination_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.coordination.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_coordination_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.coordination.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_core_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.core.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_core_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.core.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_discovery_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.discovery.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_discovery_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.discovery.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_discovery_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.discovery.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_discovery_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.discovery.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_events_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.events.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_events_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.events.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_events_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.events.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_events_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.events.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_extensions_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.extensions.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_extensions_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.extensions.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1beta2_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta2 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1beta2_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta2 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1beta3_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta3 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_flowcontrol_v1beta3_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.flowcontrol.v1beta3 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_lifecycle_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.lifecycle.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_lifecycle_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.lifecycle.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_networking_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.networking.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_networking_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.networking.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_networking_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.networking.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_networking_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.networking.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_node_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.node.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_node_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.node.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_node_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.node.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_node_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.node.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_node_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.node.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_node_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.node.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_policy_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.policy.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_policy_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.policy.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_policy_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.policy.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_policy_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.policy.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_rbac_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.rbac.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_rbac_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.rbac.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_rbac_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.rbac.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_rbac_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.rbac.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_rbac_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.rbac.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_rbac_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.rbac.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_resource_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_resource_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_resource_v1alpha3_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1alpha3 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_resource_v1alpha3_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1alpha3 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_resource_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_resource_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_resource_v1beta2_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1beta2 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_resource_v1beta2_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.resource.v1beta2 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_scheduling_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.scheduling.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_scheduling_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.scheduling.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_scheduling_v1alpha3_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.scheduling.v1alpha3 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_scheduling_v1alpha3_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.scheduling.v1alpha3 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_scheduling_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.scheduling.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_scheduling_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.scheduling.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_storage_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storage.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_storage_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storage.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_storage_v1alpha1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storage.v1alpha1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_storage_v1alpha1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storage.v1alpha1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_storage_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storage.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_storage_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storage.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_storagemigration_v1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storagemigration.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_storagemigration_v1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storagemigration.v1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_typed_storagemigration_v1beta1_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storagemigration.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_typed_storagemigration_v1beta1_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.typed.storagemigration.v1beta1 :=
  build_get_is_pkg_init_wf
instance k8s_io_client_go_kubernetes_isPkgInit : IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_getIsPkgInitWf : GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes :=
  build_get_is_pkg_init_wf


namespace github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel

/-- The model's package fact: its error variables hold some value each (persistent). -/
abbrev apimodelInit : IProp GF :=
  iprop((∃ e : GoInterface, globalAddr errStorage ↦□ e) ∗
    (∃ e : GoInterface, globalAddr errRead ↦□ e) ∗
    (∃ s : GoString, globalAddr errAmbiguous ↦□ s))

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel :=
  define_is_pkg_init apimodelInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel :=
  build_get_is_pkg_init_wf

end github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel

end init

end Perennial
