/-
Lean-first (no Rocq counterpart).

Package initialization instances for the DaemonSet controller's packages (phase 5 of
`notes/k8s-daemonset-plan.md`; project `k8s-daemonset`, `notes/k8s-daemonset-goose.md`):
`k8s.io/kubernetes/pkg/controller/daemon`, its `util` and `metrics`, `pkg/controller`,
`pkg/api/v1/pod`, `pkg/apis/core/v1/helper`, `pkg/util/{labels,hash}`, `pkg/features`,
component-helpers' `scheduling/corev1{,/nodeaffinity}`, and the packages they import that have
none yet (client-go's informers, `tools/record`, `kubernetes/scheme`, `util/flowcontrol`,
apimachinery's `equality`, `util/json`, `strategicpatch`, ..., the names-only packages of
`k8s.io/kubernetes` the controller names). Every fact is `True`: assumptions about package
initialization only once an `Init.lean` proves a package's `wp_initialize'` from them
(`etc/gen-init.py`; phase 6, the closed theorem, chains `dsmain`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Base
public import GeneratedProof.k8s_io.apimachinery.pkg.api.equality
public import GeneratedProof.k8s_io.client_go.informers.internalinterfaces
public import GeneratedProof.k8s_io.client_go.informers.apps.v1
public import GeneratedProof.k8s_io.client_go.informers.core.v1
public import GeneratedProof.k8s_io.client_go.kubernetes.scheme
public import GeneratedProof.k8s_io.client_go.tools.record
public import GeneratedProof.k8s_io.client_go.util.flowcontrol
public import GeneratedProof.k8s_io.apimachinery.pkg.selection
public import GeneratedProof.k8s_io.component_helpers.scheduling.corev1.nodeaffinity
public import GeneratedProof.k8s_io.component_helpers.scheduling.corev1
public import GeneratedProof.k8s_io.apiextensions_apiserver.pkg.features
public import GeneratedProof.k8s_io.component_base.zpages.features
public import GeneratedProof.k8s_io.controller_manager.pkg.features
public import GeneratedProof.k8s_io.kubernetes.pkg.features
public import GeneratedProof.k8s_io.kubernetes.pkg.api.v1.pod
public import GeneratedProof.hash.fnv
public import GeneratedProof.k8s_io.apimachinery.pkg.util.rand
public import GeneratedProof.k8s_io.apimachinery.pkg.util.strategicpatch
public import GeneratedProof.k8s_io.kubernetes.pkg.apis.core.helper
public import GeneratedProof.k8s_io.kubernetes.pkg.apis.core.install
public import GeneratedProof.k8s_io.kubernetes.pkg.apis.core.validation
public import GeneratedProof.k8s_io.utils.dump
public import GeneratedProof.k8s_io.kubernetes.pkg.util.hash
public import GeneratedProof.k8s_io.kubernetes.pkg.util.taints
public import GeneratedProof.k8s_io.kubernetes.pkg.controller
public import GeneratedProof.k8s_io.component_base.metrics.legacyregistry
public import GeneratedProof.k8s_io.kubernetes.pkg.controller.daemon.metrics
public import GeneratedProof.k8s_io.api.extensions.v1beta1
public import GeneratedProof.k8s_io.apimachinery.pkg.util.validation
public import GeneratedProof.k8s_io.kubernetes.pkg.apis.core.v1.helper
public import GeneratedProof.k8s_io.kubernetes.pkg.controller.daemon.util
public import GeneratedProof.k8s_io.apimachinery.pkg.util.json
public import GeneratedProof.k8s_io.kubernetes.pkg.util.labels
public import GeneratedProof.k8s_io.kubernetes.pkg.controller.daemon

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace k8s_io.kubernetes

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance k8s_io_apimachinery_pkg_api_equality_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.equality :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_api_equality_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.equality :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_informers_internalinterfaces_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.informers.internalinterfaces :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_informers_internalinterfaces_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.informers.internalinterfaces :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_informers_apps_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.informers.apps.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_informers_apps_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.informers.apps.v1 :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_informers_core_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.informers.core.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_informers_core_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.informers.core.v1 :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_kubernetes_scheme_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.kubernetes.scheme :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_kubernetes_scheme_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.kubernetes.scheme :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_tools_record_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.tools.record :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_tools_record_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.tools.record :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_util_flowcontrol_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.util.flowcontrol :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_util_flowcontrol_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.util.flowcontrol :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_selection_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.selection :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_selection_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.selection :=
  build_get_is_pkg_init_wf

instance k8s_io_component_helpers_scheduling_corev1_nodeaffinity_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity :=
  define_is_pkg_init iprop(True)
instance k8s_io_component_helpers_scheduling_corev1_nodeaffinity_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1.nodeaffinity :=
  build_get_is_pkg_init_wf

instance k8s_io_component_helpers_scheduling_corev1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_component_helpers_scheduling_corev1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.component_helpers.scheduling.corev1 :=
  build_get_is_pkg_init_wf

instance k8s_io_apiextensions_apiserver_pkg_features_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiextensions_apiserver.pkg.features :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiextensions_apiserver_pkg_features_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiextensions_apiserver.pkg.features :=
  build_get_is_pkg_init_wf

instance k8s_io_component_base_zpages_features_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.component_base.zpages.features :=
  define_is_pkg_init iprop(True)
instance k8s_io_component_base_zpages_features_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.component_base.zpages.features :=
  build_get_is_pkg_init_wf

instance k8s_io_controller_manager_pkg_features_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.controller_manager.pkg.features :=
  define_is_pkg_init iprop(True)
instance k8s_io_controller_manager_pkg_features_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.controller_manager.pkg.features :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_features_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.features :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_features_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.features :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_api_v1_pod_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_api_v1_pod_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.api.v1.pod :=
  build_get_is_pkg_init_wf

instance hash_fnv_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.hash.fnv :=
  define_is_pkg_init iprop(True)
instance hash_fnv_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.hash.fnv :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_rand_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.rand :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_rand_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.rand :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_strategicpatch_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.strategicpatch :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_strategicpatch_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.strategicpatch :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_apis_core_helper_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.helper :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_apis_core_helper_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.helper :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_apis_core_install_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.install :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_apis_core_install_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.install :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_apis_core_validation_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.validation :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_apis_core_validation_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.validation :=
  build_get_is_pkg_init_wf

instance k8s_io_utils_dump_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.utils.dump :=
  define_is_pkg_init iprop(True)
instance k8s_io_utils_dump_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.dump :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_util_hash_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.util.hash :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_util_hash_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.util.hash :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_util_taints_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.util.taints :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_util_taints_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.util.taints :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_controller_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_controller_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller :=
  build_get_is_pkg_init_wf

instance k8s_io_component_base_metrics_legacyregistry_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.component_base.metrics.legacyregistry :=
  define_is_pkg_init iprop(True)
instance k8s_io_component_base_metrics_legacyregistry_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.component_base.metrics.legacyregistry :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_controller_daemon_metrics_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_controller_daemon_metrics_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.metrics :=
  build_get_is_pkg_init_wf

instance k8s_io_api_extensions_v1beta1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.api.extensions.v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_api_extensions_v1beta1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.api.extensions.v1beta1 :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_validation_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_validation_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_apis_core_v1_helper_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.v1.helper :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_apis_core_v1_helper_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.apis.core.v1.helper :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_controller_daemon_util_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_controller_daemon_util_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon.util :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_json_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.json :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_json_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.json :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_util_labels_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.util.labels :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_util_labels_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.util.labels :=
  build_get_is_pkg_init_wf

instance k8s_io_kubernetes_pkg_controller_daemon_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon :=
  define_is_pkg_init iprop(True)
instance k8s_io_kubernetes_pkg_controller_daemon_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon :=
  build_get_is_pkg_init_wf

end init

end k8s_io.kubernetes
end Perennial
