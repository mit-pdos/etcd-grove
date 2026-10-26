/-
Lean-first (no Rocq counterpart).

Package initialization instances for client-go's leaf libraries (`notes/k8s-clientgo-goose.md`;
the DaemonSet controller, `notes/k8s-daemonset-plan.md`): `util/workqueue`, `util/consistency`,
`util/retry`, the listers (`listers`, `listers/{apps,core}/v1`), and the
packages they import that have none yet (in import order): apimachinery's `util/resourceversion`,
`api/resource`, `util/intstr` and the API types `k8s.io/api/{core,apps}/v1`. (`tools/cache`,
`features` and the packages `tools/cache` imports have theirs in the watch cache's `Base.lean`,
which the cache shares with KEP-6404.) Every fact is `True`. These are assumptions about package
initialization only once an `Init.lean` proves a package's `wp_initialize'` from them
(`etc/gen-init.py`). `util/flowcontrol` has none yet: it imports `math/rand`, whose instance is in
the gRPC server's `v3rpc/Base.lean` (moving it to a module of its own rebuilds the server's
proofs; do it when a proof needs `flowcontrol`'s initialization).
-/
module

public import GeneratedProof.k8s_io.client_go.util.workqueue
public import GeneratedProof.k8s_io.client_go.util.consistency
public import GeneratedProof.k8s_io.client_go.util.retry
public import GeneratedProof.k8s_io.client_go.listers.apps.v1
public import GeneratedProof.k8s_io.client_go.listers.core.v1
public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace k8s_io.client_go

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance k8s_io_apimachinery_pkg_util_resourceversion_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.resourceversion :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_resourceversion_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.resourceversion :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_util_consistency_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.util.consistency :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_util_consistency_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.util.consistency :=
  build_get_is_pkg_init_wf

/-- The work queue's package fact (2026-10-26, its proofs: `Proof/k8s_io/client_go/util/workqueue/`):
`globalMetricsProvider` holds the no-op provider, read-only for good. Its initializer stores
`noopMetricsProvider{}`; `SetProvider` would replace it, and has no spec (a program that sets a
global provider is outside the queue's specs, which cover queues without metrics). -/
def workqueueInit : IProp GF :=
  iprop(globalAddr k8s_io.client_go.util.workqueue.globalMetricsProvider ↦□
    (interface.mkOk k8s_io.client_go.util.workqueue.noopMetricsProvider.ty
      #(k8s_io.client_go.util.workqueue.noopMetricsProvider.mk) :
      k8s_io.client_go.util.workqueue.MetricsProvider))

instance k8s_io_client_go_util_workqueue_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.util.workqueue :=
  define_is_pkg_init workqueueInit
instance k8s_io_client_go_util_workqueue_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.util.workqueue :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_util_retry_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.util.retry :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_util_retry_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.util.retry :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_api_resource_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.resource :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_api_resource_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.resource :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_intstr_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.intstr :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_intstr_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.intstr :=
  build_get_is_pkg_init_wf

instance k8s_io_api_core_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.api.core.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_api_core_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.api.core.v1 :=
  build_get_is_pkg_init_wf

instance k8s_io_api_apps_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.api.apps.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_api_apps_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.api.apps.v1 :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_listers_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.listers :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_listers_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.listers :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_listers_apps_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_listers_apps_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_listers_core_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.listers.core.v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_listers_core_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.listers.core.v1 :=
  build_get_is_pkg_init_wf

end init

end k8s_io.client_go
end Perennial
