/-
Lean-first (no Rocq counterpart).

Package initialization instances for the watch cache (`k8s.io/apiserver/pkg/storage/cacher`,
KEP-6404, `notes/kep-6404-plan.md`), its store (`cacher/store`, with bodies) and the packages they
import that have none yet (in import order): `isPkgInit` of a package includes `isPkgInit` of
everything it imports, so every one needs an instance. All but the store are names- or types-only
(`Code/k8s_io/**.toml`, project `k8s-apiserver` of `etc/goose.py`); the cacher's translated
functions are `watch_cache.go`'s. Every fact is `True` but the cacher's metrics package's
(`cacherMetricsInit`: `WatchCacheReadWait`, which the freshness wait observes, holds a histogram
vector of the labels `group` and `resource`, `kmetrics.vecLabels`). These are assumptions about package initialization
only once an `Init.lean` proves a package's `wp_initialize'` from them (`etc/gen-init.py`).
(2026-10-27, phase 4 of `notes/k8s-daemonset-plan.md`) `tools/cache` now translates the informer
layer with bodies, so it imports more: client-go's `rest` (its instance moved here from the model API
server's `apimodel/Base.lean`), `tools/pager`, `tools/cache/synctrack`, `k8s.io/utils/{buffer,ptr}`,
apimachinery's `util/{cache,diff,net}`, `apis/meta/{v1beta1,internalversion}` (names only but
pager, synctrack and buffer), and `math/rand` (`Proof/math/rand/Base.lean`); `consistencydetector`
and `watchlist` moved before `tools/cache`.
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.storage.cacher
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.k8s_io.component_base.metrics.Defs
public import Proof.math.rand.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace k8s_io.apiserver.pkg.storage.cacher

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The cacher's metrics package's fact (see the file header). -/
abbrev cacherMetricsInit : IProp GF :=
  iprop(∃ v : Loc, globalAddr k8s_io.apiserver.pkg.storage.cacher.metrics.WatchCacheReadWait ↦□ v ∗
    ⌜EtcdGrove.kmetrics.vecLabels v [go!"group", go!"resource"]⌝)

instance k8s_io_component_base_metrics_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.component_base.metrics :=
  define_is_pkg_init iprop(True)
instance k8s_io_component_base_metrics_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.component_base.metrics :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_cacher_metrics_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.metrics :=
  define_is_pkg_init cacherMetricsInit
instance k8s_io_apiserver_pkg_storage_cacher_metrics_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.metrics :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_cacher_consistency_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.consistency :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_cacher_consistency_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.consistency :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_cacher_key_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.key :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_cacher_key_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.key :=
  build_get_is_pkg_init_wf

-- (what `tools/cache`'s local half, translated with bodies since 2026-10-26, imports:
-- notes/k8s-clientgo-goose.md; `features` has translated initializers, `Init.lean` proves them)
instance k8s_io_apimachinery_pkg_util_naming_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.naming :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_naming_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.naming :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_version_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.version :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_version_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.version :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_features_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.features :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_features_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.features :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_sets_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_sets_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets :=
  build_get_is_pkg_init_wf

instance k8s_io_utils_trace_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.utils.trace :=
  define_is_pkg_init iprop(True)
instance k8s_io_utils_trace_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.trace :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_util_consistencydetector_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.util.consistencydetector :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_util_consistencydetector_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.util.consistencydetector :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_util_watchlist_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.util.watchlist :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_util_watchlist_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.util.watchlist :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_rest_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.rest :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_rest_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.rest :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_cache_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.cache :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_cache_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.cache :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_diff_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.diff :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_diff_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.diff :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_apis_meta_v1beta1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1beta1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_apis_meta_v1beta1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1beta1 :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_net_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.net :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_net_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.net :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_apis_meta_internalversion_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».internalversion :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_apis_meta_internalversion_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».internalversion :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_tools_pager_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.tools.pager :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_tools_pager_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.tools.pager :=
  build_get_is_pkg_init_wf

instance k8s_io_utils_ptr_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.utils.ptr :=
  define_is_pkg_init iprop(True)
instance k8s_io_utils_ptr_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.ptr :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_tools_cache_synctrack_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.tools.cache.synctrack :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_tools_cache_synctrack_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.tools.cache.synctrack :=
  build_get_is_pkg_init_wf

instance k8s_io_utils_buffer_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.utils.buffer :=
  define_is_pkg_init iprop(True)
instance k8s_io_utils_buffer_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.buffer :=
  build_get_is_pkg_init_wf

/-- client-go's `tools/cache` fact (phase 4 of the DaemonSet plan, 2026-10-27; `etc/gen-init.py`):
its error variables `ErrFIFOClosed` (`RealFIFO.Pop` returns it once closed) and
`errorStopRequested` (the reflector's watch returns it when stopped), untranslated `errors.New`
calls, hold some error each, for good. -/
abbrev k8sCacheInit : IProp GF :=
  iprop(∃ e1 e2 : GoInterface,
    globalAddr k8s_io.client_go.tools.cache.ErrFIFOClosed ↦□ e1 ∗
    globalAddr k8s_io.client_go.tools.cache.errorStopRequested ↦□ e2)

instance k8s_io_client_go_tools_cache_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.tools.cache :=
  define_is_pkg_init k8sCacheInit
instance k8s_io_client_go_tools_cache_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.tools.cache :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_cacher_store_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_cacher_store_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_cacher_progress_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.progress :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_cacher_progress_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.progress :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_cacher_delegator_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.delegator :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_cacher_delegator_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.delegator :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_cacher_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_cacher_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher :=
  build_get_is_pkg_init_wf

end init

end k8s_io.apiserver.pkg.storage.cacher
end Perennial
