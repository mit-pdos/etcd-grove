/-
Lean-first (no Rocq counterpart).

Package initialization instances for `k8s.io/apiserver/pkg/storage/etcd3` (the Kubernetes etcd3
store, `notes/k8s-etcd3-plan.md`), `k8s.io/apiserver/pkg/storage` and the packages they import
that have none yet (in import order): `isPkgInit` of a package includes `isPkgInit` of everything it imports, so
every one needs an instance. The k8s, otel, grpc and klog packages are translated with bodies
(`storage/etcd3`, `storage`) or names- or types-only (`Code/k8s_io/**.toml`, project
`k8s-apiserver` of `etc/goose.py`); the standard-library `encoding/base64`, `encoding/json`,
`iter` and `path` are not translated by Perennial (`notes/perennial-changes.md`; `encoding/base64`'s instance is in its own `Base.lean`). Every fact is
`True` but the store's metrics package's (`metricsInit`: `ErrTransactionConflict`, which
`txnError` returns for a failed comparison, holds some error) and `util/feature`'s
(`featureInit`: `DefaultFeatureGate` holds a gate whose `Enabled` answers some `bool`; the gate is
names-only, `component-base/featuregate`, and which features are on is the deployment's) and
`storage/feature`'s (`checkerInit`: `CheckClient` on `DefaultFeatureSupportChecker`'s checker,
which `etcd3.New` calls, returns; names-only, it starts goroutines that poll each endpoint's
`Status`, reads; stated as the call's own WP, the variable's load included, since the interface
type is axiomatized: its methods name `storage.Feature`, an alias, Goose's gap G1 of
`notes/k8s-etcd3-goose.md`) and `storage`'s (`storageInit`: `RequestWatchProgress` and
`tooLargeResourceVersionCauseMsg`, `NewTooLargeResourceVersionError`'s, hold strings). As in the cache's `Base.lean`, these
are assumptions about package initialization only once an `Init.lean` proves a package's
`wp_initialize'` from them (none does yet: the packages are not in `etc/gen-init.py`'s `ROOTS`).
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.storage.etcd3
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base
public import Perennial.Proof.strings.Base
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.encoding.base64.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace k8s_io.apiserver.pkg.storage.etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The store's metrics package's fact: `ErrTransactionConflict` (`errors.New` at init) holds some
error, for good. -/
abbrev metricsInit : IProp GF :=
  iprop(∃ e : GoInterface,
    globalAddr k8s_io.apiserver.pkg.storage.etcd3.metrics.ErrTransactionConflict ↦□ e)

/-- `util/feature`'s fact: `DefaultFeatureGate` holds a feature gate whose `Enabled` answers some
`bool` for any feature (see the file header). -/
abbrev featureInit : IProp GF :=
  iprop(∃ g : GoInterfaceOk,
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g ∗
    □ ∀ (f : val) (Φ : val → IProp GF), ▷ (∀ b : Bool, Φ #b) -∗
      WP (App (Val #(methods g.ty go!"Enabled" g.v)) (Val f)) {{ Φ }})

/-- `storage/feature`'s fact: `CheckClient` on `DefaultFeatureSupportChecker`'s checker returns
(see the file header). -/
abbrev checkerInit : IProp GF :=
  iprop(□ ∀ (ctx cl f : val) (Φ : val → IProp GF), ▷ Φ #() -∗
    WP (App (App (App (App (Val (GoInstruction (MethodResolve
        k8s_io.apiserver.pkg.storage.feature.FeatureSupportChecker.ty go!"CheckClient")))
        (App (Val (GoInstruction (GoLoad k8s_io.apiserver.pkg.storage.feature.FeatureSupportChecker.ty)))
          (Val #(globalAddr k8s_io.apiserver.pkg.storage.feature.DefaultFeatureSupportChecker))))
        (Val ctx)) (Val cl)) (Val f)) {{ Φ }})

/-- `storage`'s fact: `RequestWatchProgress` and `tooLargeResourceVersionCauseMsg` hold strings
(see the file header). -/
abbrev storageInit : IProp GF :=
  iprop(∃ rw tl : GoString, globalAddr k8s_io.apiserver.pkg.storage.RequestWatchProgress ↦□ rw ∗
    globalAddr k8s_io.apiserver.pkg.storage.tooLargeResourceVersionCauseMsg ↦□ tl)

instance k8s_io_apimachinery_pkg_runtime_schema_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime.schema :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_runtime_schema_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime.schema :=
  build_get_is_pkg_init_wf

instance k8s_io_klog_v2_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.klog.v2 :=
  define_is_pkg_init iprop(True)
instance k8s_io_klog_v2_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.klog.v2 :=
  build_get_is_pkg_init_wf

instance k8s_io_utils_clock_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.utils.clock :=
  define_is_pkg_init iprop(True)
instance k8s_io_utils_clock_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.clock :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_wait_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_wait_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_features_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.features :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_features_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.features :=
  build_get_is_pkg_init_wf

instance k8s_io_component_base_featuregate_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.component_base.featuregate :=
  define_is_pkg_init iprop(True)
instance k8s_io_component_base_featuregate_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.component_base.featuregate :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_util_feature_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.util.feature :=
  define_is_pkg_init featureInit
instance k8s_io_apiserver_pkg_util_feature_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.util.feature :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_types_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.types :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_types_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.types :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_conversion_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_conversion_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_runtime_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_runtime_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_apis_meta_v1_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1 :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_apis_meta_v1_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1 :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_api_errors_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_api_errors_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_errors_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_errors_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_api_meta_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_api_meta_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.«meta» :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_validation_field_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_validation_field_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field :=
  build_get_is_pkg_init_wf

-- `encoding/base64`: its instance is in `Proof/encoding/base64/Base.lean` (the auth plan's E2x,
-- 2026-10-26: the server reads its `StdEncoding`)

-- `encoding/json`'s instance: `etcdserver/apply/Base.lean` (D43 M4, 2026-10-26: membership's).

instance path_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.path :=
  define_is_pkg_init iprop(True)
instance path_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.path :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_fields_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.fields :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_fields_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.fields :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_labels_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_labels_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.labels :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_watch_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.watch :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_watch_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.watch :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_sharding_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.sharding :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_sharding_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.sharding :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_api_validate_content_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.validate.content :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_api_validate_content_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.validate.content :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage :=
  define_is_pkg_init storageInit
instance k8s_io_apiserver_pkg_storage_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_value_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.value :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_value_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.value :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_endpoints_request_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.endpoints.request :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_endpoints_request_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.endpoints.request :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_util_runtime_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.runtime :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_util_runtime_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.runtime :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_etcd3_metrics_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics :=
  define_is_pkg_init metricsInit
instance k8s_io_apiserver_pkg_storage_etcd3_metrics_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics :=
  build_get_is_pkg_init_wf

instance google_golang_org_grpc_grpclog_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.grpclog :=
  define_is_pkg_init iprop(True)
instance google_golang_org_grpc_grpclog_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.grpclog :=
  build_get_is_pkg_init_wf

instance iter_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.iter :=
  define_is_pkg_init iprop(True)
instance iter_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.iter :=
  build_get_is_pkg_init_wf

instance go_opentelemetry_io_otel_attribute_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» :=
  define_is_pkg_init iprop(True)
instance go_opentelemetry_io_otel_attribute_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» :=
  build_get_is_pkg_init_wf

instance k8s_io_apimachinery_pkg_apis_meta_v1_unstructured_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured :=
  define_is_pkg_init iprop(True)
instance k8s_io_apimachinery_pkg_apis_meta_v1_unstructured_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1.unstructured :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_audit_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.audit :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_audit_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.audit :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_feature_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.feature :=
  define_is_pkg_init checkerInit
instance k8s_io_apiserver_pkg_storage_feature_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.feature :=
  build_get_is_pkg_init_wf

instance k8s_io_component_base_tracing_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.component_base.tracing :=
  define_is_pkg_init iprop(True)
instance k8s_io_component_base_tracing_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.component_base.tracing :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_util_flowcontrol_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.util.flowcontrol :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_util_flowcontrol_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.util.flowcontrol :=
  build_get_is_pkg_init_wf

instance k8s_io_apiserver_pkg_storage_etcd3_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 :=
  define_is_pkg_init iprop(True)
instance k8s_io_apiserver_pkg_storage_etcd3_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 :=
  build_get_is_pkg_init_wf

end init

end k8s_io.apiserver.pkg.storage.etcd3
end Perennial
