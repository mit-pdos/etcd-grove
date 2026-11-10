/-
Lean-first (no Rocq counterpart).

Package initialization instances for `k8s.io/apiserver/pkg/storage/etcd3` (the Kubernetes etcd3
store, `notes/k8s-etcd3-plan.md`), `k8s.io/apiserver/pkg/storage` and the packages they import
that have none yet (in import order): `isPkgInit` of a package includes `isPkgInit` of everything it imports, so
every one needs an instance. The k8s, otel, grpc and klog packages are translated with bodies
(`storage/etcd3`, `storage`) or names- or types-only (`Code/k8s_io/**.toml`, project
`k8s-apiserver` of `etc/goose.py`); the standard-library `encoding/base64`, `encoding/json`,
`iter` and `path` are not translated by Perennial (`notes/perennial-changes.md`; `encoding/base64`'s instance is in its own `Base.lean`). Every fact is
`True` but `etcd3`'s own (the compactor registry, `registryFact`, `RegistryDefs.lean`), the store's metrics package's (`metricsInit`: `ErrTransactionConflict`, which
`txnError` returns for a failed comparison, holds `errors.New("transaction conflict")`) and `util/feature`'s
(`featureInit`: its two variables hold one gate) and `features`' (`featuresInit`, sweep repairs 1,
B5: the gate, its features registered, with `Enabled`'s and `Set(false)`'s specs,
`k8sfeature.featureGateOk`; the gate is names-only, `component-base/featuregate`) and
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
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.RegistryDefs
public import Proof.k8s_io.apiserver.pkg.util.feature.Gate

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace k8s_io.apiserver.pkg.storage.etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The store's metrics package's fact: `ErrTransactionConflict` holds the error
`errors.New("transaction conflict")` (`metrics.go:42` at the apiserver pin `9c4ec15b8038`), for
good: a `*errorString` whose `Error()` returns that message. (Premise fixes 3, 2026-11-10: it was
some error; `txnError`'s result must be one grpc's `status` accepts, `statusErrOk`, for
`metrics.RecordEtcdRequest`.) -/
abbrev metricsInit : IProp GF :=
  EtcdGrove.errorsNewVar k8s_io.apiserver.pkg.storage.etcd3.metrics.ErrTransactionConflict
    go!"transaction conflict"

/-- `util/feature`'s fact: `DefaultMutableFeatureGate` and `DefaultFeatureGate` hold the same
feature gate, for good (Go never writes the variables after). (Sweep repairs 1, B5: until then
`DefaultFeatureGate`'s `Enabled` answered any `bool` for any feature, false of an unregistered one;
the gate's specs are now `features`' fact, `featuresInit`.) -/
abbrev featureInit : IProp GF :=
  iprop(∃ g : GoInterfaceOk,
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultMutableFeatureGate ↦□ GoInterface.ok g ∗
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g)

/-- `features`' fact (sweep repairs 1, B5): once its `init` registered its features with the
default gate, `DefaultFeatureGate` holds a gate with the specs of `k8sfeature.featureGateOk`
(`Enabled` of the queried features, `Set` of one to `false`). -/
abbrev featuresInit : IProp GF :=
  iprop(∃ g : GoInterfaceOk,
    globalAddr k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate ↦□ GoInterface.ok g ∗
    EtcdGrove.k8sfeature.featureGateOk g)

/-- **What `CheckClient` needs of its arguments** (sweep repairs 1, B5; revised after etcd-grove-81's
attack, `/shared/tmp/81-b5-attack`): `cl` a `*kubernetes.Client` whose embedded `*clientv3.Client` `c'`
holds, read-only, exactly the fields `CheckClient` relies on: the non-nil context `ctx` (`c.Ctx()`,
which the per-endpoint goroutines wait on), the embedded `Maintenance`, a non-nil `*maintenance`
(the goroutines call its `Status`), and the endpoints mutex `epMu`, non-nil (`Endpoints()` locks it).
Read-only (`↦□`): no party can write them afterwards, so a struct copy or an owner that later sets
`Maintenance` to nil cannot meet the guard (the attack's `maintnil` and `copy` cases, whose
`CheckClient` crashes). A nil client, a typed-nil one, or a zero `clientv3.Client` does not meet it
either (`notes/axiom-review/k8s-featureinit.md`). Producer: `New`'s client (`isNewClient_ctxOk`). -/
def checkClientOk (ctx cl : val) : IProp GF :=
  iprop(∃ (kc c' mp mu : Loc) (h cx : GoInterface),
    ⌜cl = #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #kc) ∧
      ctx = #cx ∧ cx ≠ GoInterface.nil ∧ mp ≠ null ∧ mu ≠ null⌝ ∗
    kc ↦□ go_etcd_io.etcd.client.v3.kubernetes.Client.mk c' h ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" c' ↦□ cx ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Maintenance" c' ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty) #mp : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" c' ↦□ mu)

/-- `storage/feature`'s fact: `CheckClient` on `DefaultFeatureSupportChecker`'s checker returns,
for a constructed client and its context (`checkClientOk`; see the file header). (Sweep repairs 1,
B5: until then for any arguments, false of a nil client.) -/
abbrev checkerInit : IProp GF :=
  iprop(□ ∀ (ctx cl f : val) (Φ : val → IProp GF), checkClientOk ctx cl -∗ ▷ Φ #() -∗
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

-- (logr: names only, the target of klog's alias `Logger`, notes/k8s-clientgo-goose.md)
instance github_com_go_logr_logr_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.go_logr.logr :=
  define_is_pkg_init iprop(True)
instance github_com_go_logr_logr_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.go_logr.logr :=
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

-- (sweep repairs 1, B5) after `util/feature`'s: `features` imports it
instance k8s_io_apiserver_pkg_features_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.features :=
  define_is_pkg_init featuresInit
instance k8s_io_apiserver_pkg_features_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.features :=
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

/-- `etcd3`'s fact: the compactor registry (`EtcdGrove.k8s.registryFact`, `RegistryDefs.lean`),
at the registry's name (`CompactorRegistry`, Q1 (c), 2026-11-05). -/
instance k8s_io_apiserver_pkg_storage_etcd3_is_pkg_init_inst [EtcdGrove.k8s.CompactorRegistry] :
    IsPkgInit (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 :=
  define_is_pkg_init (EtcdGrove.k8s.registryFact (GF := GF))
instance k8s_io_apiserver_pkg_storage_etcd3_get_is_pkg_init_wf_inst [EtcdGrove.k8s.CompactorRegistry] :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 :=
  build_get_is_pkg_init_wf

end init

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An `errors.New` error is one grpc's `status` accepts** (`statusErrOk`; premise fixes 3,
2026-11-10): a `*errorString` is a leaf without `Is` or `GRPCStatus` (`EtcdGrove.ErrorStringLeaf`,
of the method set goose emits), and its `Error()` returns its message. `metricsInit`'s
`ErrTransactionConflict`, which `txnError` returns. -/
theorem errorString_statusErrOk [EtcdGrove.ErrorStringLeaf] (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Error" #x)) (Val #())) {{ Φ }}) ⊢
    go_etcd_io.etcd.cache.v3.statusErrOk
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  obtain ⟨-, hl, hIs, hG⟩ := EtcdGrove.errorString_errLeaf x
  iintro #Hm
  unfold go_etcd_io.etcd.cache.v3.statusErrOk
  iintro !> %e %he
  cases he
  isplitr
  · iexists msg
    unfold go_etcd_io.etcd.cache.v3.errorMsgIs
    iexact Hm
  isplitr
  · ipureintro; exact hl
  isplitr
  rotate_left
  · ipureintro; exact EtcdGrove.ErrorStringLeaf.noFormat
  unfold go_etcd_io.etcd.cache.v3.grpcErrMethodsOk
  isplitl
  · iintro %h
    simp only [hG] at h; cases h
  · iintro %h
    exact absurd h hIs

/-- **The client's result error is one grpc's `status` accepts** (premise fixes 3): `nil` on
success, `statusErrOk` on failure, as `Client.Get`'s, `OptimisticPut`'s and `OptimisticDelete`'s
posts state it; the post is kept. -/
theorem statusErrOk_split (err : GoInterface) (P Q : IProp GF) (c : Prop) :
    ((⌜err = GoInterface.nil⌝ ∗ P) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ⌜c⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗ Q)) ⊢
    go_etcd_io.etcd.cache.v3.statusErrOk err ∗
      ((⌜err = GoInterface.nil⌝ ∗ P) ∨
        (⌜err ≠ GoInterface.nil⌝ ∗ ⌜c⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗ Q)) := by
  iintro (⟨%h, HP⟩ | ⟨%h, %hc, #Hs, HQ⟩)
  · subst h
    isplitr
    · iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
    · ileft; iframe HP; ipureintro; rfl
  · iframe Hs
    iright
    isplitr; · ipureintro; exact h
    isplitr; · ipureintro; exact hc
    iframe HQ

end errs

end k8s_io.apiserver.pkg.storage.etcd3
end Perennial
