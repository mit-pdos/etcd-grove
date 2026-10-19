/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`v3rpcInit`, `Base.lean`): its error map `toGRPCErrorMap` and counter vector
`clientRequests` with its label names (untranslated: the trust-boundary axioms `<X>_init`), `metricsServerLock` (an
unlocked mutex guarding `metricsServerCached`, `nil`: `metricsVars`), `rpctypes`' errors and
metadata keys and `etcdserverpb`'s sort-name maps and six `ServiceDesc`s (`svcDescsOk`, from their
facts), and `context.Canceled` a
pointer error (from the read package's premise `EtcdGrove.ContextReadErrs`: Perennial's `context`
fact lacks it). Its precondition has the read package's registration rights
(`EtcdGrove.read.readRegPerm`, decision D16), which it passes on to `etcdserver`'s initializer.
(D19j, 2026-10-18) And what `watch.go` reads but `io.EOF` (`watchPkgVars`): `auth`'s and `mvcc`'s
errors (from their facts), `rpctypes`' (from its), its metrics `streamFailures` (with its label
names) and the four
`watchSendLoop*` histograms (untranslated: the trust-boundary axioms `<X>_init`),
`traceutil.Tracer`, and `progressReportIntervalMu`, initialized here, guarding
`progressReportInterval` (`10 * time.Minute`: `intervalP`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.crypto.tls.Init
public import Proof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.credentials.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.config.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Init
public import Proof.go_etcd_io.etcd.server.v3.features.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.Init
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_uber_org.zap.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.health.Init
public import Proof.google_golang_org.grpc.health.grpc_health_v1.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.google_golang_org.grpc.status.Init
public import Proof.math.rand.Init
public import Proof.unicode.utf8.Init
public import Perennial.Proof.sync.RWMutexGuard
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
namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([sentBytes.init,
        receivedBytes.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `toGRPCErrorMap = map[error]error{...}` (`util.go`): a map whose values are `rpctypes.ErrGRPC*` errors (and `ErrTooManyRequests`, `ErrMemberNotEnoughStarted`), non-nil. -/
axiom toGRPCErrorMap_init :
    {{ (True : IProp GF) }} (App (Val toGRPCErrorMap.init) (Val #()))
    {{ RET #(); ∃ (mp : Loc) (M : GMap GoInterface GoInterface), globalAddr toGRPCErrorMap ↦ mp ∗ mp ↦$□ M ∗ ⌜∀ k v, M !! k = some v → v ≠ GoInterface.nil⌝ }}

/-- `clientRequests = prometheus.NewCounterVec(..., []string{"type", "client_api_version"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom clientRequests_init :
    {{ (True : IProp GF) }} (App (Val clientRequests.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr clientRequests ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"type", go!"client_api_version"]⌝ }}

/-- `streamFailures = prometheus.NewCounterVec(..., []string{"Type", "API"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom streamFailures_init :
    {{ (True : IProp GF) }} (App (Val streamFailures.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr streamFailures ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"Type", go!"API"]⌝ }}

/-- `watchSendLoopWatchStreamDuration = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom watchSendLoopWatchStreamDuration_init :
    {{ (True : IProp GF) }} (App (Val watchSendLoopWatchStreamDuration.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr watchSendLoopWatchStreamDuration ↦ GoInterface.ok h ∗ □ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x)) {{ RET #(); True }}) }}

/-- `watchSendLoopWatchStreamDurationPerEvent = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom watchSendLoopWatchStreamDurationPerEvent_init :
    {{ (True : IProp GF) }} (App (Val watchSendLoopWatchStreamDurationPerEvent.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr watchSendLoopWatchStreamDurationPerEvent ↦ GoInterface.ok h ∗ □ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x)) {{ RET #(); True }}) }}

/-- `watchSendLoopControlStreamDuration = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom watchSendLoopControlStreamDuration_init :
    {{ (True : IProp GF) }} (App (Val watchSendLoopControlStreamDuration.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr watchSendLoopControlStreamDuration ↦ GoInterface.ok h ∗ □ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x)) {{ RET #(); True }}) }}

/-- `watchSendLoopProgressDuration = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom watchSendLoopProgressDuration_init :
    {{ (True : IProp GF) }} (App (Val watchSendLoopProgressDuration.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr watchSendLoopProgressDuration ↦ GoInterface.ok h ∗ □ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x)) {{ RET #(); True }}) }}

end go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]
variable [_root_.Perennial.log.NewModel]

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_res (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc get_is_pkg_init) :
    {{ EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_res (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.RWMutex) progressReportIntervalMu _ as HprogressReportIntervalMu
  wp_apply wp_GlobalAlloc (V := w64) progressReportInterval _ as HprogressReportInterval
  wp_apply wp_GlobalAlloc (V := Loc) metricsServerCached _ as HmetricsServerCached
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Mutex) metricsServerLock _ as HmetricsServerLock
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.pkg.v3.traceutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd43⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd42⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.verify.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd41⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd40⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_opentelemetry_io.otel.trace.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd39⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_opentelemetry_io.otel.«attribute».wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd38⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.math.rand.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd37⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd36⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd35⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd34⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.version.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd33⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.config.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd32⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd31⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd30⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd29⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.pkg.v3.adt.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd28⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.google_golang_org.grpc.status.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd27⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.google_golang_org.grpc.codes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd26⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3 _root_.Perennial.go_etcd_io.raft.v3.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3 _root_.Perennial.go_etcd_io.raft.v3.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd25⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.types.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.google_golang_org.grpc.metadata.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.unicode.utf8.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.features.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.client.v3.credentials.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.google_golang_org.grpc.health.grpc_health_v1.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.google_golang_org.grpc.health.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.google_golang_org.grpc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.crypto.tls.wp_initialize'_lb _ Hinit.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.wp_initialize'_res _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.server.v3.auth.wp_initialize'_lb _ Hinit.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize'_lb _ Hinit.2.2.1))
    $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1))
    $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk sentBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk receivedBytes.init (by mem_tac))
  wp_apply streamFailures_init as ⟨%vstreamFailures, HstreamFailures, #LstreamFailures⟩
  wp_apply clientRequests_init as ⟨%vclientRequests, HclientRequests, #LclientRequests⟩
  wp_apply watchSendLoopWatchStreamDuration_init as ⟨%hwatchSendLoopWatchStreamDuration, HwatchSendLoopWatchStreamDuration, #SwatchSendLoopWatchStreamDuration⟩
  wp_apply watchSendLoopWatchStreamDurationPerEvent_init as ⟨%hwatchSendLoopWatchStreamDurationPerEvent, HwatchSendLoopWatchStreamDurationPerEvent, #SwatchSendLoopWatchStreamDurationPerEvent⟩
  wp_apply watchSendLoopControlStreamDuration_init as ⟨%hwatchSendLoopControlStreamDuration, HwatchSendLoopControlStreamDuration, #SwatchSendLoopControlStreamDuration⟩
  wp_apply watchSendLoopProgressDuration_init as ⟨%hwatchSendLoopProgressDuration, HwatchSendLoopProgressDuration, #SwatchSendLoopProgressDuration⟩
  wp_apply toGRPCErrorMap_init as ⟨%mptoGRPCErrorMap, %MtoGRPCErrorMap, HtoGRPCErrorMap, #StoGRPCErrorMap, %PtoGRPCErrorMap⟩
  -- translated initializer of progressReportInterval))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist HtoGRPCErrorMap
  ipersist HclientRequests
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd22
  icases Hri with ⟨-, #RCP, -, -, -, -, -, -, ⟨%eNSL, #HNSL, -⟩, -, -, #V0, #V1, #V2, #V3, #V4, #V5, #V6, #V7, #V8, #V9, #V10, #V11, #V12, #V13, #RW0, #RW1, #RW2, #RW3, #RW4, -⟩
  ihave Hpi : (go_etcd_io.etcd.cache.v3.etcdserverpbInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd2
  icases Hpi with ⟨#HSO, #HST, #HDescs⟩
  ihave ⟨#HCL, -⟩ := EtcdGrove.ContextReadErrs.errs $$ Hd1
  ihave #HCP : (∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok e ∗
      ⌜_root_.Perennial.errors.IsPointerError e⌝ : IProp GF) $$ []
  · iunfold EtcdGrove.errVarLeaf at HCL
    icases HCL with ⟨%e, #He, %Hl, -⟩
    iexists e
    iframe He
    ipureintro; exact Hl.1
  -- `getServerMetrics`' lock and what it guards (`metricsServerCached`, `nil`)
  imod sync.init_Mutex EtcdGrove.v3rpc.metricsP ⊤ EtcdGrove.v3rpc.metricsMu $$ HmetricsServerLock [HmetricsServerCached] with #HMV
  · inext
    unfold EtcdGrove.v3rpc.metricsP
    iexists _
    iframe HmetricsServerCached
    ileft
    ipureintro; rfl
  -- the six `ServiceDesc`s, from `etcdserverpb`'s fact
  icases HDescs with ⟨#HK, ⟨%wm, %ws, #HW, %HWp⟩, #HL, #HC, #HA, #HM, -⟩
  obtain ⟨rfl, HWp, -⟩ := HWp
  ihave #HSD : (EtcdGrove.v3rpc.svcDescsOk : IProp GF) $$ []
  · unfold EtcdGrove.v3rpc.svcDescsOk EtcdGrove.v3rpc.descOk EtcdGrove.descNames EtcdGrove.v3rpc.handlerTy EtcdGrove.v3rpc.kvDescMethods
    iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HL
    iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HC
    iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HA
    iunfold go_etcd_io.etcd.cache.v3.pbDescOk at HM
    iframe HK HL HC HA HM
    iexists ws
    iframe HW
    ipureintro; exact HWp
  -- (D19j) what `watch.go` reads but `io.EOF` (`watchPkgVars`): `auth`'s errors
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd3
  icases Hai with ⟨#AUE, -, #APD, #AAO, #AIA, -⟩
  ihave #WUE := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ AUE
  ihave #WPD := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ APD
  ihave #WAO := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ AAO
  ihave #WIA := EtcdGrove.v3rpc.errVarLeaf_of_authErrVar _ $$ AIA
  -- mvcc's
  ihave Hmi : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd36
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #NEWR, #NWDI, -⟩
  ihave #WEWR := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NEWR
  ihave #WWDI := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NWDI
  -- `rpctypes`'
  ihave #MCP := EtcdGrove.v3rpc.msgErrVar_of_spec _ $$ RCP
  ihave #MRW0 := EtcdGrove.v3rpc.msgErrVar_of_spec _ $$ RW0
  ihave #MRW1 := EtcdGrove.v3rpc.msgErrVar_of_spec _ $$ RW1
  ihave #MRW2 := EtcdGrove.v3rpc.msgErrVar_of_spec _ $$ RW2
  ihave #MRW3 := EtcdGrove.v3rpc.msgErrVar_of_spec _ $$ RW3
  ihave #MRW4 := EtcdGrove.v3rpc.msgErrVar_of_spec _ $$ RW4
  -- the metrics
  ipersist HstreamFailures
  ipersist HwatchSendLoopWatchStreamDuration
  ipersist HwatchSendLoopWatchStreamDurationPerEvent
  ipersist HwatchSendLoopControlStreamDuration
  ipersist HwatchSendLoopProgressDuration
  ihave #WH0 : (EtcdGrove.v3rpc.histVar watchSendLoopWatchStreamDuration : IProp GF) $$ []
  · iunfold EtcdGrove.v3rpc.histVar; iexists _; iframe HwatchSendLoopWatchStreamDuration SwatchSendLoopWatchStreamDuration
  ihave #WH1 : (EtcdGrove.v3rpc.histVar watchSendLoopWatchStreamDurationPerEvent : IProp GF) $$ []
  · iunfold EtcdGrove.v3rpc.histVar; iexists _; iframe HwatchSendLoopWatchStreamDurationPerEvent SwatchSendLoopWatchStreamDurationPerEvent
  ihave #WH2 : (EtcdGrove.v3rpc.histVar watchSendLoopControlStreamDuration : IProp GF) $$ []
  · iunfold EtcdGrove.v3rpc.histVar; iexists _; iframe HwatchSendLoopControlStreamDuration SwatchSendLoopControlStreamDuration
  ihave #WH3 : (EtcdGrove.v3rpc.histVar watchSendLoopProgressDuration : IProp GF) $$ []
  · iunfold EtcdGrove.v3rpc.histVar; iexists _; iframe HwatchSendLoopProgressDuration SwatchSendLoopProgressDuration
  -- `traceutil.Tracer`
  ihave Hti : (go_etcd_io.etcd.pkg.v3.traceutil.traceutilInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd43
  icases Hti with #HTR
  -- the progress interval's lock and what it guards (`progressReportInterval`, `10 * time.Minute`)
  imod (sync.init_RWMutex EtcdGrove.v3rpc.intervalP EtcdGrove.v3rpc.intervalMu (E := ⊤)) $$ [HprogressReportInterval] HprogressReportIntervalMu with HIS
  · inext
    unfold EtcdGrove.v3rpc.intervalP
    iexists _
    iframe HprogressReportInterval
    ipureintro
    first | decide | (simp [_root_.Perennial.time.Minute]; decide) | word
  ihave ⟨-, #HIG⟩ := sync.ownRWMutex_slots_guard _ _ $$ HIS
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold v3rpcInit EtcdGrove.v3rpc.watchPkgVars grpcErrMap checkErrVars sortNameMaps ctxCanceledPtr interceptorVars errVarSet EtcdGrove.v3rpc.metricsVars
  iframe #
  ipureintro
  exact PtoGRPCErrorMap

/-- Perennial's form with the resource (decision D16), from `wp_initialize'_res`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init ∗ EtcdGrove.read.readRegPerm (GF := GF) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc }} :=
  EtcdGrove.wp_init_of_res _ _ _ _ _ (wp_initialize'_res get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

end init

end Perennial
