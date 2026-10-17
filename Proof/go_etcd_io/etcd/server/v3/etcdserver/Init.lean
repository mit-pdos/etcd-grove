/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`srvInit`, `BaseApply.lean`): its metrics (`metrics.go`, untranslated: the
trust-boundary axioms `<X>_init`), and from its imports' facts `traceutil.Tracer`, `schema`'s
`AllBuckets` and the error variables of `etcdserver/errors`, `auth` and raft it returns (leaf
errors by the premise `EtcdGrove.ErrorStringLeaf`). Its theorem takes the read package's
initializer's spec (`wp_read`), not proved (`Spec/.../read/initialize.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.dustin.go_humanize.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.logutil.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.contention.Init
public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.Init
public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.notify.Init
public import Proof.go_etcd_io.etcd.pkg.v3.pbutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.wait.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.config.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.cindex.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Init
public import Proof.go_etcd_io.etcd.server.v3.features.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_uber_org.zap.Init
public import Proof.net.http.Init
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.initialize

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
namespace go_etcd_io.etcd.server.v3.etcdserver
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([«_».init,
        learnerPromoteFailed.init,
        learnerPromoteSucceed.init,
        applySnapshotInProgress.init,
        leaseExpired.init,
        currentVersion.init,
        currentGoVersion.init,
        serverID.init,
        serverFeatureEnabled.init,
        fdUsed.init,
        fdLimit.init,
        monitorVersionInterval.init,
        recommendedMaxRequestBytesString.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `hasLeader = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom hasLeader_init :
    {{ (True : IProp GF) }} (App (Val hasLeader.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr hasLeader ↦ GoInterface.ok m ∗ gaugeSetSpec m }}

/-- `isLeader = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom isLeader_init :
    {{ (True : IProp GF) }} (App (Val isLeader.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr isLeader ↦ GoInterface.ok m ∗ gaugeSetSpec m }}

/-- `proposalsCommitted = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom proposalsCommitted_init :
    {{ (True : IProp GF) }} (App (Val proposalsCommitted.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr proposalsCommitted ↦ GoInterface.ok m ∗ gaugeSetSpec m }}

/-- `proposalsApplied = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom proposalsApplied_init :
    {{ (True : IProp GF) }} (App (Val proposalsApplied.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr proposalsApplied ↦ GoInterface.ok m ∗ gaugeSetSpec m }}

/-- `leaderChanges = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom leaderChanges_init :
    {{ (True : IProp GF) }} (App (Val leaderChanges.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr leaderChanges ↦ GoInterface.ok m ∗ go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec m }}

/-- `heartbeatSendFailures = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom heartbeatSendFailures_init :
    {{ (True : IProp GF) }} (App (Val heartbeatSendFailures.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr heartbeatSendFailures ↦ GoInterface.ok m ∗ go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec m }}

/-- `proposalsFailed = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom proposalsFailed_init :
    {{ (True : IProp GF) }} (App (Val proposalsFailed.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr proposalsFailed ↦ GoInterface.ok m ∗ go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec m }}

/-- `proposalsPending = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom proposalsPending_init :
    {{ (True : IProp GF) }} (App (Val proposalsPending.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr proposalsPending ↦ GoInterface.ok m ∗ go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec m }}

/-- `requestDurationSec = prometheus.NewHistogramVec(...)` (`metrics.go`): a `*HistogramVec`. -/
axiom requestDurationSec_init :
    {{ (True : IProp GF) }} (App (Val requestDurationSec.init) (Val #()))
    {{ RET #(); ∃ hv : Loc, globalAddr requestDurationSec ↦ hv }}

end go_etcd_io.etcd.server.v3.etcdserver
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]
variable [_root_.Perennial.log.NewModel]

namespace go_etcd_io.etcd.server.v3.etcdserver

set_option maxHeartbeats 8000000 in
theorem wp_initialize'
    (wp_read : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.initialize'.spec (GF := GF) (hG := hG))
    (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd50⟩
  wp_apply _root_.Perennial.go_opentelemetry_io.otel.trace.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd49⟩
  wp_apply _root_.Perennial.go_opentelemetry_io.otel.«attribute».wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd48⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.lease.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd47⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.features.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd46⟩
  wp_apply wp_read _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd45⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd44⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd43⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd42⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd41⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.auth.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd40⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.wait.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd39⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.traceutil.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd38⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.schedule.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd37⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.notify.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd36⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.idutil.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd35⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd34⟩
  wp_apply _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd33⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.contention.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd32⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.logutil.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd31⟩
  wp_apply _root_.Perennial.log.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd30⟩
  wp_apply _root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd29⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd28⟩
  wp_apply _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd27⟩
  wp_apply _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd26⟩
  wp_apply _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd25⟩
  wp_apply _root_.Perennial.go_etcd_io.raft.v3.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.cindex.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.config.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.pbutil.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.types.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply _root_.Perennial.go_uber_org.zap.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply _root_.Perennial.github_com.dustin.go_humanize.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply _root_.Perennial.net.http.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.version.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.github_com.Masterminds.semver.v3.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.context.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply hasLeader_init as ⟨%mhasLeader, HhasLeader, #S0hasLeader⟩
  wp_apply isLeader_init as ⟨%misLeader, HisLeader, #S0isLeader⟩
  wp_apply leaderChanges_init as ⟨%mleaderChanges, HleaderChanges, #S0leaderChanges⟩
  wp_apply (opaqueInitsOk learnerPromoteFailed.init (by mem_tac))
  wp_apply (opaqueInitsOk learnerPromoteSucceed.init (by mem_tac))
  wp_apply heartbeatSendFailures_init as ⟨%mheartbeatSendFailures, HheartbeatSendFailures, #S0heartbeatSendFailures⟩
  wp_apply (opaqueInitsOk applySnapshotInProgress.init (by mem_tac))
  wp_apply proposalsCommitted_init as ⟨%mproposalsCommitted, HproposalsCommitted, #S0proposalsCommitted⟩
  wp_apply proposalsApplied_init as ⟨%mproposalsApplied, HproposalsApplied, #S0proposalsApplied⟩
  wp_apply proposalsPending_init as ⟨%mproposalsPending, HproposalsPending, #S0proposalsPending⟩
  wp_apply proposalsFailed_init as ⟨%mproposalsFailed, HproposalsFailed, #S0proposalsFailed⟩
  wp_apply requestDurationSec_init as ⟨%hvrequestDurationSec, HrequestDurationSec⟩
  wp_apply (opaqueInitsOk leaseExpired.init (by mem_tac))
  wp_apply (opaqueInitsOk currentVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk currentGoVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk serverID.init (by mem_tac))
  wp_apply (opaqueInitsOk serverFeatureEnabled.init (by mem_tac))
  wp_apply (opaqueInitsOk fdUsed.init (by mem_tac))
  wp_apply (opaqueInitsOk fdLimit.init (by mem_tac))
  wp_apply (opaqueInitsOk monitorVersionInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk recommendedMaxRequestBytesString.init (by mem_tac))
  ipersist HhasLeader
  ipersist HisLeader
  ipersist HproposalsCommitted
  ipersist HproposalsApplied
  ipersist HleaderChanges
  ipersist HheartbeatSendFailures
  ipersist HproposalsFailed
  ipersist HproposalsPending
  ipersist HrequestDurationSec
  ihave HeiTMR : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd20
  icases HeiTMR with ⟨-, #HevTMR⟩
  ihave #NTMR := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTooManyRequests) (m := go!"etcdserver: too many requests") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevTMR
  ihave #LTMR := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NTMR
  iunfold EtcdGrove.errorsNewVar at NTMR
  icases NTMR with ⟨%xTMR, #HTMR, -⟩
  ihave HeiRTL : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd20
  icases HeiRTL with ⟨-, #HevRTL⟩
  ihave #NRTL := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrRequestTooLarge) (m := go!"etcdserver: request is too large") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevRTL
  ihave #LRTL := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NRTL
  iunfold EtcdGrove.errorsNewVar at NRTL
  icases NRTL with ⟨%xRTL, #HRTL, -⟩
  ihave HeiSTP : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd20
  icases HeiSTP with ⟨-, #HevSTP⟩
  ihave #NSTP := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped) (m := go!"etcdserver: server stopped") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevSTP
  ihave #LSTP := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NSTP
  iunfold EtcdGrove.errorsNewVar at NSTP
  icases NSTP with ⟨%xSTP, #HSTP, -⟩
  ihave HeiCAN : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd20
  icases HeiCAN with ⟨-, #HevCAN⟩
  ihave #NCAN := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCanceled) (m := go!"etcdserver: request cancelled") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevCAN
  ihave #LCAN := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NCAN
  iunfold EtcdGrove.errorsNewVar at NCAN
  icases NCAN with ⟨%xCAN, #HCAN, -⟩
  ihave HeiTMO : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd20
  icases HeiTMO with ⟨-, #HevTMO⟩
  ihave #NTMO := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout) (m := go!"etcdserver: request timed out") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevTMO
  ihave #LTMO := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NTMO
  iunfold EtcdGrove.errorsNewVar at NTMO
  icases NTMO with ⟨%xTMO, #HTMO, -⟩
  ihave HeiTLF : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd20
  icases HeiTLF with ⟨-, #HevTLF⟩
  ihave #NTLF := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToLeaderFail) (m := go!"etcdserver: request timed out, possibly due to previous leader failure") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevTLF
  ihave #LTLF := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NTLF
  iunfold EtcdGrove.errorsNewVar at NTLF
  icases NTLF with ⟨%xTLF, #HTLF, -⟩
  ihave HeiTCL : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd20
  icases HeiTCL with ⟨-, #HevTCL⟩
  ihave #NTCL := EtcdGrove.errorsNewVars_mem (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToConnectionLost) (m := go!"etcdserver: request timed out, possibly due to connection lost") (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; mem_tac) $$ HevTCL
  ihave #LTCL := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NTCL
  iunfold EtcdGrove.errorsNewVar at NTCL
  icases NTCL with ⟨%xTCL, #HTCL, -⟩
  ihave Hai : (go_etcd_io.etcd.server.v3.auth.authInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd40
  icases Hai with ⟨-, -, -, #HAOR0, -⟩
  ihave #LAOR : (EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.auth.ErrAuthOldRevision : IProp GF) $$ []
  · unfold EtcdGrove.errVarLeaf EtcdGrove.errLeaf EtcdGrove.errMsgOk
    iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HAOR0
    iexact HAOR0
  ihave Hri : (go_etcd_io.raft.v3.isInitialized : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd24
  iunfold go_etcd_io.raft.v3.isInitialized at Hri
  icases Hri with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, Hrr⟩
  iNamed Hrr
  ihave #LPD := EtcdGrove.errVarLeaf_of_newVar _ _ $$ ErrPropDroppedNew
  ihave Hti : (go_etcd_io.etcd.pkg.v3.traceutil.traceutilInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd38
  icases Hti with ⟨%tr, #HTr⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, -, #HAB, -, -⟩
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold srvInit srvRaftInit srvReqInit srvApplyLoopInit srvErrVars
  iframe #
  ipureintro
  exact fun x => EtcdGrove.errorString_leaf x


end go_etcd_io.etcd.server.v3.etcdserver

end init

end Perennial
