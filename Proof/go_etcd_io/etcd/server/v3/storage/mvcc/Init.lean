/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.mvcc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`mvccInit`, `Base.lean`): its error variables (translated `errors.New` calls), its
metrics (`metrics.go`, untranslated: the trust-boundary axioms `<X>_init`; a counter's `Add` only
of a non-negative value), its constants, and `schema`'s two compaction key names (from `schema`'s
fact). `opaqueInitsOk` states its other untranslated initializers run.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.dustin.go_humanize.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Init
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_uber_org.zap.Init
public import Proof.hash.Init
public import Proof.k8s_io.utils.third_party.forked.golang.btree.initialize
public import Perennial.Proof.context.NewErrorString
public import Proof.errors.NewVarCell
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
namespace go_etcd_io.etcd.server.v3.storage.mvcc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.mvcc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([totalEventsCounter.init,
        dbTotalSize.init,
        dbTotalSizeInUse.init,
        dbOpenReadTxN.init,
        hashSec.init,
        hashRevSec.init,
        currentRev.init,
        compactRev.init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.mvcc`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `rangeCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom rangeCounter_init :
    {{ (True : IProp GF) }} (App (Val rangeCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr rangeCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `putCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom putCounter_init :
    {{ (True : IProp GF) }} (App (Val putCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr putCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `deleteCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom deleteCounter_init :
    {{ (True : IProp GF) }} (App (Val deleteCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr deleteCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `txnCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom txnCounter_init :
    {{ (True : IProp GF) }} (App (Val txnCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr txnCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `dbCompactionKeysCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom dbCompactionKeysCounter_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionKeysCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionKeysCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `watchStreamGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom watchStreamGauge_init :
    {{ (True : IProp GF) }} (App (Val watchStreamGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr watchStreamGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `watcherGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom watcherGauge_init :
    {{ (True : IProp GF) }} (App (Val watcherGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr watcherGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `pendingEventsGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom pendingEventsGauge_init :
    {{ (True : IProp GF) }} (App (Val pendingEventsGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr pendingEventsGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `totalPutSizeGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom totalPutSizeGauge_init :
    {{ (True : IProp GF) }} (App (Val totalPutSizeGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr totalPutSizeGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `slowWatcherGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom slowWatcherGauge_init :
    {{ (True : IProp GF) }} (App (Val slowWatcherGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr slowWatcherGauge ↦ GoInterface.ok m ∗ gaugeSpec m ∗ gaugeSetSpec m }}

/-- `keysGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom keysGauge_init :
    {{ (True : IProp GF) }} (App (Val keysGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr keysGauge ↦ GoInterface.ok m ∗ gaugeSpec m ∗ gaugeSetSpec m }}

/-- `dbCompactionLast = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom dbCompactionLast_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionLast.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionLast ↦ GoInterface.ok m ∗ gaugeSetSpec m }}

/-- `indexCompactionPauseMs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom indexCompactionPauseMs_init :
    {{ (True : IProp GF) }} (App (Val indexCompactionPauseMs.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr indexCompactionPauseMs ↦ GoInterface.ok m ∗ histSpec m }}

/-- `dbCompactionPauseMs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom dbCompactionPauseMs_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionPauseMs.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionPauseMs ↦ GoInterface.ok m ∗ histSpec m }}

/-- `dbCompactionTotalMs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom dbCompactionTotalMs_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionTotalMs.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionTotalMs ↦ GoInterface.ok m ∗ histSpec m }}

/-- `defaultCompactionBatchLimit = 1000` (`kvstore.go`). -/
axiom defaultCompactionBatchLimit_init :
    {{ (True : IProp GF) }} (App (Val defaultCompactionBatchLimit.init) (Val #()))
    {{ RET #(); globalAddr defaultCompactionBatchLimit ↦ (W64 1000 : w64) }}

/-- `defaultCompactionSleepInterval = 10 * time.Millisecond` (`kvstore.go`). -/
axiom defaultCompactionSleepInterval_init :
    {{ (True : IProp GF) }} (App (Val defaultCompactionSleepInterval.init) (Val #()))
    {{ RET #(); ∃ d : w64, globalAddr defaultCompactionSleepInterval ↦ d }}

end go_etcd_io.etcd.server.v3.storage.mvcc
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace go_etcd_io.etcd.server.v3.storage.mvcc

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := w64) watchBatchMaxRevs _ as HwatchBatchMaxRevs
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrWatcherDuplicateID _ as HErrWatcherDuplicateID
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrEmptyWatcherRange _ as HErrEmptyWatcherRange
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrWatcherNotExist _ as HErrWatcherNotExist
  wp_apply wp_GlobalAlloc (V := w64) watchResyncPeriod _ as HwatchResyncPeriod
  wp_apply wp_GlobalAlloc (V := w64) maxWatchersPerSync _ as HmaxWatchersPerSync
  wp_apply wp_GlobalAlloc (V := w64) chanBufLen _ as HchanBufLen
  wp_apply wp_GlobalAlloc (V := GoFunc) reportCompactRev _ as HreportCompactRev
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.RWMutex) reportCompactRevMu _ as HreportCompactRevMu
  wp_apply wp_GlobalAlloc (V := GoFunc) reportCurrentRev _ as HreportCurrentRev
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.RWMutex) reportCurrentRevMu _ as HreportCurrentRevMu
  wp_apply wp_GlobalAlloc (V := GoFunc) reportDbOpenReadTxN _ as HreportDbOpenReadTxN
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.RWMutex) reportDbOpenReadTxNMu _ as HreportDbOpenReadTxNMu
  wp_apply wp_GlobalAlloc (V := GoFunc) reportDbTotalSizeInUseInBytes _ as HreportDbTotalSizeInUseInBytes
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.RWMutex) reportDbTotalSizeInUseInBytesMu _ as HreportDbTotalSizeInUseInBytesMu
  wp_apply wp_GlobalAlloc (V := GoFunc) reportDbTotalSizeInBytes _ as HreportDbTotalSizeInBytes
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.RWMutex) reportDbTotalSizeInBytesMu _ as HreportDbTotalSizeInBytesMu
  wp_apply wp_GlobalAlloc (V := w64) restoreChunkKeys _ as HrestoreChunkKeys
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrFutureRev _ as HErrFutureRev
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCompacted _ as HErrCompacted
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRevisionNotFound _ as HErrRevisionNotFound
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.adt.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply (_root_.Perennial.go_opentelemetry_io.otel.trace.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (_root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.github_com.dustin.go_humanize.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.schedule.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.verify.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.lease.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.traceutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.k8s_io.utils.third_party.forked.golang.btree _root_.Perennial.k8s_io.utils.third_party.forked.golang.btree.initialize'
      EtcdGrove.ExternalInit.k8s_io_utils_third_party_forked_golang_btree _root_.Perennial.EtcdGrove.btree.initialize.wp_proof _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.schema.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.hash.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrRevisionNotFound))
  -- translated initializer of ErrCompacted))
  -- translated initializer of ErrFutureRev))
  -- translated initializer of restoreChunkKeys))
  wp_apply _root_.Perennial.context.wp_New_errorString as %xRNF #MRNF
  wp_apply EtcdGrove.wp_New_errorString_cell as %xCP ⟨#MCP, #CCP⟩
  wp_apply EtcdGrove.wp_New_errorString_cell as %xFR ⟨#MFR, #CFR⟩
  wp_apply defaultCompactionBatchLimit_init as HdefaultCompactionBatchLimit
  wp_apply defaultCompactionSleepInterval_init as ⟨%ddefaultCompactionSleepInterval, HdefaultCompactionSleepInterval⟩
  wp_apply rangeCounter_init as ⟨%mrangeCounter, HrangeCounter, #S0rangeCounter⟩
  wp_apply putCounter_init as ⟨%mputCounter, HputCounter, #S0putCounter⟩
  wp_apply deleteCounter_init as ⟨%mdeleteCounter, HdeleteCounter, #S0deleteCounter⟩
  wp_apply txnCounter_init as ⟨%mtxnCounter, HtxnCounter, #S0txnCounter⟩
  wp_apply keysGauge_init as ⟨%mkeysGauge, HkeysGauge, #S0keysGauge, #S1keysGauge⟩
  wp_apply watchStreamGauge_init as ⟨%mwatchStreamGauge, HwatchStreamGauge, #S0watchStreamGauge⟩
  wp_apply watcherGauge_init as ⟨%mwatcherGauge, HwatcherGauge, #S0watcherGauge⟩
  wp_apply slowWatcherGauge_init as ⟨%mslowWatcherGauge, HslowWatcherGauge, #S0slowWatcherGauge, #S1slowWatcherGauge⟩
  wp_apply (opaqueInitsOk totalEventsCounter.init (by mem_tac))
  wp_apply pendingEventsGauge_init as ⟨%mpendingEventsGauge, HpendingEventsGauge, #S0pendingEventsGauge⟩
  wp_apply indexCompactionPauseMs_init as ⟨%mindexCompactionPauseMs, HindexCompactionPauseMs, #S0indexCompactionPauseMs⟩
  wp_apply dbCompactionPauseMs_init as ⟨%mdbCompactionPauseMs, HdbCompactionPauseMs, #S0dbCompactionPauseMs⟩
  wp_apply dbCompactionTotalMs_init as ⟨%mdbCompactionTotalMs, HdbCompactionTotalMs, #S0dbCompactionTotalMs⟩
  wp_apply dbCompactionLast_init as ⟨%mdbCompactionLast, HdbCompactionLast, #S0dbCompactionLast⟩
  wp_apply dbCompactionKeysCounter_init as ⟨%mdbCompactionKeysCounter, HdbCompactionKeysCounter, #S0dbCompactionKeysCounter⟩
  -- translated initializer of reportDbTotalSizeInBytes))
  wp_apply (opaqueInitsOk dbTotalSize.init (by mem_tac))
  -- translated initializer of reportDbTotalSizeInUseInBytes))
  wp_apply (opaqueInitsOk dbTotalSizeInUse.init (by mem_tac))
  -- translated initializer of reportDbOpenReadTxN))
  wp_apply (opaqueInitsOk dbOpenReadTxN.init (by mem_tac))
  wp_apply (opaqueInitsOk hashSec.init (by mem_tac))
  wp_apply (opaqueInitsOk hashRevSec.init (by mem_tac))
  -- translated initializer of reportCurrentRev))
  wp_apply (opaqueInitsOk currentRev.init (by mem_tac))
  -- translated initializer of reportCompactRev))
  wp_apply (opaqueInitsOk compactRev.init (by mem_tac))
  wp_apply totalPutSizeGauge_init as ⟨%mtotalPutSizeGauge, HtotalPutSizeGauge, #S0totalPutSizeGauge⟩
  -- translated initializer of chanBufLen))
  -- translated initializer of maxWatchersPerSync))
  -- translated initializer of watchResyncPeriod))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  -- translated initializer of ErrWatcherNotExist))
  -- translated initializer of ErrEmptyWatcherRange))
  -- translated initializer of ErrWatcherDuplicateID))
  -- translated initializer of watchBatchMaxRevs))
  wp_apply _root_.Perennial.context.wp_New_errorString as %xWNE #MWNE
  wp_apply _root_.Perennial.context.wp_New_errorString as %xEWR #MEWR
  wp_apply _root_.Perennial.context.wp_New_errorString as %xWDI #MWDI
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist HErrRevisionNotFound
  ipersist HErrCompacted
  ipersist HErrFutureRev
  ipersist HErrWatcherNotExist
  ipersist HErrEmptyWatcherRange
  ipersist HErrWatcherDuplicateID
  ipersist HrangeCounter
  ipersist HputCounter
  ipersist HdeleteCounter
  ipersist HtxnCounter
  ipersist HdbCompactionKeysCounter
  ipersist HwatchStreamGauge
  ipersist HwatcherGauge
  ipersist HpendingEventsGauge
  ipersist HtotalPutSizeGauge
  ipersist HslowWatcherGauge
  ipersist HkeysGauge
  ipersist HdbCompactionLast
  ipersist HindexCompactionPauseMs
  ipersist HdbCompactionPauseMs
  ipersist HdbCompactionTotalMs
  ipersist HdefaultCompactionBatchLimit
  ipersist HdefaultCompactionSleepInterval
  ipersist HchanBufLen
  ipersist HmaxWatchersPerSync
  ipersist HwatchResyncPeriod
  ipersist HwatchBatchMaxRevs
  ipersist HrestoreChunkKeys
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd5
  icases Hsi with ⟨-, -, -, -, -, #HSK, #HFK⟩
  ihave #VCP : (EtcdGrove.errVarCell ErrCompacted go!"mvcc: required revision has been compacted" : IProp GF) $$ []
  · unfold EtcdGrove.errVarCell; iexists _; iframe HErrCompacted CCP
  ihave #VFR : (EtcdGrove.errVarCell ErrFutureRev go!"mvcc: required revision is a future revision" : IProp GF) $$ []
  · unfold EtcdGrove.errVarCell; iexists _; iframe HErrFutureRev CFR
  -- (R2) the metrics reporters' locks, each over its reporter (any closure)
  imod (sync.init_RWMutex (go_etcd_io.etcd.server.v3.storage.mvcc.reportP reportDbTotalSizeInBytes) (globalAddr reportDbTotalSizeInBytesMu) (E := ⊤)) $$ [HreportDbTotalSizeInBytes] HreportDbTotalSizeInBytesMu with HRP0
  · inext
    unfold go_etcd_io.etcd.server.v3.storage.mvcc.reportP
    iexists _; iframe HreportDbTotalSizeInBytes
  ihave ⟨-, #GRP0⟩ := sync.ownRWMutex_slots_guard _ _ $$ HRP0
  imod (sync.init_RWMutex (go_etcd_io.etcd.server.v3.storage.mvcc.reportP reportDbTotalSizeInUseInBytes) (globalAddr reportDbTotalSizeInUseInBytesMu) (E := ⊤)) $$ [HreportDbTotalSizeInUseInBytes] HreportDbTotalSizeInUseInBytesMu with HRP1
  · inext
    unfold go_etcd_io.etcd.server.v3.storage.mvcc.reportP
    iexists _; iframe HreportDbTotalSizeInUseInBytes
  ihave ⟨-, #GRP1⟩ := sync.ownRWMutex_slots_guard _ _ $$ HRP1
  imod (sync.init_RWMutex (go_etcd_io.etcd.server.v3.storage.mvcc.reportP reportDbOpenReadTxN) (globalAddr reportDbOpenReadTxNMu) (E := ⊤)) $$ [HreportDbOpenReadTxN] HreportDbOpenReadTxNMu with HRP2
  · inext
    unfold go_etcd_io.etcd.server.v3.storage.mvcc.reportP
    iexists _; iframe HreportDbOpenReadTxN
  ihave ⟨-, #GRP2⟩ := sync.ownRWMutex_slots_guard _ _ $$ HRP2
  imod (sync.init_RWMutex (go_etcd_io.etcd.server.v3.storage.mvcc.reportP reportCurrentRev) (globalAddr reportCurrentRevMu) (E := ⊤)) $$ [HreportCurrentRev] HreportCurrentRevMu with HRP3
  · inext
    unfold go_etcd_io.etcd.server.v3.storage.mvcc.reportP
    iexists _; iframe HreportCurrentRev
  ihave ⟨-, #GRP3⟩ := sync.ownRWMutex_slots_guard _ _ $$ HRP3
  imod (sync.init_RWMutex (go_etcd_io.etcd.server.v3.storage.mvcc.reportP reportCompactRev) (globalAddr reportCompactRevMu) (E := ⊤)) $$ [HreportCompactRev] HreportCompactRevMu with HRP4
  · inext
    unfold go_etcd_io.etcd.server.v3.storage.mvcc.reportP
    iexists _; iframe HreportCompactRev
  ihave ⟨-, #GRP4⟩ := sync.ownRWMutex_slots_guard _ _ $$ HRP4
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold mvccInit EtcdGrove.errorsNewVar
  iframe #
  rw [show (W64 100000000 : w64) = W64 100 * W64 1000000 by rfl]
  iexact HwatchResyncPeriod

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.storage.mvcc

end init

end Perennial
