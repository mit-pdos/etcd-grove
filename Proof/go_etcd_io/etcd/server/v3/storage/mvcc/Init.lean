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
public import Proof.k8s_io.utils.third_party.forked.golang.btree.initialize
public import Perennial.Proof.context.NewErrorString

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
    ∀ v ∈ ([restoreChunkKeys.init,
        totalEventsCounter.init,
        reportDbTotalSizeInBytes.init,
        dbTotalSize.init,
        reportDbTotalSizeInUseInBytes.init,
        dbTotalSizeInUse.init,
        reportDbOpenReadTxN.init,
        dbOpenReadTxN.init,
        hashSec.init,
        hashRevSec.init,
        reportCurrentRev.init,
        currentRev.init,
        reportCompactRev.init,
        compactRev.init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

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

/-- `keysGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom keysGauge_init :
    {{ (True : IProp GF) }} (App (Val keysGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr keysGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

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
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
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
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrFutureRev _ as HErrFutureRev
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCompacted _ as HErrCompacted
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRevisionNotFound _ as HErrRevisionNotFound
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.adt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply _root_.Perennial.go_opentelemetry_io.otel.trace.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply _root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply _root_.Perennial.github_com.dustin.go_humanize.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.schedule.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.verify.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.lease.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.pkg.v3.traceutil.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.EtcdGrove.btree.initialize.wp_proof _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.storage.schema.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.go_uber_org.zap.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.sync.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrRevisionNotFound))
  -- translated initializer of ErrCompacted))
  -- translated initializer of ErrFutureRev))
  wp_apply _root_.Perennial.context.wp_New_errorString as %xRNF #MRNF
  wp_apply _root_.Perennial.context.wp_New_errorString as %xCP #MCP
  wp_apply _root_.Perennial.context.wp_New_errorString as %xFR #MFR
  wp_apply (opaqueInitsOk restoreChunkKeys.init (by mem_tac))
  wp_apply defaultCompactionBatchLimit_init as HdefaultCompactionBatchLimit
  wp_apply defaultCompactionSleepInterval_init as ⟨%ddefaultCompactionSleepInterval, HdefaultCompactionSleepInterval⟩
  wp_apply rangeCounter_init as ⟨%mrangeCounter, HrangeCounter, #S0rangeCounter⟩
  wp_apply putCounter_init as ⟨%mputCounter, HputCounter, #S0putCounter⟩
  wp_apply deleteCounter_init as ⟨%mdeleteCounter, HdeleteCounter, #S0deleteCounter⟩
  wp_apply txnCounter_init as ⟨%mtxnCounter, HtxnCounter, #S0txnCounter⟩
  wp_apply keysGauge_init as ⟨%mkeysGauge, HkeysGauge, #S0keysGauge⟩
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
  wp_apply (opaqueInitsOk reportDbTotalSizeInBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk dbTotalSize.init (by mem_tac))
  wp_apply (opaqueInitsOk reportDbTotalSizeInUseInBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk dbTotalSizeInUse.init (by mem_tac))
  wp_apply (opaqueInitsOk reportDbOpenReadTxN.init (by mem_tac))
  wp_apply (opaqueInitsOk dbOpenReadTxN.init (by mem_tac))
  wp_apply (opaqueInitsOk hashSec.init (by mem_tac))
  wp_apply (opaqueInitsOk hashRevSec.init (by mem_tac))
  wp_apply (opaqueInitsOk reportCurrentRev.init (by mem_tac))
  wp_apply (opaqueInitsOk currentRev.init (by mem_tac))
  wp_apply (opaqueInitsOk reportCompactRev.init (by mem_tac))
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
  ipersist HkeysGauge
  ipersist HwatchStreamGauge
  ipersist HwatcherGauge
  ipersist HpendingEventsGauge
  ipersist HtotalPutSizeGauge
  ipersist HslowWatcherGauge
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
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd4
  icases Hsi with ⟨-, -, -, -, -, #HSK, #HFK⟩
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


end go_etcd_io.etcd.server.v3.storage.mvcc

end init

end Perennial
