/-
Package initialization instances for etcd's mvcc store (`server/v3/storage/mvcc`) and the
packages it imports that no other proof module provides: `pkg/v3/traceutil`,
`pkg/v3/schedule` and opentelemetry's `otel/trace` with the packages of the
types its `Span` names (`trace/embedded`, `codes`, `attribute`) and its no-op tracer (`trace/noop`) (all names and types only, but
`schedule`'s jobs: `NewJob`, `job.Do`) and `hash` (a standard-library package Perennial does not
translate: types only, here, the type of `kvHasher`'s `hash` field). The others are the interval tree's (`pkg/v3/adt/Base.lean`), the
cache's (`cache/v3/Base.lean`: `zap`, `proto`, `mvccpb`, `client/v3`), the server's
(`etcdserver/Base.lean`: `schema`), the backend's (`storage/backend/Base.lean`: `backend`,
`client/pkg/v3/verify`, prometheus's `client_golang/prometheus`, `go-humanize`: S4b, 2026-11-18, the
snapshot's goroutine calls `humanize.Bytes`; until then here), the btree's
(`btree/Init.lean`), the lessor's (`server/v3/lease/Base.lean`) and Perennial's (`sync`, `bytes`, `context`, `errors`, `fmt`, `time`,
`encoding/binary`, `math`, `strings`).

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'` (mvcc's initializer runs the axiomatized initializers of its untranslated
variables). `mvccInit` states what the KV core reads of them: the three error variables, each
a fixed non-nil error, and the prometheus counters and gauges of `metrics.go` the transactions
and the key index update, each a fixed interface value whose `Inc`/`Dec`/`Add` return
(`counterSpec`, `gaugeSpec`: metrics have no effect here); and the two configuration defaults
`NewStore` reads (`defaultCompactionBatchLimit`, `defaultCompactionSleepInterval`), any values;
the watch stream's errors and gauge, and the watcher group's `watchBatchMaxRevs` (1000).
-/
module

public import Proof.errors.NewVarCell
public import Code.go_etcd_io.etcd.server.v3.storage.mvcc
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Proof.time
public import Perennial.Proof.bytes
public import Proof.hash.crc32.PkgInit
public import Perennial.Proof.math
public import Perennial.Proof.strings
public import Perennial.Proof.io
public import Proof.hash.PkgInit
public import Proof.github_com.prometheus.client_golang.prometheus.Metric
public import Proof.github_com.prometheus.client_golang.prometheus.MetricRep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- (`hash`'s instance: `Proof/hash/PkgInit.lean`, shared with bbolt)

namespace go_etcd_io.etcd.pkg.v3.schedule

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.schedule

namespace go_opentelemetry_io.otel.trace.embedded

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.trace.embedded :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.trace.embedded :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.otel.trace.embedded

namespace go_opentelemetry_io.otel.codes

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.codes :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.codes :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.otel.codes

namespace go_opentelemetry_io.otel.attribute

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.attribute :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.attribute :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.otel.attribute

namespace go_opentelemetry_io.otel.trace

/-- otel `trace`'s fact (prove-protootel, 2026-11-20; `True` until then): `noopSpanInstance` holds a
`noopSpan` as a `Span`, read-only for good (`noop.go`: `var noopSpanInstance Span = noopSpan{}`), what
`SpanFromContext` returns when the context has no span. -/
def traceInit : IProp GF :=
  iprop(∃ x : noopSpan, globalAddr noopSpanInstance ↦□ (interface.mkOk noopSpan.ty #x : GoInterface))

instance traceInit_persistent : Persistent (traceInit (GF := GF)) := by
  unfold traceInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.trace :=
  define_is_pkg_init traceInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.trace :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.otel.trace

namespace go_opentelemetry_io.otel.trace.noop

/-- otel `trace/noop`'s fact (otel-tracing, 2026-11-23): `noopSpanInstance` holds a no-op `Span` as a
`trace.Span`, read-only for good (`noop.go`: `var noopSpanInstance trace.Span = Span{}`). -/
def noopInit : IProp GF :=
  iprop(∃ x : Span, globalAddr noopSpanInstance ↦□ (interface.mkOk Span.ty #x : GoInterface))

instance noopInit_persistent : Persistent (noopInit (GF := GF)) := by
  unfold noopInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.trace.noop :=
  define_is_pkg_init noopInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.trace.noop :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.otel.trace.noop

namespace go_etcd_io.etcd.pkg.v3.traceutil

/-- `traceutil`'s fact (item 8, 2026-10-17: moved here from the server's `srvReqInit`): `Tracer`
holds a fixed tracer (`trace.go`: `noop.NewTracerProvider().Tracer(...)`). -/
abbrev traceutilInit : IProp GF :=
  iprop(∃ tr : GoInterfaceOk, globalAddr Tracer ↦□ GoInterface.ok tr)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil :=
  define_is_pkg_init traceutilInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.traceutil

namespace go_etcd_io.etcd.server.v3.storage.mvcc

/- The prometheus metrics' method specs (`counterSpec`, `gaugeSpec`, `histSpec`, `gaugeSetSpec`),
defined here until 2026-11-19, are prometheus's (`EtcdGrove.prometheus.metric`, the package's
`Metric.lean`), re-exported under their old names. -/
export EtcdGrove.prometheus.metric (counterSpec counterSpec_persistent gaugeSpec gaugeSpec_persistent
  histSpec histSpec_persistent gaugeSetSpec gaugeSetSpec_persistent)

/-- **What a metrics reporter's lock guards** at the fraction `q` (`metrics.go`: each of the five
`report*` closures, which `setupMetricsReporter` sets under its `report*Mu`; the restore plan's
R2): some closure. Only Prometheus's collector calls them, which no verified code runs. -/
def reportP (g : GoString) (q : Qp) : IProp GF :=
  iprop(∃ f : GoFunc, typedPointsto (globalAddr g) f (DFrac.own q))

instance reportP_fractional (g : GoString) : Fractional (reportP (GF := GF) g) where
  fractional q1 q2 := by
    unfold reportP
    constructor
    · iintro ⟨%f, Hf⟩
      icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hf with ⟨H1, H2⟩
      isplitl [H1]
      · iexists f; iframe
      · iexists f; iframe
    · iintro ⟨⟨%f1, H1⟩, ⟨%f2, H2⟩⟩
      icombine H1 H2 gives %Hf
      subst Hf
      iexists f1
      iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe

/-- The metrics reporter `g`'s lock `mu` (persistent): a guarded `RWMutex` over `reportP g`. -/
abbrev reportVar (mu g : GoString) : IProp GF :=
  sync.isRWMutexGuard (globalAddr mu) (reportP g)

/-- mvcc's package facts: the error variables `ErrRevisionNotFound` (`key_index.go`),
`ErrCompacted` and `ErrFutureRev` (`kvstore.go`), each a fixed non-nil error; and the metrics
of `metrics.go` the KV core updates: the gauge `keysGauge` (the key index), the counters
`txnCounter`, `rangeCounter`, `putCounter`, `deleteCounter` and the gauge `totalPutSizeGauge`
(the transactions' `End`); and the variables `defaultCompactionBatchLimit` and
`defaultCompactionSleepInterval` (`kvstore.go`) `NewStore` reads, read-only (only tests change
them), the batch limit's its initial value `1000` (the compaction job's loop needs a positive
limit), the interval's unconstrained; and the watch
stream's (`watcher.go`): the errors `ErrWatcherNotExist`, `ErrEmptyWatcherRange` and
`ErrWatcherDuplicateID`, each a fixed non-nil error, and the gauge `watchStreamGauge`; and the
watcher group's (`watcher_group.go`): `watchBatchMaxRevs`, a `var` for tests only, read-only at
its initial value `1000`; and the watchable store's (`watchable_store.go`, `metrics.go`): the
gauges `watcherGauge`, `slowWatcherGauge` and `pendingEventsGauge`, the `var`s `chanBufLen`
(`128`), `maxWatchersPerSync` (`512`) and `watchResyncPeriod` (`100 * time.Millisecond`), for
tests only, read-only at their initial values, and `slowWatcherGauge`'s `Set` (`syncWatchers`);
and compaction's (2026-10-13, unit 5a): the two `Meta` key names it reads and writes
(`schema.ScheduledCompactKeyName`, `schema.FinishedCompactKeyName`: the bytes of
`"scheduledCompactRev"` and `"finishedCompactRev"`, read-only; `schema` is names-only for them,
and its own facts are the consistent index's), and the compaction metrics (`metrics.go`: the
histograms `indexCompactionPauseMs`, `dbCompactionPauseMs`, `dbCompactionTotalMs`, whose
`Observe` returns, the counter `dbCompactionKeysCounter` and the gauge `dbCompactionLast`); and
(item 8, 2026-10-17) `ErrCompacted` and `ErrFutureRev` as the `errors.New` errors they are, which
the apply package's facts take from here; and (D19j, 2026-10-18) `ErrEmptyWatcherRange` and
`ErrWatcherDuplicateID` as theirs, which `v3rpc`'s facts take from here; and (2026-10-23, the
restore plan's R0) `restoreChunkKeys` (`kvstore.go`: `10000`, a `var` for tests only, read-only at
its initial value), the chunk size and channel capacity of `store.restore`; and (R2) the five
metrics reporters' locks (`reportVar`), which `setupMetricsReporter` takes to set them; and
(mvccfull's Freeze, 2026-11-10: `errVars.law`) `ErrWatcherNotExist` as the `errors.New` error it is,
and the message cells of `ErrEmptyWatcherRange` and `ErrWatcherNotExist` (as `ErrCompacted`'s and
`ErrFutureRev`'s), so that the four error variables a client compares with are apart: one conjunct,
the last, so that every pattern ending in `-` is unchanged; and (prove-ps2-metrics, 2026-11-22), in
that last conjunct, `ReportEventReceived`'s two metrics: the counter `totalEventsCounter` and the
gauge `pendingEventsGauge` as the `*gauge` it is (`metric.isGauge`, for its proved `Sub`). -/
abbrev mvccInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok e) ∗
    (∃ g : GoInterfaceOk, globalAddr keysGauge ↦□ GoInterface.ok g ∗ gaugeSpec g ∗ gaugeSetSpec g) ∗
    (∃ c : GoInterfaceOk, globalAddr txnCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr rangeCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr putCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr deleteCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ g : GoInterfaceOk, globalAddr totalPutSizeGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
    globalAddr defaultCompactionBatchLimit ↦□ (W64 1000 : w64) ∗
    (∃ d : w64, globalAddr defaultCompactionSleepInterval ↦□ d) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrWatcherNotExist ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrEmptyWatcherRange ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrWatcherDuplicateID ↦□ GoInterface.ok e) ∗
    (∃ g : GoInterfaceOk, globalAddr watchStreamGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
    globalAddr watchBatchMaxRevs ↦□ (W64 1000 : w64) ∗
    (∃ g : GoInterfaceOk, globalAddr watcherGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
    (∃ g : GoInterfaceOk, globalAddr slowWatcherGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
    (∃ g : GoInterfaceOk, globalAddr pendingEventsGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
    globalAddr chanBufLen ↦□ (W64 128 : w64) ∗
    globalAddr maxWatchersPerSync ↦□ (W64 512 : w64) ∗
    globalAddr watchResyncPeriod ↦□ (W64 100000000 : w64) ∗
    (∃ g : GoInterfaceOk, globalAddr slowWatcherGauge ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ s : GoSlice, globalAddr go_etcd_io.etcd.server.v3.storage.schema.ScheduledCompactKeyName ↦□ s ∗
      s ↦*□ (go!"scheduledCompactRev" : GoString)) ∗
    (∃ s : GoSlice, globalAddr go_etcd_io.etcd.server.v3.storage.schema.FinishedCompactKeyName ↦□ s ∗
      s ↦*□ (go!"finishedCompactRev" : GoString)) ∗
    (∃ h : GoInterfaceOk, globalAddr indexCompactionPauseMs ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr dbCompactionPauseMs ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr dbCompactionTotalMs ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ c : GoInterfaceOk, globalAddr dbCompactionKeysCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ g : GoInterfaceOk, globalAddr dbCompactionLast ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    EtcdGrove.errorsNewVar ErrCompacted go!"mvcc: required revision has been compacted" ∗
    EtcdGrove.errorsNewVar ErrFutureRev go!"mvcc: required revision is a future revision" ∗
    EtcdGrove.errorsNewVar ErrEmptyWatcherRange go!"mvcc: watcher range is empty" ∗
    EtcdGrove.errorsNewVar ErrWatcherDuplicateID
      go!"mvcc: duplicate watch ID provided on the WatchStream" ∗
    EtcdGrove.errVarCell ErrCompacted go!"mvcc: required revision has been compacted" ∗
    EtcdGrove.errVarCell ErrFutureRev go!"mvcc: required revision is a future revision" ∗
    globalAddr restoreChunkKeys ↦□ (W64 10000 : w64) ∗
    reportVar reportDbTotalSizeInBytesMu reportDbTotalSizeInBytes ∗
    reportVar reportDbTotalSizeInUseInBytesMu reportDbTotalSizeInUseInBytes ∗
    reportVar reportDbOpenReadTxNMu reportDbOpenReadTxN ∗
    reportVar reportCurrentRevMu reportCurrentRev ∗
    reportVar reportCompactRevMu reportCompactRev ∗
    (EtcdGrove.errorsNewVar ErrWatcherNotExist go!"mvcc: watcher does not exist" ∗
      EtcdGrove.errVarCell ErrEmptyWatcherRange go!"mvcc: watcher range is empty" ∗
      EtcdGrove.errVarCell ErrWatcherNotExist go!"mvcc: watcher does not exist" ∗
      (∃ c : GoInterfaceOk, globalAddr totalEventsCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
      (∃ g : GoInterfaceOk, globalAddr pendingEventsGauge ↦□ GoInterface.ok g ∗
        EtcdGrove.prometheus.metric.isGauge g)))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc :=
  define_is_pkg_init mvccInit
instance get_isPkgInit_wf_inst [EtcdGrove.prometheus.PromRegGS GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.mvcc

end init

end Perennial
