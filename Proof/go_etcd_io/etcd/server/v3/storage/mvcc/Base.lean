/-
Package initialization instances for etcd's mvcc store (`server/v3/storage/mvcc`) and the
packages it imports that no other proof module provides: `pkg/v3/traceutil`, `server/v3/lease`,
`pkg/v3/schedule`, `go-humanize` (moved here from the server's `BaseApply.lean` on 2026-10-13: the
compaction job calls `humanize.Bytes`) and opentelemetry's `otel/trace` with the packages of the
types its `Span` names (`trace/embedded`, `codes`, `attribute`) (all names and types only, but
`schedule`'s jobs: `NewJob`, `job.Do`). The others are the interval tree's (`pkg/v3/adt/Base.lean`), the
cache's (`cache/v3/Base.lean`: `zap`, `proto`, `mvccpb`, `client/v3`), the server's
(`etcdserver/Base.lean`: `schema`), the backend's (`storage/backend/Base.lean`: `backend`,
`client/pkg/v3/verify`, prometheus's `client_golang/prometheus`), the btree's
(`btree/Init.lean`) and Perennial's (`sync`, `bytes`, `context`, `errors`, `fmt`, `time`,
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

public import Code.go_etcd_io.etcd.server.v3.storage.mvcc
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Perennial.Proof.time
public import Perennial.Proof.bytes
public import Perennial.Proof.math
public import Perennial.Proof.strings

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.pkg.v3.traceutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.traceutil

namespace go_etcd_io.etcd.server.v3.lease

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.lease

namespace go_etcd_io.etcd.pkg.v3.schedule

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.schedule

namespace github_com.dustin.go_humanize

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.dustin.go_humanize :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.dustin.go_humanize :=
  build_get_is_pkg_init_wf

end github_com.dustin.go_humanize

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

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.trace :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.trace :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.otel.trace

namespace go_etcd_io.etcd.server.v3.storage.mvcc

/-- A prometheus `Counter` as the KV core uses it: `Inc()` and `Add(x)` return. -/
def counterSpec (c : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods c.ty go!"Inc" c.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods c.ty go!"Add" c.v)) (Val #x)) {{ RET #(); True }}))

instance counterSpec_persistent (c : GoInterfaceOk) : Persistent (counterSpec (GF := GF) c) := by
  unfold counterSpec; infer_instance

/-- A prometheus `Gauge` as the KV core uses it: `Inc()`, `Dec()` and `Add(x)` return. -/
def gaugeSpec (g : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods g.ty go!"Inc" g.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods g.ty go!"Dec" g.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods g.ty go!"Add" g.v)) (Val #x)) {{ RET #(); True }}))

instance gaugeSpec_persistent (g : GoInterfaceOk) : Persistent (gaugeSpec (GF := GF) g) := by
  unfold gaugeSpec; infer_instance

/-- A prometheus `Histogram`'s `Observe(x)` returns (the compaction's timings). -/
def histSpec (h : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x)) {{ RET #(); True }}))

instance histSpec_persistent (h : GoInterfaceOk) : Persistent (histSpec (GF := GF) h) := by
  unfold histSpec; infer_instance

/-- A prometheus `Gauge`'s `Set(x)` returns (the watchable store's `slowWatcherGauge`). -/
def gaugeSetSpec (g : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods g.ty go!"Set" g.v)) (Val #x)) {{ RET #(); True }}))

instance gaugeSetSpec_persistent (g : GoInterfaceOk) : Persistent (gaugeSetSpec (GF := GF) g) := by
  unfold gaugeSetSpec; infer_instance

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
`Observe` returns, the counter `dbCompactionKeysCounter` and the gauge `dbCompactionLast`). -/
abbrev mvccInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok e) ∗
    (∃ g : GoInterfaceOk, globalAddr keysGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
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
    (∃ g : GoInterfaceOk, globalAddr dbCompactionLast ↦□ GoInterface.ok g ∗ gaugeSetSpec g))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc :=
  define_is_pkg_init mvccInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.mvcc

end init

end Perennial
