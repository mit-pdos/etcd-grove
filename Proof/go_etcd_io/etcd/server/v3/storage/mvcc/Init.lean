/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.mvcc`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`mvccInit`, `Base.lean`): its error variables (translated `errors.New` calls), its
metrics (`metrics.go`, translated: `prometheus.NewCounter`, `NewGauge` and `NewHistogram` of an
options literal, the trust-boundary axioms of those constructors and `ExponentialBuckets`'s spec; a
counter's `Add` only of a non-negative value), its constants, and `schema`'s two compaction key names (from `schema`'s
fact). (prove-initmisc, 2026-11-20) Its other metrics (`totalEventsCounter`, `hashSec`,
`hashRevSec`, and the `NewGaugeFunc` gauges, over that constructor's spec) and `_` (`var _
WatchableKV = (*watchableStore)(nil)`) are translated too (until then the trust-boundary axiom
`opaqueInitsOk`).
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
public import Proof.hash.crc32.Init
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVarCell
public import Perennial.Proof.sync.RWMutexGuard
public import Proof.github_com.prometheus.client_golang.prometheus.MetricLaws
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.runtime.PkgInitRes

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

namespace go_etcd_io.etcd.server.v3.storage.mvcc

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"range_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"put_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"delete_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"txn_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"keys_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"watch_stream_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"watcher_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"slow_watcher_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"events_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"pending_events_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"index_compaction_pause_duration_milliseconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"db_compaction_pause_duration_milliseconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"db_compaction_total_duration_milliseconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"db_compaction_last",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"db_compaction_keys_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"db_total_size_in_bytes",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"db_total_size_in_use_in_bytes",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"db_open_read_transactions",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"hash_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"mvcc" go!"hash_rev_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"current_revision",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"compact_revision",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"mvcc" go!"total_put_size_in_bytes"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := []

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights (keyed by ID,
`EtcdGrove.prometheus.regRes`) are its initializer's resources (`ownInitResL`,
`Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.lease, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regKeys)]

end go_etcd_io.etcd.server.v3.storage.mvcc

end Perennial
