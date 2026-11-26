/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`v3rpcInit`, `Base.lean`): its error map `toGRPCErrorMap` and counter vector
`clientRequests` with its label names (the map translated since grpcerrmap,
2026-11-26: until then the trust-boundary axiom `toGRPCErrorMap_init`; the vector translated, over `NewCounterVec`'s spec, until 2026-11-19 an
axiom `<X>_init`), `metricsServerLock` (an
unlocked mutex guarding `metricsServerCached`, `nil`: `metricsVars`), `rpctypes`' errors and
metadata keys and `etcdserverpb`'s sort-name maps and six `ServiceDesc`s (`svcDescsOk`, from their
facts), and `context.Canceled` a
pointer error (`EtcdGrove.ContextReadErrs.errs_strong`, from Perennial's `context.isInit`).
Its precondition has the registration rights of the metric
names of its import closure (`namesFree initNames`, decision D16; mustreg, 2026-11-20), which it
passes on to its imports' initializers.
(D19j, 2026-10-18) And what `watch.go` reads but `io.EOF` (`watchPkgVars`): `auth`'s and `mvcc`'s
errors (from their facts), `rpctypes`' (from its), its metrics `streamFailures` (with its label
names; translated, over `NewCounterVec`'s spec, until 2026-11-19 an axiom) and the four
`watchSendLoop*` histograms (translated, over prometheus's `NewHistogram` and `ExponentialBuckets`
specs; until 2026-11-19 the trust-boundary axioms `<X>_init`),
`traceutil.Tracer`, and `progressReportIntervalMu`, initialized here, guarding
`progressReportInterval` (`10 * time.Minute`: `intervalP`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.math.rand.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unicode.utf8.Link
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Init
public import Proof.go_etcd_io.etcd.server.v3.features.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
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
public import Perennial.Proof.sync.RWMutexGuard
public import Proof.github_com.prometheus.client_golang.prometheus.MetricLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ErrMapInit
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

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"client_grpc_sent_bytes_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"client_grpc_received_bytes_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"network" go!"server_stream_failures_total",
   EtcdGrove.prometheus.fqName go!"etcd" go!"server" go!"client_requests_total",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"server" go!"watch_send_loop_watch_stream_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"server" go!"watch_send_loop_watch_stream_duration_per_event_seconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"server" go!"watch_send_loop_control_stream_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"server" go!"watch_send_loop_progress_duration_seconds"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := EtcdGrove.grpc_prometheus.grpcKeys

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights (keyed by ID,
`EtcdGrove.prometheus.regRes`) are its initializer's resources (`ownInitResL`,
`Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.lease, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.wal, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regKeys)]

end go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

end Perennial
