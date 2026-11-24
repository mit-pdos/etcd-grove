/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`srvInit`, `BaseApply.lean`): its metrics (`metrics.go`: the gauges and counters
translated, over prometheus's constructor specs, until 2026-11-19 the trust-boundary axioms
`<X>_init`; the vectors, with their label names, translated over the `New<Kind>Vec` specs, until
2026-11-19 the axioms `<X>_init`), and from its imports' facts `traceutil.Tracer`, `schema`'s
`AllBuckets` and the error variables of `etcdserver/errors`, `auth` and raft it returns (leaf
errors by `EtcdGrove.ErrorStringLeaf`). Its precondition has the
registration rights of the metric names of its import closure (`namesFree initNames`, decision D16;
the read package's, `EtcdGrove.read.readRegPerm`, until mustreg, 2026-11-20), which it passes on to
the registering packages' initializers. (D19r (C), 2026-10-18) And `raftStatusMu` (`raft.go`), initialized here,
guarding `raftStatus` (`rnRaftStatusOk`; the `init()` of `raft.go` registers an `expvar` closure that
reads `raftStatus` under the mutex: a trusted no-op model since etcd-grove#39, 2026-11-23, as `server.go`'s,
since no verified code reads `expvar`'s registry; `metrics.go`'s, which registers the metrics, stays
names-only, the trust-boundary axiom `initFuncsOk`: translating it needs Perennial's `runtime.Version`). (revoke-open, 2026-11-06) And the counter `leaseExpired`
(`metrics.go`, translated: `prometheus.NewCounter` of a `CounterOpts` literal, the trust-boundary
axiom `NewCounter.wp_proof`), which
`revokeExpiredLeases` increments. (auth-mediation M2, 2026-11-20) And `PromoteMember`'s metrics,
the counter `learnerPromoteSucceed` and the counter vector `learnerPromoteFailed`. (prove-errinits, 2026-11-19) Its other metrics (`learnerPromoteFailed`,
`learnerPromoteSucceed`, `currentVersion`, `currentGoVersion`, `fdUsed`, `fdLimit`),
and `recommendedMaxRequestBytesString` (`humanize.Bytes`, over its spec) are translated too;
(prove-etcdserver, 2026-11-20) and `monitorVersionInterval` (`rafthttp.ConnWriteTimeout - time.Second`,
from rafthttp's fact) and `_` (`var _ serverversion.Server = ...`, a conversion): no untranslated
initializer is left.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.base64.Init
public import Proof.encoding.json.Init
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.dustin.go_humanize.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.logutil.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.contention.Init
public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.Init
public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.notify.Init
public import Proof.go_etcd_io.etcd.pkg.v3.pbutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.runtime.Init
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.wait.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.config.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.types.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.cindex.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Init
public import Proof.go_etcd_io.etcd.server.v3.features.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.leasehttp.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_uber_org.zap.Init
public import Proof.golang_org.x.crypto.bcrypt.Init
public import Proof.net.http.Init
public import Proof.os.Init
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

section opaqueInits
namespace go_etcd_io.etcd.server.v3.etcdserver
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.server.v3.etcdserver
end opaqueInits

namespace go_etcd_io.etcd.server.v3.etcdserver

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights (keyed by ID,
`EtcdGrove.prometheus.regRes`) are its initializer's resources (`ownInitResL`,
`Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.auth, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.auth.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.apply.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.read.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.txn.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.lease, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.lease.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.regKeys), (pkg_id.go_etcd_io.etcd.server.v3.storage.wal, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regKeys)]

end go_etcd_io.etcd.server.v3.etcdserver

end Perennial
