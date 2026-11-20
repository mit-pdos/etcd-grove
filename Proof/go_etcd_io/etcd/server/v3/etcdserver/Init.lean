/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`srvInit`, `BaseApply.lean`): its metrics (`metrics.go`: the gauges and counters
translated, over prometheus's constructor specs, until 2026-11-19 the trust-boundary axioms
`<X>_init`; the vectors untranslated, the axioms `<X>_init`, with their label names), and from its imports' facts `traceutil.Tracer`, `schema`'s
`AllBuckets` and the error variables of `etcdserver/errors`, `auth` and raft it returns (leaf
errors by `EtcdGrove.ErrorStringLeaf`). Its precondition has the read package's
registration rights (`EtcdGrove.read.readRegPerm`, decision D16), which it passes on to the read
package's initializer. (D19r (C), 2026-10-18) And `raftStatusMu` (`raft.go`), initialized here,
guarding `raftStatus` (`rnRaftStatusOk`; the names-only `init()` registers an `expvar` closure that
reads `raftStatus` under the mutex). (revoke-open, 2026-11-06) And the counter `leaseExpired`
(`metrics.go`, translated: `prometheus.NewCounter` of a `CounterOpts` literal, the trust-boundary
axiom `NewCounter.wp_proof`), which
`revokeExpiredLeases` increments.
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.types.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.cindex.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Init
public import Proof.go_etcd_io.etcd.server.v3.features.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.leasehttp.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_uber_org.zap.Init
public import Proof.golang_org.x.crypto.bcrypt.Init
public import Proof.net.http.Init

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

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([«_».init,
        learnerPromoteFailed.init,
        learnerPromoteSucceed.init,
        currentVersion.init,
        currentGoVersion.init,
        fdUsed.init,
        fdLimit.init,
        monitorVersionInterval.init,
        recommendedMaxRequestBytesString.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `serverFeatureEnabled = prometheus.NewGaugeVec(..., []string{"name", "stage"})`
(`metrics.go`): a `*GaugeVec` with those label names (`vecLabels`). -/
axiom serverFeatureEnabled_init :
    {{ (True : IProp GF) }} (App (Val serverFeatureEnabled.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr serverFeatureEnabled ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"name", go!"stage"]⌝ }}

/-- `serverID = prometheus.NewGaugeVec(..., []string{"server_id"})`
(`metrics.go`): a `*GaugeVec` with those label names (`vecLabels`). -/
axiom serverID_init :
    {{ (True : IProp GF) }} (App (Val serverID.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr serverID ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"server_id"]⌝ }}

/-- `requestDurationSec = prometheus.NewHistogramVec(..., []string{"type", "success"})`
(`metrics.go`): a `*HistogramVec` with those label names (`vecLabels`). -/
axiom requestDurationSec_init :
    {{ (True : IProp GF) }} (App (Val requestDurationSec.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr requestDurationSec ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"type", go!"success"]⌝ }}

end go_etcd_io.etcd.server.v3.etcdserver
end opaqueInits

end Perennial
