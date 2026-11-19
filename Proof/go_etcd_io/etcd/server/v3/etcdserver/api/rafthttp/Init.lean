/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`rafthttpInit`, `etcdserver/BaseApply.lean`): `ErrExceedSizeLimit` holds a non-nil
error, `linkHeartbeatMessage` a heartbeat message without unknown fields, read-only for good. Its
initializer runs its variables' untranslated initializers: `ErrExceedSizeLimit`'s is an `errors.New`
call (`msg_codec.go`), which the trust-boundary axiom `errorsNewVarsInit` states;
`linkHeartbeatSize_init` states `linkHeartbeatSize`'s (`stream.go`); `opaqueInitsOk` the others.
(const-inits, 2026-11-19) The timeouts and intervals (`snapResponseReadTimeout`, `ConnWriteTimeout`,
`proberInterval`, `statusMonitoringInterval`, `statusErrorInterval`), `errMemberNotFound`
(`fmt.Errorf`, its proof) and `supportedStream` (a map literal of slice literals) are translated
and set (until then the trust-boundary axioms `<X>_init` and `opaqueInitsOk`).
`RaftPrefix` (`"/raft"`), its subpaths `ProbingPrefix`, `RaftStreamPrefix` and `RaftSnapshotPrefix`
(`path.Join`, proved), `ConnReadTimeout` (`DefaultConnReadTimeout`, five seconds), `readBytesLimit`
(512 MiB) and (raft-entsize, route H1, 2026-11-10) `linkHeartbeatMessage`
(`raftpb.Message{Type: raftpb.MsgHeartbeat.Enum()}`, `stream.go`: `Enum`'s proof inlined, the
literal frozen by `hbMsg_init`) are translated and set.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.dustin.go_humanize.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.github_com.xiang90.probing.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.transport.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.httputil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.ioutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.pbutil.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.golang_org.x.time.rate.Init
public import Proof.net.Init
public import Proof.net.http.Init
public import Proof.net.url.Init
public import Proof.path.Init
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2
public import Proof.errors.NewVarCell

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
namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`'s variables initialized by `errors.New`.** Each
listed `X.init` (untranslated) runs Go's `var X = errors.New(msg)`, as its Go source has
it, the fresh `errorString`'s `s` field holding `msg` (`errStrCell`, D19k). -/
axiom errorsNewVarsInit :
    ∀ (init : val) (X msg : GoString), (init, X, msg) ∈ ([(ErrExceedSizeLimit.init, ErrExceedSizeLimit, go!"rafthttp: error limit exceeded"),
        (errIncompatibleVersion.init, errIncompatibleVersion, go!"incompatible version"),
        (ErrClusterIDMismatch.init, ErrClusterIDMismatch, go!"cluster ID mismatch"),
        (errStopped.init, errStopped, go!"stopped"),
        (errMemberRemoved.init, errMemberRemoved, go!"the member has been permanently removed from the cluster"),
        (errUnsupportedStreamType.init, errUnsupportedStreamType, go!"unsupported stream type")] : List (val × GoString × GoString)) →
    EtcdGrove.errorsNewVarInitC (GF := GF) init X msg

/-- `linkHeartbeatSize = proto.Size(&linkHeartbeatMessage)` (`stream.go`): the heartbeat's encoding's size (two bytes), an `int` from `0` to below `2^50`; nothing writes it (the stream writer adds it to its metrics). -/
axiom linkHeartbeatSize_init :
    {{ (True : IProp GF) }} (App (Val linkHeartbeatSize.init) (Val #()))
    {{ RET #(); ∃ n : w64, globalAddr linkHeartbeatSize ↦ n ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n < 2 ^ 50⌝ }}

/-- `receivedBytes = prometheus.NewCounterVec(..., []string{"From"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom receivedBytes_init :
    {{ (True : IProp GF) }} (App (Val receivedBytes.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr receivedBytes ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝ }}

/-- `recvFailures = prometheus.NewCounterVec(..., []string{"From"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom recvFailures_init :
    {{ (True : IProp GF) }} (App (Val recvFailures.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr recvFailures ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝ }}

/-- `sentBytes = prometheus.NewCounterVec(..., []string{"To"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom sentBytes_init :
    {{ (True : IProp GF) }} (App (Val sentBytes.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr sentBytes ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝ }}

/-- `sentFailures = prometheus.NewCounterVec(..., []string{"To"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom sentFailures_init :
    {{ (True : IProp GF) }} (App (Val sentFailures.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr sentFailures ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝ }}

/-- `activePeers = prometheus.NewGaugeVec(..., []string{"Local", "Remote"})`
(`metrics.go`): a `*GaugeVec` with those label names (`vecLabels`). -/
axiom activePeers_init :
    {{ (True : IProp GF) }} (App (Val activePeers.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr activePeers ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"Local", go!"Remote"]⌝ }}

/-- `disconnectedPeers = prometheus.NewCounterVec(..., []string{"Local", "Remote"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom disconnectedPeers_init :
    {{ (True : IProp GF) }} (App (Val disconnectedPeers.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr disconnectedPeers ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"Local", go!"Remote"]⌝ }}

/-- `rttSec = prometheus.NewHistogramVec(...)` (`metrics.go`): some pointer, read-only for good. -/
axiom rttSec_init :
    {{ (True : IProp GF) }} (App (Val rttSec.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr rttSec ↦ v }}

/-- `snapshotSend = prometheus.NewCounterVec(..., []string{"To"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom snapshotSend_init :
    {{ (True : IProp GF) }} (App (Val snapshotSend.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotSend ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝ }}

/-- `snapshotSendInflights = prometheus.NewGaugeVec(..., []string{"To"})`
(`metrics.go`): a `*GaugeVec` with those label names (`vecLabels`). -/
axiom snapshotSendInflights_init :
    {{ (True : IProp GF) }} (App (Val snapshotSendInflights.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotSendInflights ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝ }}

/-- `snapshotSendFailures = prometheus.NewCounterVec(..., []string{"To"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom snapshotSendFailures_init :
    {{ (True : IProp GF) }} (App (Val snapshotSendFailures.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotSendFailures ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝ }}

/-- `snapshotSendSeconds = prometheus.NewHistogramVec(..., []string{"To"})`
(`metrics.go`): a `*HistogramVec` with those label names (`vecLabels`). -/
axiom snapshotSendSeconds_init :
    {{ (True : IProp GF) }} (App (Val snapshotSendSeconds.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotSendSeconds ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝ }}

/-- `snapshotReceive = prometheus.NewCounterVec(..., []string{"From"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom snapshotReceive_init :
    {{ (True : IProp GF) }} (App (Val snapshotReceive.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotReceive ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝ }}

/-- `snapshotReceiveInflights = prometheus.NewGaugeVec(..., []string{"From"})`
(`metrics.go`): a `*GaugeVec` with those label names (`vecLabels`). -/
axiom snapshotReceiveInflights_init :
    {{ (True : IProp GF) }} (App (Val snapshotReceiveInflights.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotReceiveInflights ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝ }}

/-- `snapshotReceiveFailures = prometheus.NewCounterVec(..., []string{"From"})`
(`metrics.go`): a `*CounterVec` with those label names (`vecLabels`). -/
axiom snapshotReceiveFailures_init :
    {{ (True : IProp GF) }} (App (Val snapshotReceiveFailures.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotReceiveFailures ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝ }}

/-- `snapshotReceiveSeconds = prometheus.NewHistogramVec(..., []string{"From"})`
(`metrics.go`): a `*HistogramVec` with those label names (`vecLabels`). -/
axiom snapshotReceiveSeconds_init :
    {{ (True : IProp GF) }} (App (Val snapshotReceiveSeconds.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr snapshotReceiveSeconds ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝ }}

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
end opaqueInits

end Perennial
