/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`rafthttpInit`, `etcdserver/BaseApply.lean`): `ErrExceedSizeLimit` holds a non-nil
error, `linkHeartbeatMessage` a heartbeat message, read-only for good. Its initializer runs its
variables' untranslated initializers: `ErrExceedSizeLimit`'s is an `errors.New` call
(`msg_codec.go`), which the trust-boundary axiom `errorsNewVarsInit` states; `linkHeartbeatMessage_init`
states `linkHeartbeatMessage`'s and `linkHeartbeatSize_init` `linkHeartbeatSize`'s (`stream.go`);
`opaqueInitsOk` the others. `RaftPrefix` (`"/raft"`), its subpaths `ProbingPrefix`,
`RaftStreamPrefix` and `RaftSnapshotPrefix` (`path.Join`, proved), `ConnReadTimeout`
(`DefaultConnReadTimeout`, five seconds) and `readBytesLimit` (512 MiB) are translated and set.
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
public import Proof.path.Join
public import Proof.path.Clean
public import Proof.path.lazybuf__index
public import Proof.path.lazybuf__append
public import Proof.path.lazybuf__string
public import Proof.errors.NewVarCell
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
namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ConnWriteTimeout.init,
        proberInterval.init,
        statusMonitoringInterval.init,
        statusErrorInterval.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

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

/-- `linkHeartbeatMessage = raftpb.Message{Type: raftpb.MsgHeartbeat.Enum()}` (`stream.go`): a message whose type is `MsgHeartbeat`, no other field set; nothing writes it (`hbSt`). -/
axiom linkHeartbeatMessage_init :
    {{ (True : IProp GF) }} (App (Val linkHeartbeatMessage.init) (Val #()))
    {{ RET #(); EtcdGrove.msgOwn (globalAddr linkHeartbeatMessage) DFrac.discard hbSt }}

/-- `linkHeartbeatSize = proto.Size(&linkHeartbeatMessage)` (`stream.go`): the heartbeat's encoding's size (two bytes), an `int` from `0` to below `2^50`; nothing writes it (the stream writer adds it to its metrics). -/
axiom linkHeartbeatSize_init :
    {{ (True : IProp GF) }} (App (Val linkHeartbeatSize.init) (Val #()))
    {{ RET #(); ∃ n : w64, globalAddr linkHeartbeatSize ↦ n ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n < 2 ^ 50⌝ }}

/-- `supportedStream = map[string][]streamType{"2.0.0": {}, "2.1.0": {streamTypeMsgAppV2, streamTypeMessage}, ...}` (`stream.go`): a map of slices; nothing writes the map or its slices. -/
axiom supportedStream_init :
    {{ (True : IProp GF) }} (App (Val supportedStream.init) (Val #()))
    {{ RET #(); ∃ (m : Loc) (M : GMap GoString GoSlice), globalAddr supportedStream ↦ m ∗ m ↦$□ M ∗ □ ∀ (k : GoString) (sl : GoSlice), ⌜M !! k = some sl⌝ -∗ ∃ ts : List GoString, sl ↦*□ ts }}

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

/-- `snapResponseReadTimeout = 5 * time.Second` (`snapshot_sender.go`): some duration, read-only for good. -/
axiom snapResponseReadTimeout_init :
    {{ (True : IProp GF) }} (App (Val snapResponseReadTimeout.init) (Val #()))
    {{ RET #(); ∃ d : time.Duration, globalAddr snapResponseReadTimeout ↦ d }}

/-- `errMemberNotFound = errors.New("member not found")` (`util.go`): some error, read-only for good. -/
axiom errMemberNotFound_init :
    {{ (True : IProp GF) }} (App (Val errMemberNotFound.init) (Val #()))
    {{ RET #(); ∃ e : GoInterface, globalAddr errMemberNotFound ↦ e }}

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]
variable [_root_.Perennial.log.NewModel]

namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := w64) ConnReadTimeout _ as HConnReadTimeout
  wp_apply wp_GlobalAlloc (V := w64) readBytesLimit _ as HreadBytesLimit
  wp_apply wp_GlobalAlloc (V := GoString) RaftSnapshotPrefix _ as HRaftSnapshotPrefix
  wp_apply wp_GlobalAlloc (V := GoString) RaftStreamPrefix _ as HRaftStreamPrefix
  wp_apply wp_GlobalAlloc (V := GoString) ProbingPrefix _ as HProbingPrefix
  wp_apply wp_GlobalAlloc (V := GoString) RaftPrefix _ as HRaftPrefix
  wp_apply (_root_.Perennial.net.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd30⟩
  wp_apply (_root_.Perennial.net.url.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd29⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.transport.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd28⟩
  wp_apply (_root_.Perennial.github_com.Masterminds.semver.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd27⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.httputil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd26⟩
  wp_apply (_root_.Perennial.github_com.xiang90.probing.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd25⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3 _root_.Perennial.go_etcd_io.raft.v3.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3 _root_.Perennial.go_etcd_io.raft.v3.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (_root_.Perennial.golang_org.x.time.rate.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.pbutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.ioutil.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.types.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.version.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.github_com.dustin.go_humanize.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.path.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.net.http.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of RaftPrefix))
  -- translated initializer of ProbingPrefix))
  try wp_auto
  wp_apply (wp_slice_literal (l := [go!"/raft", go!"probing"])); isplitr; (· ipureintro; rfl); iintro %pjP ⟨SjP, -⟩
  try wp_auto
  wp_apply (EtcdGrove.path.Join.wp_proof (EtcdGrove.path.Clean.wp_proof EtcdGrove.path.lazybuf.index.wp_proof EtcdGrove.path.lazybuf.append.wp_proof EtcdGrove.path.lazybuf.string.wp_proof)) _ [go!"/raft", go!"probing"] _ (by decide) $$ [$SjP] as %rjP ⟨%HjP, -⟩
  subst HjP
  rw [show EtcdGrove.path.joinModel [go!"/raft", go!"probing"] = go!"/raft/probing" from by decide]
  try wp_auto
  -- translated initializer of RaftStreamPrefix))
  try wp_auto
  wp_apply (wp_slice_literal (l := [go!"/raft", go!"stream"])); isplitr; (· ipureintro; rfl); iintro %pjS ⟨SjS, -⟩
  try wp_auto
  wp_apply (EtcdGrove.path.Join.wp_proof (EtcdGrove.path.Clean.wp_proof EtcdGrove.path.lazybuf.index.wp_proof EtcdGrove.path.lazybuf.append.wp_proof EtcdGrove.path.lazybuf.string.wp_proof)) _ [go!"/raft", go!"stream"] _ (by decide) $$ [$SjS] as %rjS ⟨%HjS, -⟩
  subst HjS
  rw [show EtcdGrove.path.joinModel [go!"/raft", go!"stream"] = go!"/raft/stream" from by decide]
  try wp_auto
  -- translated initializer of RaftSnapshotPrefix))
  try wp_auto
  wp_apply (wp_slice_literal (l := [go!"/raft", go!"snapshot"])); isplitr; (· ipureintro; rfl); iintro %pjN ⟨SjN, -⟩
  try wp_auto
  wp_apply (EtcdGrove.path.Join.wp_proof (EtcdGrove.path.Clean.wp_proof EtcdGrove.path.lazybuf.index.wp_proof EtcdGrove.path.lazybuf.append.wp_proof EtcdGrove.path.lazybuf.string.wp_proof)) _ [go!"/raft", go!"snapshot"] _ (by decide) $$ [$SjN] as %rjN ⟨%HjN, -⟩
  subst HjN
  rw [show EtcdGrove.path.joinModel [go!"/raft", go!"snapshot"] = go!"/raft/snapshot" from by decide]
  try wp_auto
  wp_apply (errorsNewVarsInit errIncompatibleVersion.init errIncompatibleVersion go!"incompatible version" (by mem_tac))
    as ⟨%xerrIncompatibleVersion, HerrIncompatibleVersion, #MerrIncompatibleVersion, #CerrIncompatibleVersion⟩
  wp_apply (errorsNewVarsInit ErrClusterIDMismatch.init ErrClusterIDMismatch go!"cluster ID mismatch" (by mem_tac))
    as ⟨%xErrClusterIDMismatch, HErrClusterIDMismatch, #MErrClusterIDMismatch, #CErrClusterIDMismatch⟩
  wp_apply activePeers_init as ⟨%vactivePeers, HactivePeers, #LactivePeers⟩
  wp_apply disconnectedPeers_init as ⟨%vdisconnectedPeers, HdisconnectedPeers, #LdisconnectedPeers⟩
  wp_apply sentBytes_init as ⟨%vsentBytes, HsentBytes, #LsentBytes⟩
  wp_apply receivedBytes_init as ⟨%vreceivedBytes, HreceivedBytes, #LreceivedBytes⟩
  wp_apply sentFailures_init as ⟨%vsentFailures, HsentFailures, #LsentFailures⟩
  wp_apply recvFailures_init as ⟨%vrecvFailures, HrecvFailures, #LrecvFailures⟩
  wp_apply snapshotSend_init as ⟨%vsnapshotSend, HsnapshotSend, #LsnapshotSend⟩
  wp_apply snapshotSendInflights_init as ⟨%vsnapshotSendInflights, HsnapshotSendInflights, #LsnapshotSendInflights⟩
  wp_apply snapshotSendFailures_init as ⟨%vsnapshotSendFailures, HsnapshotSendFailures, #LsnapshotSendFailures⟩
  wp_apply snapshotSendSeconds_init as ⟨%vsnapshotSendSeconds, HsnapshotSendSeconds, #LsnapshotSendSeconds⟩
  wp_apply snapshotReceive_init as ⟨%vsnapshotReceive, HsnapshotReceive, #LsnapshotReceive⟩
  wp_apply snapshotReceiveInflights_init as ⟨%vsnapshotReceiveInflights, HsnapshotReceiveInflights, #LsnapshotReceiveInflights⟩
  wp_apply snapshotReceiveFailures_init as ⟨%vsnapshotReceiveFailures, HsnapshotReceiveFailures, #LsnapshotReceiveFailures⟩
  wp_apply snapshotReceiveSeconds_init as ⟨%vsnapshotReceiveSeconds, HsnapshotReceiveSeconds, #LsnapshotReceiveSeconds⟩
  wp_apply rttSec_init as ⟨%vrttSec, HrttSec⟩
  -- translated initializer of readBytesLimit))
  wp_apply (errorsNewVarsInit ErrExceedSizeLimit.init ErrExceedSizeLimit go!"rafthttp: error limit exceeded" (by mem_tac))
    as ⟨%xErrExceedSizeLimit, HErrExceedSizeLimit, #MErrExceedSizeLimit, #CErrExceedSizeLimit⟩
  -- translated initializer of ConnReadTimeout))
  simp only [DefaultConnReadTimeout]
  try wp_auto
  wp_apply (opaqueInitsOk ConnWriteTimeout.init (by mem_tac))
  wp_apply (errorsNewVarsInit errStopped.init errStopped go!"stopped" (by mem_tac))
    as ⟨%xerrStopped, HerrStopped, #MerrStopped, #CerrStopped⟩
  wp_apply (opaqueInitsOk proberInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk statusMonitoringInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk statusErrorInterval.init (by mem_tac))
  wp_apply snapResponseReadTimeout_init as ⟨%dsnapResponseReadTimeout, HsnapResponseReadTimeout⟩
  wp_apply (errorsNewVarsInit errUnsupportedStreamType.init errUnsupportedStreamType go!"unsupported stream type" (by mem_tac))
    as ⟨%xerrUnsupportedStreamType, HerrUnsupportedStreamType, #MerrUnsupportedStreamType, #CerrUnsupportedStreamType⟩
  wp_apply supportedStream_init as ⟨%msupportedStream, %MsupportedStream, HsupportedStream, #MMsupportedStream, #MEsupportedStream⟩
  wp_apply linkHeartbeatMessage_init as #HlinkHeartbeatMessage
  wp_apply linkHeartbeatSize_init as ⟨%nlinkHeartbeatSize, HlinkHeartbeatSize, %BlinkHeartbeatSize⟩
  wp_apply (errorsNewVarsInit errMemberRemoved.init errMemberRemoved go!"the member has been permanently removed from the cluster" (by mem_tac))
    as ⟨%xerrMemberRemoved, HerrMemberRemoved, #MerrMemberRemoved, #CerrMemberRemoved⟩
  wp_apply errMemberNotFound_init as ⟨%eerrMemberNotFound, HerrMemberNotFound⟩
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  -- translated initializer of RaftPrefix))
  -- translated initializer of RaftPrefix))
  -- translated initializer of RaftPrefix))
  ipersist HerrMemberNotFound
  ipersist HsnapResponseReadTimeout
  ipersist HsnapshotSend
  ipersist HsnapshotSendInflights
  ipersist HsnapshotSendFailures
  ipersist HsnapshotSendSeconds
  ipersist HsnapshotReceive
  ipersist HsnapshotReceiveInflights
  ipersist HsnapshotReceiveFailures
  ipersist HsnapshotReceiveSeconds
  ipersist HreceivedBytes
  ipersist HrecvFailures
  ipersist HsentBytes
  ipersist HsentFailures
  ipersist HactivePeers
  ipersist HdisconnectedPeers
  ipersist HrttSec
  ipersist HErrExceedSizeLimit
  ipersist HerrIncompatibleVersion
  ipersist HErrClusterIDMismatch
  ipersist HerrStopped
  ipersist HerrMemberRemoved
  ipersist HRaftPrefix
  ipersist HProbingPrefix
  ipersist HRaftStreamPrefix
  ipersist HRaftSnapshotPrefix
  ipersist HConnReadTimeout
  ipersist HlinkHeartbeatSize
  ipersist HreadBytesLimit
  ipersist HerrUnsupportedStreamType
  ipersist HsupportedStream
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  isplitr
  · simp only [EtcdGrove.errorsNewVar]; iframe #
  isplitr
  · iexact HlinkHeartbeatMessage
  isplitr
  · iexact HRaftPrefix
  isplitr
  · iexact HProbingPrefix
  isplitr
  · iexact HRaftStreamPrefix
  isplitr
  · iexact HRaftSnapshotPrefix
  simp only [EtcdGrove.errorsNewVar, EtcdGrove.errVarCells, EtcdGrove.errVarCell]
  iframe #
  try (ipureintro; exact BlinkHeartbeatSize)

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

end init

end Perennial
