/-
Package initialization instances for the packages the apply thread's translation
(`server/v3/etcdserver`, `EtcdCache/Code/go_etcd_io/etcd/server/v3/etcdserver.lean`) reaches,
beyond those of `Cache/Base.lean` (protobuf, `etcdserverpb`, ...), `Server/Base.lean`
(`cindex`, `schema`; `backend`, `verify`, bbolt in `storage/backend/Base.lean`) and mvcc's `Base.lean` (`storage/mvcc`, with the
facts of its initializer the KV core's proofs use, `pkg/v3/traceutil`, `server/v3/lease`,
`pkg/v3/schedule`, prometheus; 2026-10-10: the three were here too, as `True`, until the
mvcc translation got bodies and `storage/mvcc`'s instance needed prometheus's). Generated
by a script from the translation's `PkgInfo` imports.

As there, these are assumptions about package initialization, not proved from
`initialize'`. They are `True` (the packages are translated names-only or types-only), but the
server's own (`srvInit`, 2026-10-12: the request path's metrics, `traceutil.Tracer` and error
variables).
`etcdserver/errors`' (`ErrNoSpace`, which the entry applier compares the applier's error
with) is in its own `errors/Base.lean` (2026-10-11: moved there, unchanged, for the server's
txn package, which imports it without the apply thread's translation). The instances of the
packages the server's `apply` package reaches (`apply` itself, `raftpb`, `pbutil`, `wait`,
`auth`, `v3alarm`, `membership`, `storage`, `client/pkg/v3/types`) are in `apply/Base.lean`
(2026-10-12: moved there, unchanged but for `apply`'s, which now states the package's facts,
for the apply package, which must not import the server's translation). Those of `config`, `snap`
and `config`'s imports (`otelgrpc`, `crypto/tls`, `transport`, `featuregate`, `v3discovery`) are
there too since D22 S-f (2026-10-19: `storage`, whose instance is there, imports `config` and `snap`
for `OpenSnapshotBackend`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.raft.v3.InvPbMsg

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

namespace net.http

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

end net.http

-- `go-humanize`: mvcc's `Base.lean` (2026-10-13: mvcc's compaction calls `humanize.Bytes`).

-- zap, zapcore, protoreflect and proto: `Proof/go_etcd_io/etcd/cache/v3/Base.lean` (clientv3
-- imports them too).

-- names only (stage R8b of the raft v3.7 retarget, 2026-10-16): the packages the raft wrapper's
-- construction names (`newRaftNode`'s dead logger branch, the WAL `bootstrappedRaft.newRaftNode`
-- wraps); `logutil`'s instance is in `cache/v3/Base.lean` (item 5: `clientv3` imports it).

namespace go_etcd_io.etcd.server.v3.storage.wal

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.wal

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v2stats

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v2stats

-- names only (D21 M2, 2026-10-19): `Process`'s `403` errors (`httptypes.NewHTTPError`)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.types

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.types :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.types :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.types

-- the names-only packages of `rafthttp.Transport`'s fields (unit N4, 2026-10-17)
namespace golang_org.x.time.rate

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.golang_org.x.time.rate :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.golang_org.x.time.rate :=
  build_get_is_pkg_init_wf

end golang_org.x.time.rate

namespace github_com.xiang90.probing

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.xiang90.probing :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.xiang90.probing :=
  build_get_is_pkg_init_wf

end github_com.xiang90.probing

-- (D38, rafthttp's stage 1: the packages its message path names, names only)
namespace internal.bytealg

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.bytealg :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.bytealg :=
  build_get_is_pkg_init_wf

end internal.bytealg

namespace path

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.path :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.path :=
  build_get_is_pkg_init_wf

end path

namespace go_etcd_io.etcd.pkg.v3.ioutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.ioutil

namespace go_etcd_io.etcd.pkg.v3.httputil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.httputil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.httputil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.httputil

-- (after `snap`, which it imports since 2026-10-12: the `Transporter` interface)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

/-- The state of `linkHeartbeatMessage` (`raftpb.Message{Type: raftpb.MsgHeartbeat.Enum()}`). -/
def hbSt : EtcdGrove.MsgSt :=
  ⟨⟨EtcdGrove.MsgHeartbeat, 0, 0, 0, 0, 0, 0, 0, false, 0⟩, [], none, [], []⟩

/-- rafthttp's package fact (2026-10-22, rafthttp stage 3): `ErrExceedSizeLimit`
(`msg_codec.go`, `errors.New`), the message decoder's error for a message over its limit, holds a
non-nil error; `linkHeartbeatMessage` (`stream.go`), which the msgappv2 decoder clones for a
heartbeat frame, is a heartbeat with no other field set, read-only for good (no code writes it);
(2026-10-23) `RaftPrefix` (`http.go`), the pipeline's path, is `"/raft"`, read-only for good,
and (2026-10-24) `ProbingPrefix`, `RaftStreamPrefix` and `RaftSnapshotPrefix` its `probing`,
`stream` and `snapshot` subpaths;
(stage 5b) `ConnReadTimeout` (`peer.go`) is five seconds, read-only for good. -/
abbrev rafthttpInit : IProp GF :=
  iprop(EtcdGrove.errorsNewVar ErrExceedSizeLimit go!"rafthttp: error limit exceeded" ∗
    EtcdGrove.msgOwn (globalAddr linkHeartbeatMessage) DFrac.discard hbSt ∗
    -- (2026-10-23, rafthttp stage 4) the pipeline's path (`http.go`, translated)
    globalAddr RaftPrefix ↦□ go!"/raft" ∗
    -- (2026-10-24, rafthttp stage 6d) the handlers' and the streams' paths (`http.go`,
    -- translated: `path.Join(RaftPrefix, ...)`)
    globalAddr ProbingPrefix ↦□ go!"/raft/probing" ∗
    globalAddr RaftStreamPrefix ↦□ go!"/raft/stream" ∗
    globalAddr RaftSnapshotPrefix ↦□ go!"/raft/snapshot" ∗
    -- (2026-10-23) the `errors.New` errors the pipeline answers with or reports
    EtcdGrove.errorsNewVar errIncompatibleVersion go!"incompatible version" ∗
    EtcdGrove.errorsNewVar ErrClusterIDMismatch go!"cluster ID mismatch" ∗
    EtcdGrove.errorsNewVar errStopped go!"stopped" ∗
    EtcdGrove.errorsNewVar errMemberRemoved
      go!"the member has been permanently removed from the cluster" ∗
    -- (2026-10-23) the pipeline's metric vectors (`metrics.go`), with their label names
    (∃ v : Loc, globalAddr receivedBytes ↦□ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝) ∗
    (∃ v : Loc, globalAddr recvFailures ↦□ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝) ∗
    (∃ v : Loc, globalAddr sentBytes ↦□ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝) ∗
    (∃ v : Loc, globalAddr sentFailures ↦□ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝) ∗
    -- (2026-10-23, rafthttp stage 4d) the peer status's metric vectors (`metrics.go`)
    (∃ v : Loc, globalAddr activePeers ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"Local", go!"Remote"]⌝) ∗
    (∃ v : Loc, globalAddr disconnectedPeers ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"Local", go!"Remote"]⌝) ∗
    -- (2026-10-23, rafthttp stage 5b) the stream writer's heartbeat period's base (`peer.go`,
    -- translated): `DefaultConnReadTimeout`, five seconds, read-only for good (tests change it)
    globalAddr ConnReadTimeout ↦□ (W64 5000000000) ∗
    -- (2026-10-23, rafthttp stage 5b) the heartbeat's size (`stream.go`, untranslated), which the
    -- stream writer counts: some `int`, read-only for good
    (∃ n : w64, globalAddr linkHeartbeatSize ↦□ n ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n < 2 ^ 50⌝) ∗
    -- (2026-10-23, rafthttp stage 5c) the message decoder's limit (`msg_codec.go`, translated):
    -- 512 MiB, read-only for good
    globalAddr readBytesLimit ↦□ (W64 536870912) ∗
    -- (2026-10-23, rafthttp stage 5c) the stream reader's dial error for a stream type an older
    -- peer does not support (`stream.go`, `fmt.Errorf` without verbs: an `errors.New` error)
    EtcdGrove.errorsNewVar errUnsupportedStreamType go!"unsupported stream type" ∗
    -- (2026-10-23, rafthttp stage 6c) the probers' round-trip histogram (`metrics.go`, untranslated):
    -- some pointer, read-only for good (`AddPeer` hands it to the prober)
    (∃ v : Loc, globalAddr rttSec ↦□ v) ∗
    -- (2026-10-24, rafthttp stage 6e) the cells of the errors `checkPostResponse` returns, which
    -- tell them from `errMemberRemoved` (`errVarCell`; D19k)
    EtcdGrove.errVarCells [(errIncompatibleVersion, go!"incompatible version"),
      (ErrClusterIDMismatch, go!"cluster ID mismatch"),
      (errMemberRemoved, go!"the member has been permanently removed from the cluster")] ∗
    -- (2026-10-24, rafthttp stage 6e) the stream types each version supports (`stream.go`,
    -- untranslated): a map of slices, read-only for good (the stream reader's
    -- `checkStreamSupport` looks a peer's version up)
    (∃ (m : Loc) (M : GMap GoString GoSlice), globalAddr supportedStream ↦□ m ∗ m ↦$□ M ∗
      □ ∀ (k : GoString) (sl : GoSlice), ⌜M !! k = some sl⌝ -∗ ∃ ts : List GoString, sl ↦*□ ts) ∗
    -- (2026-10-24, rafthttp stage 7d) `errStopped`'s cell, which tells it from `errMemberRemoved`
    -- (the snapshot sender's `post` returns it)
    EtcdGrove.errVarCells [(errStopped, go!"stopped")] ∗
    -- (2026-10-24, rafthttp stage 7d) the snapshot sender's and handler's metric vectors
    -- (`metrics.go`), with their label names
    (∃ v : Loc, globalAddr snapshotSend ↦□ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝) ∗
    (∃ v : Loc, globalAddr snapshotSendInflights ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝) ∗
    (∃ v : Loc, globalAddr snapshotSendFailures ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝) ∗
    (∃ v : Loc, globalAddr snapshotSendSeconds ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"To"]⌝) ∗
    (∃ v : Loc, globalAddr snapshotReceive ↦□ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝) ∗
    (∃ v : Loc, globalAddr snapshotReceiveInflights ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝) ∗
    (∃ v : Loc, globalAddr snapshotReceiveFailures ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝) ∗
    (∃ v : Loc, globalAddr snapshotReceiveSeconds ↦□ v ∗
      ⌜EtcdGrove.prometheus.vecLabels v [go!"From"]⌝) ∗
    -- (2026-10-24, rafthttp stage 7d) the snapshot sender's response-read timeout
    -- (`snapshot_sender.go`, untranslated): some duration, read-only for good
    (∃ d : time.Duration, globalAddr snapResponseReadTimeout ↦□ d) ∗
    -- (2026-10-24, rafthttp stage 7d) `SendSnapshot`'s error for a message without a peer
    -- (`util.go`, untranslated): some error, read-only for good
    (∃ e : GoInterface, globalAddr errMemberNotFound ↦□ e))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp :=
  define_is_pkg_init rafthttpInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

-- etcdserver/errors: its own `errors/Base.lean` (imported above; the server txn package needs it
-- without the apply thread's translation).

-- raft v3.7 (`go_etcd_io.raft.v3`): raft's `Base.lean` states its instance (`isInitialized`,
-- with `emptyState`), imported through the apply package's `Base`, since stage R6 of the raft
-- v3.7 retarget (2026-10-16; until then `raftInit` here, the names-only dependency's).

namespace go_etcd_io.etcd.pkg.v3.contention

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.contention :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.contention :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.contention

namespace go_etcd_io.etcd.pkg.v3.idutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.idutil

-- `pkg/v3/notify`: `apply/Base.lean` (2026-10-14, unit P1b: `membership` imports it)

-- `api/v3/version`: `server/v3/lease/Base.lean` (2026-10-13, unit 9: the lessor's
-- `shouldPersistCheckpoints` reads its `V3_6`)

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

-- `strconv` (Perennial's translation, names only: `FormatBool`, the request path's metrics
-- labels, and `FormatUint`, the read loop's trace field; no variable read): raft's `Base.lean`
-- states its instance (imported through the apply package's `Base`, stage R6).

namespace go_etcd_io.etcd.server.v3.etcdserver.read

/-- **`context.DeadlineExceeded` holds a struct error the gRPC layer can take** (a package fact
the read package states, as the server states its foreign errors in `srvErrVars`; 2026-10-13, the
request path's unit 4a: `LinearizableReadNotify` returns a done context's `Err()`, which is
`Canceled` or `DeadlineExceeded`, `context.ErrDone`): Go's `deadlineExceededError{}` (an empty
struct, not a pointer: `context.go`'s `var DeadlineExceeded error = deadlineExceededError{}`), whose
method set is `Error`, `Timeout`, `Temporary` (no `Is`, `As` or `Unwrap`: a leaf), comparable (an
empty struct: `==` on it does not panic, a safe map key), and whose `Error()` returns. Method sets
are uninterpreted in the semantics, so this is stated, as `srvErrVars`' `errLeaf`. -/
abbrev ctxDeadlineLeaf : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.isLeafError e ∧
      methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) ∧
      (∀ T, e.ty ≠ go.GoType.PointerType T) ∧
      SafeMapKey (GF := GF) go.error (GoInterface.ok e)⌝ ∗
    EtcdGrove.errMsgOk e)

/-- **The read package's facts** (`server/v3/etcdserver/read`; 2026-10-13, the request path's unit
4a; `True` until then): its metrics `slowReadIndex` and `readIndexFailed` hold fixed counters
(`prometheus.NewCounter` at init; mvcc's `counterSpec`), `readIndexRetryTime` some duration (`500 *
time.Millisecond`), and the error variables it returns or compares with hold `errors.New` errors
(`EtcdGrove.errVarLeaf`): `etcdserver/errors`' `ErrStopped`, `ErrLeaderChanged`, `ErrTimeout`, raft's
`ErrStopped` (`errors.Is`'s target in `sendReadIndex` and `isStopped`), and `context.Canceled`; and
`context.DeadlineExceeded`'s (`ctxDeadlineLeaf`). An assumption about those packages'
initialization, stated here for the errors of other packages, as `srvErrVars`. -/
abbrev readInit : IProp GF :=
  iprop((∃ c : GoInterfaceOk, globalAddr slowReadIndex ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr readIndexFailed ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c) ∗
    (∃ d : _root_.Perennial.time.Duration, globalAddr readIndexRetryTime ↦□ d) ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrLeaderChanged ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout ∗
    EtcdGrove.errVarLeaf go_etcd_io.raft.v3.ErrStopped ∗
    EtcdGrove.errVarLeaf _root_.Perennial.context.Canceled ∗
    ctxDeadlineLeaf)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read :=
  define_is_pkg_init readInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.read

-- `server/v3/features` (names only, with the two feature constants the request path reads)
namespace go_etcd_io.etcd.server.v3.features

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.features

namespace go_etcd_io.etcd.server.v3.etcdserver

/-- **The error variables the request path returns** (`v3_server.go`, `server.go`'s
`parseProposeCtxErr`) hold `errors.New` errors (`EtcdGrove.errVarLeaf`): `etcdserver/errors`'
`ErrTooManyRequests` (the request limit), `ErrRequestTooLarge` (`MaxRequestBytes`),
`ErrStopped` (the server stopped while a proposal waited), `ErrCanceled`, `ErrTimeout`,
`ErrTimeoutDueToLeaderFail`, `ErrTimeoutDueToConnectionLost` (a proposal's context done),
`auth.ErrAuthOldRevision` (`doSerialize`'s stale token), and raft's `ErrProposalDropped` (the
result raft's `node.Propose` answers a dropped proposal with, `stepErr`; 2026-10-16, stage R7c).
An assumption about those packages' initialization (each `var X = errors.New(...)`), stated here
rather than in their packages' facts, as the apply package's `applyErrVars`. And (2026-10-12,
the request path's unit 3b) a
method-set fact: `*errors.errorString` (the dynamic type of an `errors.New` error and, in
Perennial's model, of a `fmt.Errorf` error: `mvcc.errorfIs`) has no `Is`, `As` or `Unwrap`
method (`EtcdGrove.errLeaf`), as Go's `errors` package defines it (its only method is
`Error()`); method sets are uninterpreted in the semantics (as Perennial's
`context.ErrorStringIsError`), so the read side's context errors need it to be errors the gRPC
layer can take (`applyErrIs`). -/
abbrev srvErrVars : IProp GF :=
  iprop(EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTooManyRequests ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrRequestTooLarge ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrStopped ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrCanceled ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeout ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToLeaderFail ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutDueToConnectionLost ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.auth.ErrAuthOldRevision ∗
    EtcdGrove.errVarLeaf go_etcd_io.raft.v3.ErrProposalDropped ∗
    ⌜∀ x : Loc, EtcdGrove.errLeaf
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩⌝)

/-- **The request path's part of the server package's facts** (2026-10-12; `True` until then): the
metrics `metrics.go` declares and the request path updates (`requestDurationSec`, a
`*prometheus.HistogramVec` with its label names, whose `WithLabelValues` is the trust boundary; `proposalsFailed`, a
`Counter`, and `proposalsPending`, a `Gauge`, with mvcc's `counterSpec`/`gaugeSpec` as their
contracts), `traceutil.Tracer` (a fixed tracer, stated here rather than in `traceutil`'s facts:
its `Start` is the trust boundary, `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Tracer__Start.lean`),
and the error variables (`srvErrVars`). -/
abbrev srvReqInit : IProp GF :=
  iprop((∃ hv : Loc, globalAddr requestDurationSec ↦□ hv ∗
      ⌜EtcdGrove.prometheus.vecLabels hv [go!"type", go!"success"]⌝) ∗
    (∃ c : GoInterfaceOk, globalAddr proposalsFailed ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c) ∗
    (∃ g : GoInterfaceOk, globalAddr proposalsPending ↦□ GoInterface.ok g ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec g) ∗
    (∃ tr : GoInterfaceOk, globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr) ∗
    srvErrVars)

/-- A prometheus `Gauge` as the raft wrapper uses it: `Set(x)` returns. -/
def gaugeSetSpec (g : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods g.ty go!"Set" g.v)) (Val #x))
    {{ RET #(); True }}))

instance gaugeSetSpec_persistent (g : GoInterfaceOk) :
    Persistent (gaugeSetSpec (GF := GF) g) := by
  unfold gaugeSetSpec; infer_instance

/-- The raft wrapper's part of the server's package facts (2026-10-12, `raft.go`): the metrics of
`metrics.go` the `Ready` loop updates each hold a fixed gauge (`hasLeader`, `isLeader`,
`proposalsCommitted`: `Set`) or counter (`leaderChanges`, `heartbeatSendFailures`: `Inc`, mvcc's
`counterSpec`); and the gauge vectors the construction uses (`serverFeatureEnabled`, `serverID`;
unit N4, 2026-10-17), with their label names (D19l (iii), 2026-10-18). -/
abbrev srvRaftInit : IProp GF :=
  iprop((∃ g : GoInterfaceOk, globalAddr hasLeader ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ g : GoInterfaceOk, globalAddr isLeader ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ g : GoInterfaceOk, globalAddr proposalsCommitted ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ c : GoInterfaceOk, globalAddr leaderChanges ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr heartbeatSendFailures ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c) ∗
    -- the construction's metrics (unit N4, 2026-10-17: `NewServer`'s `addFeatureGateMetrics(…,
    -- serverFeatureEnabled)` and `serverID.With(…)`): two fixed gauge vectors
    (∃ gv : Loc, globalAddr serverFeatureEnabled ↦□ gv ∗
      ⌜EtcdGrove.prometheus.vecLabels gv [go!"name", go!"stage"]⌝) ∗
    (∃ gv : Loc, globalAddr serverID ↦□ gv ∗ ⌜EtcdGrove.prometheus.vecLabels gv [go!"server_id"]⌝) ∗
    -- (D19r (C), 2026-10-18) the raft status's mutex over its function (`raft.go`; the raft
    -- wrapper's `rnRaftStatusOk`), allocated and initialized by the package's initializer
    sync.isMutex (globalAddr raftStatusMu) iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f))

/-- The apply loop's part of the server's package facts (2026-10-13, the request path's unit 4b,
`applyAll`): the metric `proposalsApplied` holds a fixed gauge (`Set`), and `schema.AllBuckets`
(the buckets `VerifyBackendConsistency` checks; stated here rather than in `schema`'s facts, as
`srvErrVars` states other packages' errors) some slice; (D22 receiver epochs, S8c, 2026-10-24)
`applySnapshotInProgress` a fixed gauge (`applySnapshot`'s `Inc`/`Dec`). -/
abbrev srvApplyLoopInit : IProp GF :=
  iprop((∃ g : GoInterfaceOk, globalAddr proposalsApplied ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ sl : GoSlice, globalAddr go_etcd_io.etcd.server.v3.storage.schema.AllBuckets ↦□ sl) ∗
    -- (D22 receiver epochs, S8c, 2026-10-24) `applySnapshot`'s gauge (`Inc`, `Dec`)
    (∃ g : GoInterfaceOk, globalAddr applySnapshotInProgress ↦□ GoInterface.ok g ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec g))

/-- **The server package's facts**: the raft wrapper's (`srvRaftInit`), the request path's
(`srvReqInit`), merged 2026-10-12, and the apply loop's (`srvApplyLoopInit`, 2026-10-13). All are
abbreviations, so `icases` sees through them: a proof destructs `srvInit` as `⟨⟨raft wrapper's⟩,
⟨request path's⟩, ⟨apply loop's⟩⟩`. -/
abbrev srvInit : IProp GF :=
  iprop(srvRaftInit ∗ srvReqInit ∗ srvApplyLoopInit)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver :=
  define_is_pkg_init srvInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver

end init

end Perennial
