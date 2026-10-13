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
for the apply package, which must not import the server's translation).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

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

namespace net.http

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

end net.http

-- `go-humanize`: mvcc's `Base.lean` (2026-10-13: mvcc's compaction calls `humanize.Bytes`).

-- zap, zapcore, protoreflect and proto: `Proof/go_etcd_io/etcd/cache/v3/Base.lean` (clientv3
-- imports them too).

namespace go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc

namespace go_etcd_io.etcd.client.pkg.v3.transport

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.transport

namespace go_etcd_io.etcd.pkg.v3.featuregate

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.featuregate

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery

namespace go_etcd_io.etcd.server.v3.config

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.config

namespace go_etcd_io.etcd.server.v3.etcdserver.api.snap

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.snap

-- (after `snap`, which it imports since 2026-10-12: the `Transporter` interface)
namespace go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp

-- etcdserver/errors: its own `errors/Base.lean` (imported above; the server txn package needs it
-- without the apply thread's translation).

namespace go_etcd_io.raft.v3

/-- raft v3.7's package facts (2026-10-12, for the raft wrapper's `IsEmptyHardState`): its
`emptyState` holds for good a pointer to a `HardState` with every field absent
(`emptyState = &pb.HardState{}`). -/
def raftInit : IProp GF :=
  iprop(∃ e : Loc, globalAddr emptyState ↦□ e ∗ ⌜e ≠ null⌝ ∗
    structFieldRef raftpb.HardState go!"Term" e ↦□ (null : Loc) ∗
    structFieldRef raftpb.HardState go!"Vote" e ↦□ (null : Loc) ∗
    structFieldRef raftpb.HardState go!"Commit" e ↦□ (null : Loc))

instance raftInit_persistent : Persistent (raftInit (GF := GF)) := by
  unfold raftInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  define_is_pkg_init raftInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  build_get_is_pkg_init_wf

end go_etcd_io.raft.v3

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

namespace go_etcd_io.etcd.pkg.v3.notify

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.notify

-- `api/v3/version`: `server/v3/lease/Base.lean` (2026-10-13, unit 9: the lessor's
-- `shouldPersistCheckpoints` reads its `V3_6`)

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v2stats

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v2stats

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

-- `strconv` (Perennial's translation, names only: `FormatBool`, the request path's metrics
-- labels, and `FormatUint`, the read loop's trace field; no variable read). Raft's `Base.lean` states the same instance for raft's proofs,
-- which no module imports with the server's.
namespace strconv

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.strconv :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.strconv :=
  build_get_is_pkg_init_wf

end strconv

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
`ErrTimeoutDueToLeaderFail`, `ErrTimeoutDueToConnectionLost` (a proposal's context done), and
`auth.ErrAuthOldRevision` (`doSerialize`'s stale token). An assumption about those packages'
initialization (each `var X = errors.New(...)`), stated here rather than in their packages'
facts, as the apply package's `applyErrVars`. And (2026-10-12, the request path's unit 3b) a
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
    ⌜∀ x : Loc, EtcdGrove.errLeaf
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩⌝)

/-- **The request path's part of the server package's facts** (2026-10-12; `True` until then): the
metrics `metrics.go` declares and the request path updates (`requestDurationSec`, a
`*prometheus.HistogramVec`, whose `WithLabelValues` is the trust boundary; `proposalsFailed`, a
`Counter`, and `proposalsPending`, a `Gauge`, with mvcc's `counterSpec`/`gaugeSpec` as their
contracts), `traceutil.Tracer` (a fixed tracer, stated here rather than in `traceutil`'s facts:
its `Start` is the trust boundary, `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Tracer__Start.lean`),
and the error variables (`srvErrVars`). -/
abbrev srvReqInit : IProp GF :=
  iprop((∃ hv : Loc, globalAddr requestDurationSec ↦□ hv) ∗
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
`counterSpec`). -/
abbrev srvRaftInit : IProp GF :=
  iprop((∃ g : GoInterfaceOk, globalAddr hasLeader ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ g : GoInterfaceOk, globalAddr isLeader ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ g : GoInterfaceOk, globalAddr proposalsCommitted ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ c : GoInterfaceOk, globalAddr leaderChanges ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr heartbeatSendFailures ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec c))

instance srvRaftInit_persistent : Persistent (srvRaftInit (GF := GF)) := by
  unfold srvRaftInit go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec; infer_instance

/-- The apply loop's part of the server's package facts (2026-10-13, the request path's unit 4b,
`applyAll`): the metric `proposalsApplied` holds a fixed gauge (`Set`), and `schema.AllBuckets`
(the buckets `VerifyBackendConsistency` checks; stated here rather than in `schema`'s facts, as
`srvErrVars` states other packages' errors) some slice. -/
abbrev srvApplyLoopInit : IProp GF :=
  iprop((∃ g : GoInterfaceOk, globalAddr proposalsApplied ↦□ GoInterface.ok g ∗ gaugeSetSpec g) ∗
    (∃ sl : GoSlice, globalAddr go_etcd_io.etcd.server.v3.storage.schema.AllBuckets ↦□ sl))

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
