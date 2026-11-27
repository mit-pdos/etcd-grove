/-
Package initialization instances for `go.etcd.io/etcd/cache/v3` and the packages it
imports (the counterpart of `Proof/go_etcd_io/raft/v3/Base.lean` for the translation of etcd).

`isPkgInit` of a package includes `isPkgInit` of everything it imports, so every package
reachable from the cache's imports needs an instance. The standard-library ones (`bytes`,
`context`, `errors`, `fmt`, `sync`, `time`) are Perennial's; the etcd, k8s, protobuf, grpc and zap
packages are translated names-only or types-only (`Code/{go_etcd_io/etcd,k8s_io,google_golang_org,go_uber_org}/**.toml`), and their
package facts are `True` except where a proof reads a package-level variable: the
cache's `ErrNotReady` (`fmt.Errorf` at init), `ErrUnsupportedRequest` and
`ErrKeyRangeInvalid`, `ErrCacheTimeout` (`errors.New`), and `rpctypes`' `ErrFutureRev` and
`ErrCompacted` each hold a fixed non-nil error (`globalAddr X ↦□ interface.ok e`, as
Perennial's own packages state their globals), and `ErrCompacted.Error()` returns some string
(`errorStringSpec`: it is an `EtcdError`, whose `Error` returns its description), as do the
cache's `ErrKeyRangeInvalid.Error()` and `ErrUnsupportedRequest.Error()`;
grpc's `EnableTracing` holds `false` for good (`grpcInit`);
`clientv3`'s `noPrefixEnd` points for good to a slice holding the byte `0`. Everything here is an assumption about
package initialization, as in `Proof/go_etcd_io/raft/v3/Base.lean`: nothing proves it from `initialize'`.
-/
module

public import Code.go_etcd_io.etcd.cache.v3
public import GeneratedProof.go_etcd_io.etcd.cache.v3
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.bytes
public import Perennial.Proof.context
public import Perennial.Proof.errors
public import Perennial.Proof.fmt
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.io
public import Perennial.Proof.strings.Base
public import Perennial.Proof.strconv.Base
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init
public import Spec.fmt.ErrorfWrap
public import Proof.go_uber_org.zap.PkgInit
public import Proof.math.rand.Base
public import Net.Proof.net.Base
public import Proof.google_golang_org.grpc.status.StatusRO
public import Proof.google_golang_org.genproto.googleapis.rpc.status.Base
public import Proof.crypto.tls.PkgInit
public import Proof.google_golang_org.protobuf.PkgInit
public import Proof.runtime.InitInv

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.cache.v3

section grpcStatus
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **`err` carries a gRPC status** (pure; grpc-trusted-T, T3, 2026-11-24): a non-nil error whose
dynamic type has grpc's `GRPCStatus() *Status` method, so that `status.FromError` takes it as a status
error (`ok = true`, given `statusErrOk`'s non-nil status: grpc v1.84.0 `status.go:96-127`). What a
caller tells grpc's own errors apart by (the gRPC driver's `errOk`); `*status.Error` is such a type. -/
def hasGRPCStatus (err : GoInterface) : Prop :=
  ∃ e : GoInterfaceOk, err = GoInterface.ok e ∧ methodSet e.ty !! go!"GRPCStatus" =
    some (go.Signature [] false [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])

end grpcStatus

section desc

-- An error's description (D29): the per-run relation `descIs err m` below (errdesc stage 2b, 2026-11-21;
-- until then the pure `errDesc : GoInterface → GoString` of `Proof/google_golang_org/grpc/status/ErrDesc.lean`).

/-- **The refusals** (D29): the descriptions after which the client's retry interceptor sends a
`nonRepeatable` call (a write) again: the auth errors (`shouldRefreshToken`, then
`refreshToken`), the learner's refusal (`isSafeRetry`), grpc's old balancer's "no address" and
"no connection" (`isSafeRetryMutableRPC`). -/
def refusalDescs : List GoString :=
  [go!"etcdserver: invalid auth token", go!"etcdserver: revision of auth store is old",
    go!"etcdserver: user name is empty", go!"etcdserver: rpc not supported for learner",
    go!"there is no address available", go!"there is no connection available"]

theorem mem_refusalDescs_balancer (d : GoString)
    (h : d = go!"there is no address available" ∨ d = go!"there is no connection available") :
    d ∈ refusalDescs := by
  rcases h with rfl | rfl <;> simp [refusalDescs]

/-- **The two read errors' descriptions** (k8s etcd3 stage 7c): `rpctypes.ErrGRPCFutureRev`'s and
`rpctypes.ErrGRPCCompacted`'s (`error.go:32-33`), which the server's `togRPCError` maps mvcc's
`ErrFutureRev` and `ErrCompacted` to, and the client's `rpctypes.ErrFutureRev`/`ErrCompacted` carry. -/
def futureRevDesc : GoString := go!"etcdserver: mvcc: required revision is a future revision"

def compactedDesc : GoString := go!"etcdserver: mvcc: required revision has been compacted"

/-- **A context error's shape** (incomingof Part B, approved by the user 2026-11-17 via etcd-grove-03):
not an `rpctypes.EtcdError` and without an `Is(error) bool` method, as Go's `context.Canceled` (a
`*errors.errorString`) and `context.DeadlineExceeded` (a `deadlineExceededError`) are
(`examples/axiomcx/incomingof-real` `TestRealTypes`). A fact of the type only, the same in every run:
what rules a context error out of `errors.Is(err, <an EtcdError>)` (`errors.IsStatusErr.spec`). -/
def ctxErrShape [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (e : GoInterfaceOk) : Prop :=
  e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty ∧
    methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])

/-- **The type `t` has no grpc `GRPCStatus() *Status` method** (incomingof T8): `status.FromError`
of a leaf error of such a type is no status error (`ok = false`). -/
def noGRPCStatus [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] (t : go.GoType) : Prop :=
  methodSet t !! go!"GRPCStatus" ≠
    some (go.Signature [] false [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])

/-- **Go's two context-error messages** (incomingof Part B, option (a), decided by etcd-grove-03,
2026-11-18): `context.go`'s `Canceled = errors.New("context canceled")` and
`deadlineExceededError.Error()`'s `"context deadline exceeded"` (`examples/axiomcx/incomingof-real`
`TestCtxErrOnlyTwo`). -/
def ctxErrMsg (m : GoString) : Prop :=
  m = go!"context canceled" ∨ m = go!"context deadline exceeded"

end desc

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

-- protobuf-go's packages' instances (names only: `pragma`, `impl`, `protoimpl`, `protoreflect`,
-- `proto`): `Proof/google_golang_org/protobuf/PkgInit.lean` (L1, 2026-11-24)

/-- The map `Event_EventType_name` (`kv.pb.go`, generated by protoc-gen-go) holds: the literal of
its initializer, its keys inserted in the literal's order (`0` first: the order the initializer's
proof inserts them). The trusted model of `Event_EventType.String` reads it (etcd-grove#39,
2026-11-23). -/
def mvccpb.eventTypeNames : GMap w32 GoString :=
  <[W32 1 := go!"DELETE"]> (<[W32 0 := go!"PUT"]> ∅)

/-- **`mvccpb`'s fact** (etcd-grove#39, 2026-11-23; `True` until then): `Event_EventType_name`
holds a map with `mvccpb.eventTypeNames`, both read-only (nothing but the initializer writes the
table). -/
abbrev mvccpbInit : IProp GF :=
  iprop(∃ mp : Loc, globalAddr go_etcd_io.etcd.api.v3.mvccpb.Event_EventType_name ↦□ mp ∗
    mp ↦$□ mvccpb.eventTypeNames)

instance mvccpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  define_is_pkg_init mvccpbInit
instance mvccpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  build_get_is_pkg_init_wf

-- `etcdserverpb` names `membershippb`'s and `authpb`'s messages (2026-10-12: the server's apply
-- package's requests): types and names only, `True` as the others
instance membershippb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.membershippb :=
  define_is_pkg_init iprop(True)
instance membershippb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.membershippb :=
  build_get_is_pkg_init_wf


/-- **`authpb`'s fact** (the auth plan's S4e, 2026-10-24; `authpb.toml`, `etc/gen-init.py`): the
permission type's name map `Permission_Type_name` (a generated `map[int32]string` literal), fixed:
its entries are the three types' names. `RoleGrantPermission` looks the granted type's name up for
its log line (`auth.typeNamesOk`). -/
abbrev authpbInit : IProp GF :=
  iprop(∃ (mp : Loc) (M : GMap w32 GoString),
    globalAddr go_etcd_io.etcd.api.v3.authpb.Permission_Type_name ↦□ mp ∗ mp ↦$□ M ∗
    ⌜M !! (W32 0) = some go!"READ" ∧ M !! (W32 1) = some go!"WRITE" ∧
      M !! (W32 2) = some go!"READWRITE"⌝)

instance authpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb :=
  define_is_pkg_init authpbInit
instance authpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb :=
  build_get_is_pkg_init_wf

-- `initInv` (the init-time invariant): `Proof/runtime/InitInv.lean` (dsv-retire-2, 2026-11-25)

-- grpc's `grpclog` and `grpclog/internal` (types and names only, but `grpclog`'s `cache` and
-- `Component`), before `connectivity`, `credentials`, `health` and grpc, whose `logger`s call
-- `grpclog.Component` at init (phase7-inits batch 2, 2026-11-25; until then in
-- `k8s/.../storage/etcd3/Base.lean`, fact `True`)
instance google_golang_org_grpc_grpclog_internal_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.grpclog.internal :=
  define_is_pkg_init iprop(True)
instance google_golang_org_grpc_grpclog_internal_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.grpclog.internal :=
  build_get_is_pkg_init_wf

namespace google_golang_org.grpc.grpclog

/-- The namespace of `cache`'s invariant. -/
def cacheN : Namespace := nroot.@"grpclogCache"

/-- **`grpclog`'s package fact** (phase7-inits batch 2, 2026-11-25; until then `True`): `cache` holds a
map for good, whose contents (a component's name to its `*componentData`) are in an init-time invariant
(`initInv`): `Component`, which reads and writes the map, is called only by package initializers (the
`logger`s of grpc, `credentials`, `health` and `connectivity`; `Spec/google_golang_org/grpc/grpclog/Component.lean`). -/
def grpclogInit : IProp GF :=
  iprop(∃ (m : Loc) (γI : GName),
    globalAddr _root_.Perennial.google_golang_org.grpc.grpclog.cache ↦□ m ∗
    inv cacheN (initInv (∃ M : GMap GoString Loc, m ↦$ M) γI))

instance grpclogInit_persistent : Persistent (grpclogInit (GF := GF)) := by
  unfold grpclogInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.grpclog :=
  define_is_pkg_init grpclogInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.grpclog :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.grpclog

-- (phase7-inits batch 2) grpc's `connectivity` (types and names only but its `logger`): `State`, the
-- type grpc's `internal.HealthChecker` names; before `internal`
instance grpc_connectivity_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.connectivity :=
  define_is_pkg_init iprop(True)
instance grpc_connectivity_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.connectivity :=
  build_get_is_pkg_init_wf

-- (phase7-inits, 2026-11-25; first phase 7 S2 core, 2026-11-23, for `FromOutgoingContextRaw`) grpc's
-- `internal` (names only but its hook variables), before `metadata`, `codes` and grpc, whose `init`s set
-- them
namespace google_golang_org.grpc.internal

-- `hookN`, `hookInv`, `hookCell`, `hookCells`: `Proof/runtime/InitInv.lean` (dsv-retire-2, 2026-11-25)

/-- The hook variables of type `any` the translated `init`s set: `metadata`'s, `mem`'s and
`internal/mem`'s, `codes`', grpc's (`dialoptions.go`, `rpc_util.go`, `server.go`) and `health`'s. -/
def hooksAny : List GoString :=
  [_root_.Perennial.google_golang_org.grpc.internal.FromOutgoingContextRaw,
   _root_.Perennial.google_golang_org.grpc.internal.SetDefaultBufferPool,
   _root_.Perennial.google_golang_org.grpc.internal.SetBufferPoolingThresholdForTesting,
   _root_.Perennial.google_golang_org.grpc.internal.CanonicalString,
   _root_.Perennial.google_golang_org.grpc.internal.AddGlobalDialOptions,
   _root_.Perennial.google_golang_org.grpc.internal.AddGlobalPerTargetDialOptions,
   _root_.Perennial.google_golang_org.grpc.internal.JoinDialOptions,
   _root_.Perennial.google_golang_org.grpc.internal.DisableGlobalDialOptions,
   _root_.Perennial.google_golang_org.grpc.internal.AcceptCompressors,
   _root_.Perennial.google_golang_org.grpc.internal.GetServerCredentials,
   _root_.Perennial.google_golang_org.grpc.internal.IsRegisteredMethod,
   _root_.Perennial.google_golang_org.grpc.internal.ServerFromContext,
   _root_.Perennial.google_golang_org.grpc.internal.AddGlobalServerOptions,
   _root_.Perennial.google_golang_org.grpc.internal.JoinServerOptions,
   _root_.Perennial.google_golang_org.grpc.internal.XDSFilterWrapperOption,
   _root_.Perennial.google_golang_org.grpc.internal.RegisterClientHealthCheckListener]

/-- The hook variables of function type the translated `init`s set: grpc's `func()`s, `health`'s
`HealthCheckFunc` (an `internal.HealthChecker`) and `balancer`'s `BalancerUnregister` (a `func(string)`). -/
def hooksFunc : List GoString :=
  [_root_.Perennial.google_golang_org.grpc.internal.ClearGlobalDialOptions,
   _root_.Perennial.google_golang_org.grpc.internal.ClearGlobalPerTargetDialOptions,
   _root_.Perennial.google_golang_org.grpc.internal.ClearGlobalServerOptions,
   _root_.Perennial.google_golang_org.grpc.internal.HealthCheckFunc,
   _root_.Perennial.google_golang_org.grpc.internal.BalancerUnregister]

/-- **`internal`'s package fact**: the invariants of its hook cells, which only package initializers
write and no translated code reads (their readers, grpc-go's tests, xds, stats/opentelemetry, orca and
`experimental`, are outside the model; `Code/google_golang_org/grpc/internal.toml`). -/
def internalInit : IProp GF :=
  iprop(hookCells GoInterface hooksAny ∗ hookCells GoFunc hooksFunc)

instance internalInit_persistent : Persistent (internalInit (GF := GF)) := by
  unfold internalInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.internal :=
  define_is_pkg_init internalInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.internal :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.internal

-- `google.golang.org/grpc/metadata` (types and names only), before `grpc`, which imports it
-- (unit W-W: grpc's `ClientStream`/`ServerStream` name `metadata.MD`; moved here from
-- `server/v3/auth/Base.lean`)
namespace google_golang_org.grpc.metadata

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.metadata :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.metadata :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.metadata

-- `net`: the part `Net/`'s translation since the net swap (etcd-dist D2, 2026-11-22), its instance
-- `Net/Proof/net/Base.lean`'s (`isInit`, imported above).

instance grpc_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.credentials :=
  define_is_pkg_init iprop(True)
instance grpc_credentials_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.credentials :=
  build_get_is_pkg_init_wf

-- grpc's `peer` (names only; unit P3a: the retry interceptor's `peer.Peer`), before `grpc`, which
-- imports it since 2026-11-20 (prove-grpcsmall: `grpc.Peer`'s option holds a `*peer.Peer`).
instance grpc_peer_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.peer :=
  define_is_pkg_init iprop(True)
instance grpc_peer_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.peer :=
  build_get_is_pkg_init_wf

-- grpc's `serviceconfig`, `attributes` and `resolver` (types and names only; moved here, before
-- `grpc`, which imports `resolver` since phase 7 S1's dial side, 2026-11-22: `dialOptions.resolvers`)
instance grpc_serviceconfig_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.serviceconfig :=
  define_is_pkg_init iprop(True)
instance grpc_serviceconfig_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.serviceconfig :=
  build_get_is_pkg_init_wf
instance grpc_attributes_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.attributes :=
  define_is_pkg_init iprop(True)
instance grpc_attributes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.attributes :=
  build_get_is_pkg_init_wf
instance grpc_resolver_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.resolver :=
  define_is_pkg_init iprop(True)
instance grpc_resolver_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.resolver :=
  build_get_is_pkg_init_wf

-- grpc's `keepalive` and `stats` (types and names only), before `grpc`, which imports them since
-- phase 7 S1 (2026-11-21: the types of the model's `serverOptions` fields; `stats` moved here from
-- the apply package's `Base.lean`)
instance grpc_keepalive_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.keepalive :=
  define_is_pkg_init iprop(True)
instance grpc_keepalive_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.keepalive :=
  build_get_is_pkg_init_wf
namespace google_golang_org.grpc.stats

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.stats :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.stats :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.stats

-- (phase7-s2a, 2026-11-25; first phase 7 S2, 2026-11-22) `grpc/internal/grpcsync` (types only:
-- `Event`, the type of `Server`'s `quit`/`done`), before grpc's, which imports it
namespace google_golang_org.grpc.internal.grpcsync

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.internal.grpcsync :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.internal.grpcsync :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.internal.grpcsync

-- (grpc-mem, 2026-11-26) grpc's `internal/mem` (types only but what `mem`'s `init` runs: the binary-tiered
-- pool, `newBinaryTiered`), before `mem`, which imports it
namespace google_golang_org.grpc.internal.mem

/-- **`internal/mem`'s package fact**: `uintSize` holds `64` for good (`var uintSize = bits.UintSize`; no
translated code writes it), which `newBinaryTiered` reads (`maxExponent := uintSize - 2`). -/
def internalMemInit : IProp GF :=
  iprop(globalAddr _root_.Perennial.google_golang_org.grpc.internal.mem.uintSize ↦□ (W64 64))

instance internalMemInit_persistent : Persistent (internalMemInit (GF := GF)) := by
  unfold internalMemInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.internal.mem :=
  define_is_pkg_init internalMemInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.internal.mem :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.internal.mem

-- (grpc-mem, 2026-11-26) grpc's `mem` (types only but its initializer: the default pool, the hook
-- `internal.SetDefaultBufferPool`), before grpc's, which imports it; nothing reads its variables
namespace google_golang_org.grpc.mem

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.mem :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.mem :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.mem

-- `grpc` (names only; `etcdserverpb`'s streams are its generic interfaces, 2026-10-12: the
-- request path's `RaftKV` names `KV_RangeStreamServer`), before `etcdserverpb`, which imports it
/-- grpc's package fact (k8s 7e-1, 2026-11-10): `EnableTracing` (`var EnableTracing bool`, `trace.go:33`
at v1.84.0, no initializer) holds `false` for good. Go allocates it zero-valued before grpc's first
initializer runs; grpc's generated `Init.lean` takes the cell from the trust-boundary axiom
`DefaultBackoffConfig_init` and persists it. No translated code writes it; a program that sets it
(etcd's `embed` at log level debug) gets no proof. Read by the reply-ownership claim of
`grpcInvokerOk`/`RepSat` (`InvGrpc.lean`): with tracing on, grpc keeps every reply. -/
abbrev grpcInit : IProp GF := globalAddr google_golang_org.grpc.EnableTracing ↦□ false

instance grpc_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc :=
  define_is_pkg_init grpcInit
instance grpc_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc :=
  build_get_is_pkg_init_wf

/-- **A generated `ServiceDesc`** at `sd` (persistent, read-only): its service name `sn`, its
handler type `ht`, its methods `mds` and its streams `sds` (grpc's `grpcDescIs`, stated here below
grpc's server-side proofs). -/
def pbDescIs (sd : Loc) (sn : GoString) (ht : GoInterface) (mds : List google_golang_org.grpc.MethodDesc)
    (sds : List google_golang_org.grpc.StreamDesc) : IProp GF :=
  iprop(∃ msl ssl : GoSlice,
    structFieldRef google_golang_org.grpc.ServiceDesc go!"ServiceName" sd ↦□ sn ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"HandlerType" sd ↦□ ht ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Methods" sd ↦□ msl ∗ msl ↦*□ mds ∗
    structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams" sd ↦□ ssl ∗ ssl ↦*□ sds)

instance pbDescIs_persistent (sd : Loc) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc) :
    Persistent (pbDescIs (GF := GF) sd sn ht mds sds) := by
  unfold pbDescIs; infer_instance

/-- **`etcdserverpb`'s six `ServiceDesc`s** (`rpc_grpc.pb.go`: generated literals, never written;
item 8, 2026-10-17: until then an assumption of `v3rpc.Server`, `svcDescsOk`): their service names,
handler types and distinct method and stream names; the KV service's methods and the Watch
service's stream exactly ((the auth plan's E3zb) the Auth service's methods too; (the lease-src plan, 2026-11-02) the Lease
service's methods and stream; 2026-10-18: the Watch stream a client stream, `ClientStreams`, which
`grpc.ClientConn.NewStream`'s spec asks of its descriptor; and the Lease service's stream, the client
lease's keep-alive; per-type stage B, B1b: every stream descriptor of KV, Lease, Cluster and
Maintenance sets `ClientStreams` or `ServerStreams`, what `RegisterService` asks; (auth-mediation M1,
2026-11-20) every service's methods and streams exactly, with their generated handlers, so that
`v3rpc.Server.spec` states its registrations exactly). -/
abbrev etcdserverpbDescs : IProp GF :=
  iprop((∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.KV_ServiceDesc) go!"etcdserverpb.KV"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.KVServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
          [(go!"Range", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Range_Handler), (go!"Put", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Put_Handler),
           (go!"DeleteRange", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_DeleteRange_Handler),
           (go!"Txn", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Txn_Handler), (go!"Compact", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Compact_Handler)] ∧
        sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
          [(go!"RangeStream", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_RangeStream_Handler)] ∧
        ∀ sd ∈ sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝) ∗
    (∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Watch_ServiceDesc) go!"etcdserverpb.Watch"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds = [] ∧ sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
        [(go!"Watch", @! go_etcd_io.etcd.api.v3.etcdserverpb._Watch_Watch_Handler)] ∧
        sds.map (·.ClientStreams') = [true]⌝) ∗
    -- (the lease-src plan, 2026-11-02) the Lease service's methods and stream exactly, with their
    -- generated handlers
    (∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Lease_ServiceDesc) go!"etcdserverpb.Lease"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.LeaseServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
          [(go!"LeaseGrant", @! go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseGrant_Handler),
           (go!"LeaseRevoke", @! go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseRevoke_Handler),
           (go!"LeaseTimeToLive", @! go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler),
           (go!"LeaseLeases", @! go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler)] ∧
        sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
          [(go!"LeaseKeepAlive", @! go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseKeepAlive_Handler)] ∧
        ∀ sd ∈ sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝) ∗
    -- (auth-mediation M1, 2026-11-20) the Cluster service's methods exactly, with their generated
    -- handlers, and no stream
    (∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Cluster_ServiceDesc) go!"etcdserverpb.Cluster"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.ClusterServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
          [(go!"MemberAdd", @! go_etcd_io.etcd.api.v3.etcdserverpb._Cluster_MemberAdd_Handler),
           (go!"MemberRemove", @! go_etcd_io.etcd.api.v3.etcdserverpb._Cluster_MemberRemove_Handler),
           (go!"MemberUpdate", @! go_etcd_io.etcd.api.v3.etcdserverpb._Cluster_MemberUpdate_Handler),
           (go!"MemberList", @! go_etcd_io.etcd.api.v3.etcdserverpb._Cluster_MemberList_Handler),
           (go!"MemberPromote", @! go_etcd_io.etcd.api.v3.etcdserverpb._Cluster_MemberPromote_Handler)] ∧
        sds = []⌝) ∗
    -- (the auth plan's E3zb) the Auth service's methods exactly, with their generated handlers
    (∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Auth_ServiceDesc) go!"etcdserverpb.Auth"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.AuthServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
          [(go!"AuthEnable", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_AuthEnable_Handler),
           (go!"AuthDisable", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_AuthDisable_Handler),
           (go!"AuthStatus", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_AuthStatus_Handler),
           (go!"Authenticate", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_Authenticate_Handler),
           (go!"UserAdd", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_UserAdd_Handler),
           (go!"UserGet", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_UserGet_Handler),
           (go!"UserList", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_UserList_Handler),
           (go!"UserDelete", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_UserDelete_Handler),
           (go!"UserChangePassword", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_UserChangePassword_Handler),
           (go!"UserGrantRole", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_UserGrantRole_Handler),
           (go!"UserRevokeRole", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_UserRevokeRole_Handler),
           (go!"RoleAdd", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_RoleAdd_Handler),
           (go!"RoleGet", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_RoleGet_Handler),
           (go!"RoleList", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_RoleList_Handler),
           (go!"RoleDelete", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_RoleDelete_Handler),
           (go!"RoleGrantPermission", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_RoleGrantPermission_Handler),
           (go!"RoleRevokePermission", @! go_etcd_io.etcd.api.v3.etcdserverpb._Auth_RoleRevokePermission_Handler)] ∧
        sds.map (·.StreamName') = []⌝) ∗
    -- (auth-mediation M1, 2026-11-20) the Maintenance service's methods and stream exactly, with
    -- their generated handlers
    (∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Maintenance_ServiceDesc) go!"etcdserverpb.Maintenance"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.MaintenanceServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
          [(go!"Alarm", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_Alarm_Handler),
           (go!"Status", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_Status_Handler),
           (go!"Defragment", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_Defragment_Handler),
           (go!"Hash", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_Hash_Handler),
           (go!"HashKV", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_HashKV_Handler),
           (go!"MoveLeader", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_MoveLeader_Handler),
           (go!"Downgrade", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_Downgrade_Handler)] ∧
        sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
          [(go!"Snapshot", @! go_etcd_io.etcd.api.v3.etcdserverpb._Maintenance_Snapshot_Handler)] ∧
        ∀ sd ∈ sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝) ∗
    -- (item 1, the client lease, 2026-10-18) the Lease service's one stream, `LeaseKeepAlive`, a
    -- client stream (what `grpc.ClientConn.NewStream`'s spec asks of its descriptor)
    (∃ (ssl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
      structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams"
        (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Lease_ServiceDesc) ↦□ ssl ∗ ssl ↦*□ sds ∗
      ⌜sds.map (·.ClientStreams') = [true]⌝))

/-- The map `AlarmType_name` (`rpc.pb.go`, generated by protoc-gen-go) holds: the literal of its
initializer, its keys inserted in the literal's order (`0` first). The trusted model of
`AlarmType.String` reads it (etcd-grove#39, 2026-11-23). -/
def etcdserverpb.alarmTypeNames : GMap w32 GoString :=
  <[W32 2 := go!"CORRUPT"]> (<[W32 1 := go!"NOSPACE"]> (<[W32 0 := go!"NONE"]> ∅))

/-- **`etcdserverpb`'s fact** (item 8, 2026-10-17: moved here from `v3rpc`'s `sortNameMaps`): the
enumerations' name maps `checkRangeRequest` looks the sort order and target up in
(`RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`: generated `map[int32]string`
literals), fixed maps whose keys are the enumerations' values, `0` to `2` and `0` to `4`; the
alarm type's name map `AlarmType_name`, `etcdserverpb.alarmTypeNames` (etcd-grove#39, 2026-11-23:
`AlarmType.String`'s trusted model reads it), read-only; and its six `ServiceDesc`s
(`etcdserverpbDescs`). -/
abbrev etcdserverpbInit : IProp GF :=
  iprop((∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortOrder_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝) ∗
    (∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortTarget_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝) ∗
    (∃ mp : Loc, globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.AlarmType_name ↦□ mp ∗
      mp ↦$□ etcdserverpb.alarmTypeNames) ∗
    etcdserverpbDescs)

instance etcdserverpb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  define_is_pkg_init etcdserverpbInit
instance etcdserverpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  build_get_is_pkg_init_wf

instance grpc_codes_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  define_is_pkg_init iprop(True)
instance grpc_codes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  build_get_is_pkg_init_wf

/-- The error value `e`'s `Error()` returns some string (and does not panic). -/
def errorStringSpec (e : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errorStringSpec_persistent (e : GoInterfaceOk) :
    Persistent (errorStringSpec (GF := GF) e) := by
  unfold errorStringSpec; infer_instance

/-- **The error value `e`'s `Error()` returns `m`, the same string on every call** (persistent;
fromerror-stable, 2026-11-06): what `status.FromError` needs to take the string as the error's
description (`errDesc`): it calls `Error()` on each call, so an `Error()` that reads mutable state
(`examples/axiomcx/flipdesc`, `notes/axiom-review/invoker-filled.md`) has no one description.
Stronger than `errorStringSpec` (`errorMsgIs_errorStringSpec`), which the printing paths keep.
A partial-correctness WP: it says each call returns `m` *or does not return*, so it does not pin `m`
against later divergence (an `Error()` that starts looping holds `errorMsgIs e m` for every `m` from
then on). A pure fact about `m` may only come from a call made while it held, with `m` fixed before the
call (a precondition), never from a wand applied to an `errorMsgIs` proved later (fromerror-wand,
2026-11-18: `notes/fromerror-wand.md`, `examples/axiomcx/fromerrorflip`). -/
def errorMsgIs (e : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errorMsgIs_persistent (e : GoInterfaceOk) (m : GoString) :
    Persistent (errorMsgIs (GF := GF) e m) := by
  unfold errorMsgIs; infer_instance

/-- **`err` is a context error** (persistent; incomingof Part B, 2026-11-18): of a context error's shape
(`ctxErrShape`), and its `Error()` stably returns one of Go's two context messages (`ctxErrMsg`), as
`ctxErrsErr` gives of `ctx.Err()`. What `ContextError` keeps (`ContextError.spec`). -/
def ctxErrIs (err : GoInterface) : IProp GF :=
  iprop(∃ (e : GoInterfaceOk) (m : GoString),
    ⌜err = GoInterface.ok e ∧ ctxErrMsg m ∧ ctxErrShape e⌝ ∗ errorMsgIs e m)

instance ctxErrIs_persistent (err : GoInterface) : Persistent (ctxErrIs (GF := GF) err) := by
  unfold ctxErrIs; infer_instance

/-- **`err`'s description is `m`** (persistent; errdesc stage 2b, 2026-11-21; D29): what
`status.FromError(err).Message()` and `rpctypes.ErrorDesc(err)` return. `nil`: `""`; an
`rpctypes.EtcdError` value: its `desc` (`EtcdError.Error` returns it, and it has no `GRPCStatus`; a pure
fact of a pointer-free value, the same in every run); an error of another type with grpc's
`GRPCStatus() *Status`: the message of the read-only status it stably returns (`status.statusAt`; since
status-bodies, 2026-11-25, the status its `*status.Error` holds, `status.grpcStatusIs`, on which two
descriptions agree); otherwise the string its `Error()` stably returns (`errorMsgIs`; grpc v1.84.0 `status.go:96-127`:
`FromError` returns the status of an error with `GRPCStatus` directly, and for every other error a status
whose message is `err.Error()`, wrapping or not). A relation, not a function: no law makes two of them on
one error agree (`notes/errdesc-ghost-plan.md`, the rule (I1)-(I4)); a fact about the description comes
from a call whose precondition fixed `m`. Until 2026-11-21 the pure `errDesc err`, a fixed function of the
error value, which no implementation could meet for the errors it allocates. -/
def descIs (err : GoInterface) (m : GoString) : IProp GF :=
  iprop(⌜err = GoInterface.nil ∧ m = go!""⌝ ∨
    ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      err = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∧ m = x.desc'⌝ ∨
    ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e ∧
        ¬ ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
          err = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝ ∗
      ((⌜methodSet e.ty !! go!"GRPCStatus" ≠ some (go.Signature [] false
          [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])⌝ ∗ errorMsgIs e m) ∨
        ∃ (s : Loc) (c : w32), ⌜methodSet e.ty !! go!"GRPCStatus" = some (go.Signature [] false
          [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])⌝ ∗
          EtcdGrove.status.grpcStatusIs e s c m))

instance descIs_persistent (err : GoInterface) (m : GoString) :
    Persistent (descIs (GF := GF) err m) := by
  unfold descIs; infer_instance

omit package_sem in
/-- The description of `nil` is `""`. -/
theorem descIs_nil : ⊢ descIs (GF := GF) GoInterface.nil go!"" := by
  unfold descIs
  ileft; ipureintro; exact ⟨rfl, rfl⟩

omit package_sem in
/-- **An `EtcdError`'s description is its `desc`** (proved; errdesc stage 2b: until then the axiom
`rpctypes.errDesc_etcdError`, a fact of the pure `errDesc`). -/
theorem descIs_etcdError (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) :
    ⊢ descIs (GF := GF)
      (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) x.desc' := by
  unfold descIs
  iright; ileft; ipureintro; exact ⟨x, rfl, rfl⟩

omit package_sem in
/-- An `EtcdError` of `desc` `m` has description `m`. -/
theorem descIs_etcdError_of (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) (m : GoString)
    (h : x.desc' = m) :
    ⊢ descIs (GF := GF)
      (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) m := by
  subst h; exact descIs_etcdError x

omit package_sem in
/-- **The value pin**: of an `EtcdError` value, a description is its `desc` (a pure fact of a
pointer-free value). -/
theorem descIs_etcdError_eq [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.TypeAssumptions] (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) (m : GoString) :
    descIs (GF := GF)
      (interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) m ⊢ ⌜m = x.desc'⌝ := by
  unfold descIs
  iintro (%h | %h | ⟨%e, %h, -⟩)
  · exact absurd h.1 nofun
  · obtain ⟨y, hy, rfl⟩ := h
    ipureintro
    simp only [interface.mkOk] at hy
    injection hy with hy
    injection hy with _ h
    have k := (go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.TypeAssumptions.get_desc
      x).isGoStep_det_internal.isGoStep_pure_det
    have k' := (go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.TypeAssumptions.get_desc
      y).isGoStep_det_internal.isGoStep_pure_det
    rw [h] at k
    have e := congrFun (k.symm.trans k') (Val #(x.desc'))
    simp only [eq_iff_iff, true_iff] at e
    have f : (#(x.desc') : val) = #(y.desc') := by injection e.symm
    exact (go.intoVal_inj f).symm
  · exact absurd ⟨x, rfl⟩ h.2

omit package_sem in
/-- **An error that is an `EtcdError` value, or whose description is its `desc`**: its description is
that `desc` (the value pin; what `errors.IsStatusErr`'s post gives for an `EtcdError` target). -/
theorem descIs_is_etcdError [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.TypeAssumptions]
    (err : GoInterface) (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) (m : GoString)
    (h : err = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∨ m = x.desc') :
    descIs (GF := GF) err m ⊢ ⌜m = x.desc'⌝ := by
  iintro #H
  rcases h with rfl | h
  · iapply descIs_etcdError_eq $$ H
  · ipureintro; exact h

omit package_sem in
/-- **An error without grpc's `GRPCStatus`, of a type other than `EtcdError`**: its stable `Error()`. -/
theorem descIs_of_msg (e : GoInterfaceOk) (m : GoString)
    (hty : e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (hg : methodSet e.ty !! go!"GRPCStatus" ≠ some (go.Signature [] false
          [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])) :
    errorMsgIs (GF := GF) e m ⊢ descIs (GoInterface.ok e) m := by
  iintro #H
  unfold descIs
  iright; iright
  iexists e
  isplitr
  · ipureintro
    refine ⟨rfl, ?_⟩
    rintro ⟨x, hx⟩
    simp only [interface.mkOk] at hx
    injection hx with hx
    exact hty (by rw [hx])
  ileft
  iframe H
  ipureintro; exact hg

omit package_sem in
/-- **`deadlineExceededError{}`'s description is `"context deadline exceeded"`** (#45, 2026-11-25):
its `Error()` returns the literal, and it has no `GRPCStatus`. -/
theorem descIs_deadlineZero [_root_.Perennial.context.Assumptions] :
    ⊢ descIs (GF := GF) (interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError)) go!"context deadline exceeded" := by
  iapply descIs_of_msg
  · intro h
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
      _root_.Perennial.context.deadlineExceededError.ty at h
    simp at h
  · have := go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty)
      go!"GRPCStatus"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at this
    simp [this]
  unfold errorMsgIs
  iintro !> %Φ HΦ
  wp_method_call
  unfold _root_.Perennial.context.deadlineExceededError.Error.impl
  wp_auto
  iexact HΦ

omit package_sem in
/-- **A context's error has a description** (#45, 2026-11-25): its stable `Error()` (`"context
canceled"` of the `*errorString` in `context.Canceled`, `"context deadline exceeded"` of
`deadlineExceededError{}`); neither type has grpc's `GRPCStatus`. What `errors.IsStatusErr` takes of
a context-error target. -/
theorem isCtxErr_descIs [_root_.Perennial.errors.Assumptions] [_root_.Perennial.context.Assumptions]
    (e : GoInterface) :
    _root_.Perennial.context.isCtxErr (GF := GF) e ⊢ ∃ m : GoString, descIs e m := by
  iintro #H
  unfold _root_.Perennial.context.isCtxErr
  icases H with (⟨-, %x, %hx, #Hs⟩ | ⟨-, %hx⟩)
  · subst hx
    iexists go!"context canceled"
    iapply descIs_of_msg
    · intro h
      try simp only [interface.mkOk] at h
      unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty at h
      cases h
    · have := go.method_set_is (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"GRPCStatus"
      simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at this
      simp [this]
    unfold errorMsgIs
    iintro !> %Φ HΦ
    rw [method_unfold]
    wp_auto
    iexact HΦ
  · subst hx
    iexists go!"context deadline exceeded"
    iapply descIs_deadlineZero

/-- **The methods grpc's `status` and Go's `errors.Is` call on the error `e` return**
(persistent; unit P3a), if `e`'s type has them (both are called through a type assertion):
`GRPCStatus() *Status` (`status.FromError`/`Code`/`Convert`) and `Is(error) bool`
(`errors.Is`, for any target). (fromerror-stable, 2026-11-06) `GRPCStatus()` returns one fixed
status `s`, so the code and message `status.FromError` reads are the error's (`statusCode`,
`errDesc`); and `Is` returns `true` only for a target with the same description
(`errors.IsStatusErr`'s post: an `Is` that answered `true` regardless would refute it; errdesc stage 2b,
2026-11-21: of descriptions `m`, `m'` the caller fixes, `descIs`, until then the pure `errDesc`).
(k8s 7f-5a-P step 5, E1, approved by etcd-grove-81 2026-11-15) The status `s` is read-only: grpc's
`*Status` is not immutable in Go (a whole-struct assignment `*s = *t` from any package copies its
unexported fields); the fact is a guarantee of the producer that built `s` (with `status.New`/`Error`)
and never writes it after, as grpc and etcd do (`examples/premisefix/grpcstatusro`;
`notes/k8s-7f5a-draft.md` §11.2); a status may be shared (package-level `status.Error` values).
(errdesc stage 2a, 2026-11-20) Read-only with some code `c` and message `m`, the per-run relation
`status.statusAt s c m` (until then `grpcStatusRO s (statusCode e)`, the pure `statusCode`).
(status-bodies, 2026-11-25, #24 7175612915) An error with `GRPCStatus() *Status` is a `*status.Error`
holding that status (`status.grpcStatusIs`: its field `s`, read-only), not one whose `GRPCStatus()` has a
WP returning it: one WP per fact, which no proof calling `GRPCStatus()` once can make agree
(`status.FromError`'s code and message); the WP follows (`grpcStatusIs_wp`). True of grpc and of the
code translated here, where `*status.Error` is the only type with that method. -/
def grpcErrMethodsOk (e : GoInterfaceOk) : IProp GF :=
  iprop((⌜methodSet e.ty !! go!"GRPCStatus" =
      some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])⌝ →
    ∃ (s : Loc) (c : w32) (m : GoString), EtcdGrove.status.grpcStatusIs e s c m) ∗
    (⌜methodSet e.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool])⌝ →
    □ ∀ (target : GoInterface) (m m' : GoString) (Φ : val → IProp GF),
      descIs (GoInterface.ok e) m -∗ descIs target m' -∗
      ▷ (∀ b : Bool, ⌜b = true → m = m'⌝ -∗ Φ #b) -∗
      WP (App (Val #(methods e.ty go!"Is" e.v)) (Val #target)) {{ Φ }}))

/-- **An error's value is of its dynamic type** (#45, 2026-11-25), for the three kinds of target
`errors.IsStatusErr` compares an error with (`errors.ComparableErr`): an `rpctypes.EtcdError`
holds an `EtcdError`, a `deadlineExceededError` its only value `deadlineExceededError{}`, and a
pointer type a pointer. Go's typing makes it true of every Go interface value; the model does not
type interface values, so the producers of errors say it. -/
def stTypedErr (e : GoInterfaceOk) : Prop :=
  (e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
    ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, e.v = #x) ∧
  (e.ty = _root_.Perennial.context.deadlineExceededError.ty →
    e.v = #(zero_val _root_.Perennial.context.deadlineExceededError)) ∧
  (∀ T, e.ty = go.PointerType T → ∃ l : Loc, e.v = #l)

/-- A pointer error is `stTypedErr`. -/
theorem stTypedErr_ptr (e : GoInterfaceOk) (h : _root_.Perennial.errors.IsPointerError e) :
    stTypedErr e := by
  obtain ⟨T, l, hT, hl⟩ := h
  refine ⟨fun h' => ?_, fun h' => ?_, fun _ _ => ⟨l, hl⟩⟩
  · rw [hT] at h'; unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty at h'; cases h'
  · rw [hT] at h'; unfold _root_.Perennial.context.deadlineExceededError.ty at h'; cases h'

/-- An `EtcdError` value is `stTypedErr`. -/
theorem stTypedErr_etcdError (x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError) :
    stTypedErr ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, #x⟩ := by
  refine ⟨fun _ => ⟨x, rfl⟩, fun h' => ?_, fun T h' => ?_⟩
  · unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
      _root_.Perennial.context.deadlineExceededError.ty at h'
    simp at h'
  · unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty at h'; cases h'

/-- `deadlineExceededError{}` is `stTypedErr`. -/
theorem stTypedErr_deadline :
    stTypedErr ⟨_root_.Perennial.context.deadlineExceededError.ty,
      #(zero_val _root_.Perennial.context.deadlineExceededError)⟩ := by
  refine ⟨fun h' => ?_, fun _ => rfl, fun T h' => ?_⟩
  · unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
      _root_.Perennial.context.deadlineExceededError.ty at h'
    simp at h'
  · unfold _root_.Perennial.context.deadlineExceededError.ty at h'; cases h'

/-- An error of a non-pointer type other than `EtcdError` and `deadlineExceededError` is
`stTypedErr` (vacuously). -/
theorem stTypedErr_of_ty (e : GoInterfaceOk)
    (h1 : e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (h2 : e.ty ≠ _root_.Perennial.context.deadlineExceededError.ty)
    (h3 : ∀ T, e.ty ≠ go.PointerType T) : stTypedErr e :=
  ⟨fun h => absurd h h1, fun h => absurd h h2, fun T h => absurd h (h3 T)⟩

/-- **An error grpc's `status` functions accept** (persistent; unit P3a): `nil`, or a leaf error
(`errors.isLeafError`: no `Unwrap` or `As` method, so `status.FromError`'s and `errors.Is`'s walks
of its error tree only check it) whose `Error()` returns one fixed string (`errorMsgIs`:
`FromError` calls it unless the error is a status error; fromerror-stable, 2026-11-06: it was any
string on each call, `errorStringSpec`) and whose `GRPCStatus()` and `Is`, if it has them, behave
(`grpcErrMethodsOk`). What `status.FromError` (`Spec/google_golang_org/grpc/
status/FromError.lean`), `status.Code`, `errors.Is` (`Spec/errors/IsStatusErr.lean`), and through
them `rpctypes.Error` and the client's retry interceptor, need. No `Format` method
(premise-fixes-4, 2026-11-10): `fmt` prints it with its `Error` (`fmt.argOk`); grpc's
`*status.Error`, `rpctypes.EtcdError` and the context errors have none (`examples/premisefix/
fmtarg`). Its `Error` is `Error() string` (`noArgStringSig`; fmt soundness 2, 2026-11-18: what
`fmt.argOk` asks since; true of every non-nil Go `error` value's dynamic type). (#45, 2026-11-25)
Its value is of its dynamic type, for the types `errors.Is` compares it with (`stTypedErr`: Go's
typing, which the model does not have). -/
def statusErrOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ →
    (∃ m : GoString, errorMsgIs e m) ∗ ⌜errors.isLeafError e⌝ ∗ grpcErrMethodsOk e ∗
    ⌜methodSet e.ty !! go!"Format" = none ∧
      methodSet e.ty !! go!"Error" = some EtcdGrove.noArgStringSig⌝ ∗
    ⌜stTypedErr e⌝)

instance statusErrOk_persistent (err : GoInterface) : Persistent (statusErrOk (GF := GF) err) := by
  unfold statusErrOk; infer_instance

/-- **The gRPC status code of `err` is `c`** (persistent; errdesc stage 2a, 2026-11-20: until then the
pure `statusCode err`): what `status.FromError(err).Code()` and `status.Code(err)` return. `nil`:
`OK`; an error without grpc's `GRPCStatus() *Status`: `Unknown` (grpc v1.84.0 `status.go:96-127`);
one with it: the code of the read-only status it stably returns (`grpcErrMethodsOk`; since status-bodies,
2026-11-25, the status its `*status.Error` holds, `status.grpcStatusIs`). -/
def statusCodeIs (err : GoInterface) (c : w32) : IProp GF :=
  iprop(⌜err = GoInterface.nil ∧ c = W32 0⌝ ∨
    (∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e ∧ methodSet e.ty !! go!"GRPCStatus" ≠
      some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty]) ∧ c = W32 2⌝) ∨
    ∃ (e : GoInterfaceOk) (s : Loc) (m : GoString), ⌜err = GoInterface.ok e ∧
      methodSet e.ty !! go!"GRPCStatus" = some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])⌝ ∗
      EtcdGrove.status.grpcStatusIs e s c m)

instance statusCodeIs_persistent (err : GoInterface) (c : w32) :
    Persistent (statusCodeIs (GF := GF) err c) := by
  unfold statusCodeIs; infer_instance

omit package_sem in
/-- **The description of an error grpc's `status` accepts**: some `m` (what a caller indifferent to
the description takes). -/
theorem statusErrOk_descIs (err : GoInterface) :
    statusErrOk (GF := GF) err ⊢ ∃ m : GoString, descIs err m := by
  iintro #H
  by_cases hx : ∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      err = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x
  · obtain ⟨x, rfl⟩ := hx
    iexists x.desc'
    iapply descIs_etcdError
  cases err with
  | nil =>
    iexists go!""
    iapply descIs_nil
  | ok e0 =>
    unfold statusErrOk
    icases H $$ %e0 %rfl with ⟨⟨%m, #Hm⟩, -, #Hg, -⟩
    unfold grpcErrMethodsOk
    icases Hg with ⟨Hg, -⟩
    by_cases hg : methodSet e0.ty !! go!"GRPCStatus" = some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])
    · ihave ⟨%s, %c, %m', #Hst⟩ := Hg $$ %hg
      iexists m'
      unfold descIs
      iright; iright
      iexists e0
      isplitr
      · ipureintro; exact ⟨rfl, hx⟩
      iright
      iexists s, c
      iframe Hst
      ipureintro; exact hg
    · iexists m
      unfold descIs
      iright; iright
      iexists e0
      isplitr
      · ipureintro; exact ⟨rfl, hx⟩
      ileft
      iframe Hm
      ipureintro; exact hg

/-- **The descriptions `errors.Is` compares, if the caller fixes them** (persistent; errdesc stage 2b,
2026-11-21): `none`, nothing (a caller indifferent to the descriptions); `some (m, m')`, `err`'s is `m`
and the target's `m'` (`errors.IsStatusErr.spec`'s precondition). -/
def isDescs (err target : GoInterface) : _root_.Option (GoString × GoString) → IProp GF
  | none => iprop(True)
  | some (m, m') => iprop(descIs err m ∗ descIs target m')

instance isDescs_persistent (err target : GoInterface) (dm : _root_.Option (GoString × GoString)) :
    Persistent (isDescs (GF := GF) err target dm) := by
  cases dm with
  | none => unfold isDescs; infer_instance
  | some p => obtain ⟨m, m'⟩ := p; unfold isDescs; infer_instance

omit package_sem in
theorem isDescs_none (err target : GoInterface) : ⊢ isDescs (GF := GF) err target none := by
  unfold isDescs; itrivial

omit package_sem in
theorem isDescs_some (err target : GoInterface) (m m' : GoString) :
    descIs (GF := GF) err m ⊢ descIs target m' -∗ isDescs err target (some (m, m')) := by
  iintro #H1 #H2
  simp only [isDescs]
  isplitl
  · iexact H1
  · iexact H2

/-- **An error that is not a handler's** (persistent; errdesc stage 2b): non-nil, with a description
none of `handlerDescs`' (grpc's own errors: `dec`'s, an interceptor's refusal). Until 2026-11-21
`err ≠ nil ∧ errDesc err ∉ handlerDescs` (a pure fact of the pure `errDesc`). -/
def notDescIn (ds : List GoString) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗ ∃ m : GoString, descIs err m ∗ ⌜m ∉ ds⌝)

instance notDescIn_persistent (ds : List GoString) (err : GoInterface) :
    Persistent (notDescIn (GF := GF) ds err) := by
  unfold notDescIn; infer_instance

omit package_sem in
theorem notDescIn_ne (ds : List GoString) (err : GoInterface) :
    notDescIn (GF := GF) ds err ⊢ ⌜err ≠ GoInterface.nil⌝ := by
  unfold notDescIn
  iintro ⟨%h, -⟩
  ipureintro; exact h

-- The names-only target of the alias `grpc/status.Status` (imported by `grpc/status` since
-- `client/v3/leasing` names it).
instance grpc_internal_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.internal.status :=
  define_is_pkg_init iprop(True)
instance grpc_internal_status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.internal.status :=
  build_get_is_pkg_init_wf

instance grpc_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.status :=
  define_is_pkg_init iprop(True)
instance grpc_status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.status :=
  build_get_is_pkg_init_wf

/-- **The method set of `rpctypes.EtcdError`** is `{Code, Error}` (`error.go`), as far as
grpc's and Go's `errors` functions look (Go's typing, which the model lacks: method sets are
uninterpreted): no `As` or `Unwrap` method (a leaf error), no `GRPCStatus` and no `Is` method
(unit P3a), and no `Format` method (premise-fixes-4: `fmt` prints it with its `Error`), and its
`Error` is `Error() string` (fmt soundness 2). -/
def rpctypesEtcdErrorTy : Prop :=
  (∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩) ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Format" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Error" =
    some EtcdGrove.noArgStringSig

/-- **`X` holds an error grpc's `status` accepts, of description `m`** (persistent; grpcerrmap,
2026-11-26): what `v3rpc`'s error map `toGRPCErrorMap` takes of each of its values. -/
abbrev statusErrVar (X m : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr X ↦□ GoInterface.ok e ∗ statusErrOk (GoInterface.ok e) ∗
    descIs (GoInterface.ok e) m)

/-- **The values of `v3rpc`'s error map** (grpcerrmap, 2026-11-26; `v3rpc/util.go`'s
`toGRPCErrorMap`, in the literal's order, each once): `rpctypes`' errors, each with its description
(`error.go`: the `status.Error` errors' messages, and `ErrMemberNotEnoughStarted`'s and
`ErrTooManyRequests`' those of the `ErrGRPC*` errors they are `Error` of). -/
abbrev rpctypesMapVals : IProp GF :=
  iprop(
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberNotFound go!"etcdserver: member not found" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberExist go!"etcdserver: member ID already exist" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPeerURLExist go!"etcdserver: Peer URLs already exists" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCMemberNotLearner go!"etcdserver: can only promote a learner member" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyLearners go!"etcdserver: too many learner members in cluster" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrMemberNotEnoughStarted go!"etcdserver: re-configuration failed due to not enough started members" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLearnerNotReady go!"etcdserver: can only promote a learner member which is in sync with leader" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCompacted go!"etcdserver: mvcc: required revision has been compacted" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCFutureRev go!"etcdserver: mvcc: required revision is a future revision" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRequestTooLarge go!"etcdserver: request is too large" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoSpace go!"etcdserver: mvcc: database space exceeded" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrTooManyRequests go!"etcdserver: too many requests" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader go!"etcdserver: no leader" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotLeader go!"etcdserver: not leader" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaderChanged go!"etcdserver: leader changed" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCanceled go!"etcdserver: request canceled" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCStopped go!"etcdserver: server stopped" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeout go!"etcdserver: request timed out" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeoutDueToLeaderFail go!"etcdserver: request timed out, possibly due to previous leader failure" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeoutDueToConnectionLost go!"etcdserver: request timed out, possibly due to connection lost" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTimeoutWaitAppliedIndex go!"etcdserver: request timed out, waiting for the applied index took too long" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUnhealthy go!"etcdserver: unhealthy cluster" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound go!"etcdserver: key not found" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCorrupt go!"etcdserver: corrupt cluster" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCBadLeaderTransferee go!"etcdserver: bad leader transferee" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCClusterVersionUnavailable go!"etcdserver: cluster version not found during downgrade" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWrongDowngradeVersionFormat go!"etcdserver: wrong downgrade target version format" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidDowngradeTargetVersion go!"etcdserver: invalid downgrade target version" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDowngradeInProcess go!"etcdserver: cluster has a downgrade job in progress" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoInflightDowngrade go!"etcdserver: no inflight downgrade job" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseNotFound go!"etcdserver: requested lease not found" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseExist go!"etcdserver: lease already exists" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseTTLTooLarge go!"etcdserver: too large lease TTL" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRootUserNotExist go!"etcdserver: root user does not exist" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRootRoleNotExist go!"etcdserver: root user does not have root role" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserAlreadyExist go!"etcdserver: user name already exists" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserEmpty go!"etcdserver: user name is empty" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserNotFound go!"etcdserver: user name not found" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleAlreadyExist go!"etcdserver: role name already exists" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleNotFound go!"etcdserver: role name not found" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleEmpty go!"etcdserver: role name is empty" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthFailed go!"etcdserver: authentication failed, invalid user ID or password" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionNotGiven go!"etcdserver: permission not given" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionDenied go!"etcdserver: permission denied" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCRoleNotGranted go!"etcdserver: role is not granted to the user" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionNotGranted go!"etcdserver: permission is not granted to the role" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthNotEnabled go!"etcdserver: authentication is not enabled" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidAuthToken go!"etcdserver: invalid auth token" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidAuthMgmt go!"etcdserver: invalid auth management" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthOldRevision go!"etcdserver: revision of auth store is old" ∗
    statusErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDeadlineExceeded go!"etcdserver: context deadline exceeded")

set_option synthInstance.maxSize 4096 in
instance rpctypesMapVals_persistent : Persistent (rpctypesMapVals (GF := GF)) := by
  unfold rpctypesMapVals statusErrVar; infer_instance

/-- `rpctypes`' package facts: the two errors the store returns (`EtcdError` values, k8s etcd3 7e-2's
D1, `examples/k8s7e2attack`'s `TestRpctypesErrTypes`); `ErrCompacted.Error()`
(the watcher's `Compact` puts it in the cancel response) returns some string, and so does
`ErrFutureRev.Error()` (`WatchResponse.Err` returns it; both are `EtcdError`s, whose `Error`
returns their description); and (unit P3a: `rpctypes.Error` is translated) the map
`errStringToError` (never written after init) whose values (the `ErrGRPC*` errors, `status.Error`'s
`*status.Error`s) grpc's `status.FromError` accepts (`statusErrOk`), `EtcdError`'s method set
(`rpctypesEtcdErrorTy`), the `EtcdError` values the client's retry interceptor compares with
(`ErrUserEmpty`, `ErrInvalidAuthToken`, `ErrAuthOldRevision`: `Error` of an `ErrGRPC*`) and its
`ErrGRPCNotSupportedForLearner` (a `*status.Error`, a pointer); and (item 8, 2026-10-17: moved here
from `auth`'s facts, so that `rpctypes`' initializer proves them) the token keys
`TokenFieldNameGRPC`, `TokenFieldNameSwagger` (`"token"`, `"authorization"`; the strings since the
auth plan's E2c); and (grpcerrmap, 2026-11-26) the values of `v3rpc`'s error map, each an error grpc's
`status` accepts with its description (`rpctypesMapVals`: the last conjunct). -/
abbrev rpctypesInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e ∗
      -- (k8s etcd3 7c) its description
      descIs (GoInterface.ok e) futureRevDesc ∗
      -- (premise-fixes-4) no `Format` method: `fmt` prints it through `Error()`
      ⌜methodSet e.ty !! go!"Format" = none⌝ ∗
      -- (k8s etcd3 7e-2, D1) an `EtcdError` value (`TestRpctypesErrTypes`)
      ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ↦□ GoInterface.ok e ∗
      errorStringSpec e ∗ descIs (GoInterface.ok e) compactedDesc ∗
      ⌜methodSet e.ty !! go!"Format" = none⌝ ∗
      ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝) ∗
    □ (∀ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e -∗
      errorStringSpec e) ∗
    (∃ (mref : Loc) (m : GMap GoString GoInterface),
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.errStringToError ↦□ mref ∗ mref ↦$□ m ∗
      □ (∀ (k : GoString) (v : GoInterface), ⌜m !! k = some v⌝ → statusErrOk v) ∗
      -- (D29, 2026-10-21) each value's description is its key (`ErrorDesc(ErrGRPCx): ErrGRPCx`)
      □ (∀ (k : GoString) (v : GoInterface), ⌜m !! k = some v⌝ → descIs v k)) ∗
    ⌜rpctypesEtcdErrorTy (GF := GF) (hG := hG)⌝ ∗
    -- (D29, 2026-10-21) the refusals with their descriptions
    (∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrUserEmpty ↦□
        interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∗
      ⌜x.desc' = go!"etcdserver: user name is empty"⌝) ∗
    (∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrInvalidAuthToken ↦□
        interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∗
      ⌜x.desc' = go!"etcdserver: invalid auth token"⌝) ∗
    (∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrAuthOldRevision ↦□
        interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x ∗
      ⌜x.desc' = go!"etcdserver: revision of auth store is old"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotSupportedForLearner ↦□
        GoInterface.ok e ∗ ⌜errors.IsPointerError e⌝ ∗
      descIs (GoInterface.ok e) go!"etcdserver: rpc not supported for learner" ∗
      -- (k8s etcd3 7c, HS-6) grpc's `status.FromError` accepts it
      statusErrOk (GoInterface.ok e)) ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameGRPC ↦□ go!"token" ∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameSwagger ↦□ go!"authorization" ∗
    -- (item 8, 2026-10-17: moved here from `v3rpc`'s facts) the `ErrGRPC*` errors the gRPC
    -- service's checks and interceptors return, fixed non-nil errors, and the metadata keys
    -- ((k8s etcd3 7c, HS-6) `*status.Error`s, which grpc's `status.FromError` accepts)
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoSpace ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotCapable ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidClientAPIVersion ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader ↦□ GoInterface.ok e ∗
      statusErrOk (GoInterface.ok e)) ∗
    (∃ k : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataClientAPIVersionKey ↦□ k) ∗
    (∃ k : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataRequireLeaderKey ↦□ k) ∗
    (∃ k : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataHasLeader ↦□ k) ∗
    -- (D19j, 2026-10-18) the `ErrGRPC*` errors `v3rpc`'s watch server returns or reports, whose
    -- `Error()` returns
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidAuthToken ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthOldRevision ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserEmpty ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionDenied ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
    -- (premise-fixes-7, Q1) `ErrGRPCWatchCanceled`, which `watchServer.Watch` returns, also one
    -- grpc's `status.FromError` accepts
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWatchCanceled ↦□ GoInterface.ok e ∗
      errorStringSpec e ∗ statusErrOk (GoInterface.ok e)) ∗
    -- (item 1, the client lease, 2026-10-18) `ErrNoLeader`, an `EtcdError` (the client's lease
    -- keep-alive loop compares a stream's error with it)
    (∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNoLeader ↦□
        interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) ∗
    -- (the auth plan's C1, 2026-10-28) `ErrAuthNotEnabled`, an `EtcdError` (the client's
    -- `getToken` compares `Authenticate`'s error with it)
    (∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrAuthNotEnabled ↦□
        interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) ∗
    -- (k8s etcd3 7c) the server-side errors `togRPCError` maps mvcc's two read errors to, with
    -- their descriptions
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCFutureRev ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) futureRevDesc) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCompacted ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) compactedDesc) ∗
    -- (k8s etcd3 7c, HS-1) the descriptions of the `ErrGRPC*` errors `v3rpc`'s checks and
    -- interceptors return (`error.go`)
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: key is not provided") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: key not found") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: value is provided") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: lease is provided") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: too many operations in txn request") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: duplicate key given in txn request") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidClientAPIVersion ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: invalid client api version") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: invalid sort option") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoSpace ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: mvcc: database space exceeded") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: no leader") ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotCapable ↦□ GoInterface.ok e ∗
      descIs (GoInterface.ok e) go!"etcdserver: not capable") ∗
    -- (grpcerrmap, 2026-11-26) the values of `v3rpc`'s error map, which its initializer reads
    rpctypesMapVals)

instance rpctypes_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  define_is_pkg_init rpctypesInit
instance rpctypes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  build_get_is_pkg_init_wf

-- The names-only packages of `clientv3.Client`'s field types.

instance clientv3_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials :=
  define_is_pkg_init iprop(True)
instance clientv3_credentials_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials :=
  build_get_is_pkg_init_wf

-- (prove-grpc3, 2026-11-21) what `internal/resolver`'s translated `New` and `SetEndpoints` import:
-- grpc's manual resolver (no package variable), its resolver types and their field types.
-- (grpc's `serviceconfig`, `attributes` and `resolver`: before `grpc`, which imports `resolver`
-- since phase 7 S1's dial side)
instance grpc_manual_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.resolver.manual :=
  define_is_pkg_init iprop(True)
instance grpc_manual_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.resolver.manual :=
  build_get_is_pkg_init_wf

instance clientv3_resolver_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver :=
  define_is_pkg_init iprop(True)
instance clientv3_resolver_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver :=
  build_get_is_pkg_init_wf

-- Names only (item 5, client construction, branch `construct`): what `clientv3.New`'s dial
-- names (the type of `Config.TLS`, grpc's keepalive parameters and insecure credentials, an
-- endpoint's credentials requirement, the default logger); `logutil`'s instance moved here from
-- `etcdserver/BaseApply.lean` (stage R8b), now that `clientv3` imports it. (`crypto/tls`'s:
-- `Proof/crypto/tls/PkgInit.lean`, L1, 2026-11-24.)
instance grpc_insecure_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure :=
  define_is_pkg_init iprop(True)
instance grpc_insecure_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure :=
  build_get_is_pkg_init_wf
instance clientv3_endpoint_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.endpoint :=
  define_is_pkg_init iprop(True)
instance clientv3_endpoint_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.endpoint :=
  build_get_is_pkg_init_wf
instance logutil_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.logutil :=
  define_is_pkg_init iprop(True)
instance logutil_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.logutil :=
  build_get_is_pkg_init_wf



/-- **A backoff function** (`clientv3.backoffFunc`, `func(attempt uint) time.Duration`) that
returns (persistent; unit P3a: the retry interceptor's `waitRetryBackoff` calls it). -/
def backoffOk (bf : GoFunc) : IProp GF :=
  iprop(□ ∀ (a : w64) (Φ : val → IProp GF), ▷ (∀ d : w64, Φ #d) -∗
    WP (App (Val #bf) (Val #a)) {{ Φ }})

instance backoffOk_persistent (bf : GoFunc) : Persistent (backoffOk (GF := GF) bf) := by
  unfold backoffOk; infer_instance

/-- The namespace of `clientTargetSeq`'s invariant (`clientv3Init`). -/
def clientTargetSeqN : Namespace := nroot.@"clientv3_target_seq"

/-- `clientv3`'s package facts: `noPrefixEnd` (`[]byte{0}`, never written), which
`getPrefix` returns for a prefix with no successor; and (unit P3a) `defaultOptions`, the retry
interceptor's options (never written), whose backoff function (`backoffLinearWithJitter`'s, float
arithmetic) returns. -/
abbrev clientv3Init : IProp GF :=
  iprop((∃ sl : GoSlice, globalAddr go_etcd_io.etcd.client.v3.noPrefixEnd ↦□ sl ∗
    sl ↦*□ [W8 0]) ∗
    (∃ (dp : Loc) (ov : go_etcd_io.etcd.client.v3.options),
      globalAddr go_etcd_io.etcd.client.v3.defaultOptions ↦□ dp ∗ dp ↦□ ov ∗
      backoffOk ov.backoffFunc' ∗
      -- (D29, 2026-10-21) the default policy: `nonRepeatable`
      ⌜ov.retryPolicy' = W8 1⌝) ∗
    -- (item 8, 2026-10-17: `client/v3`'s `clientNewVars`, which `New` took as a premise)
    -- `defaultCallOpts` (`options.go`: `WaitForReady(true)`, `MaxCallSendMsgSize`,
    -- `MaxCallRecvMsgSize`: options holding only scalars) and the retry defaults
    (∃ (sl : GoSlice) (vs : List GoInterface), globalAddr go_etcd_io.etcd.client.v3.defaultCallOpts ↦□ sl ∗ sl ↦*□ vs ∗
      ⌜sl.len = sl.cap ∧ ∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧
        t ∈ [google_golang_org.grpc.StaticMethodCallOption.ty, google_golang_org.grpc.FailFastCallOption.ty,
          google_golang_org.grpc.MaxSendMsgSizeCallOption.ty,
          google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty]⌝) ∗
    (∃ n : w64, globalAddr go_etcd_io.etcd.client.v3.defaultUnaryMaxRetries ↦□ n) ∗
    (∃ d : time.Duration, globalAddr go_etcd_io.etcd.client.v3.defaultBackoffWaitBetween ↦□ d) ∗
    (∃ f : w64, globalAddr go_etcd_io.etcd.client.v3.defaultBackoffJitterFraction ↦□ f) ∗
    -- (2026-10-18: `client/v3`'s `clientWatchVars`, which the watcher took as a premise)
    -- `watch.go`'s `valCtxCh`, `zeroTime`, `maxBackoff`
    (∃ (ch : GoChan) (t : time.Time) (d : time.Duration),
      globalAddr go_etcd_io.etcd.client.v3.valCtxCh ↦□ ch ∗
      globalAddr go_etcd_io.etcd.client.v3.zeroTime ↦□ t ∗
      globalAddr go_etcd_io.etcd.client.v3.maxBackoff ↦□ d) ∗
    -- (item 1, the client lease, 2026-10-18) `lease.go`'s `LeaseResponseChSize` (never written)
    globalAddr go_etcd_io.etcd.client.v3.LeaseResponseChSize ↦□ (W64 16 : w64) ∗
    -- (real fmt stage 1, 2026-11-24) `client.go`'s `clientTargetSeq`, the counter `Client.dial`
    -- numbers its targets with (an `atomic.Uint64`, any value)
    inv clientTargetSeqN (∃ n : w64,
      _root_.Perennial.sync.atomic.ownUint64 (globalAddr go_etcd_io.etcd.client.v3.clientTargetSeq)
        (DFrac.own 1) n))

instance clientv3_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  define_is_pkg_init clientv3Init
instance clientv3_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  build_get_is_pkg_init_wf

-- `k8s.io/utils/third_party/forked/golang/btree`: `Proof/k8s_io/.../btree/Init.lean`.

/-- The cache's package facts: the error variables `ErrNotReady` (the store returns it),
`ErrUnsupportedRequest` (wrapped by `validateGet`/`validateWatch`), `ErrKeyRangeInvalid`
(`validateRange`) and `ErrCacheTimeout` (`waitTillRevision`), each a fixed non-nil error;
`ErrKeyRangeInvalid.Error()` returns some string (`errors.New`'s `*errorString`; `Cache.Watch`
puts it in a cancel response), and so does `ErrUnsupportedRequest.Error()` (`errors.New`'s too;
`fmt.Errorf`'s `%w` of it calls it, `fmt.argsOk`, which since premise-fixes-4 also asks that its
type, `*errors.errorString`, have no `Format` method). -/
abbrev cacheInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrNotReady ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrCacheTimeout ↦□ GoInterface.ok e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e -∗ errorStringSpec e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e -∗
      errorStringSpec e ∗ ⌜methodSet e.ty !! go!"Format" = none ∧
        methodSet e.ty !! go!"Error" = some EtcdGrove.noArgStringSig⌝))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  define_is_pkg_init cacheInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  build_get_is_pkg_init_wf

end init

section errstr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A non-nil error `err`'s `Error()` returns some string (`errorStringSpec`; persistent), and it
has no `Format` method (premise-fixes-4, 2026-11-10: else `fmt` calls `Format`) and its `Error` is
`Error() string` (`noArgStringSig`; fmt soundness 2, 2026-11-18; true of every non-nil Go `error`
value's dynamic type): what `fmt`'s `%v`/`%w` of it needs (`fmt.argsOk`). -/
def errStrOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ →
    errorStringSpec e ∗ ⌜methodSet e.ty !! go!"Format" = none ∧
      methodSet e.ty !! go!"Error" = some EtcdGrove.noArgStringSig⌝)

instance errStrOk_persistent (err : GoInterface) : Persistent (errStrOk (GF := GF) err) := by
  unfold errStrOk; infer_instance

theorem errStrOk_nil : ⊢ errStrOk (GF := GF) GoInterface.nil := by
  unfold errStrOk
  iintro !> %e %h
  cases h

theorem errStrOk_ok (e : GoInterfaceOk)
    (hF : methodSet e.ty !! go!"Format" = none ∧
      methodSet e.ty !! go!"Error" = some EtcdGrove.noArgStringSig) :
    errorStringSpec (GF := GF) e ⊢ errStrOk (GoInterface.ok e) := by
  unfold errStrOk
  iintro #H !> %e' %h
  cases h
  isplitl
  · iexact H
  · ipureintro; exact hF

/-- `errStrOk` of `ok e` gives `errorStringSpec e`. -/
theorem errStrOk_elim (e : GoInterfaceOk) : errStrOk (GF := GF) (GoInterface.ok e) ⊢ errorStringSpec e := by
  unfold errStrOk
  iintro #H
  ihave ⟨#Hs, -⟩ := H $$ %e %rfl
  iexact Hs

/-- `errStrOk` of `ok e`: `e` has no `Format` method. -/
theorem errStrOk_noFormat (e : GoInterfaceOk) :
    errStrOk (GF := GF) (GoInterface.ok e) ⊢ ⌜methodSet e.ty !! go!"Format" = none⌝ := by
  unfold errStrOk
  iintro #H
  ihave ⟨-, %hF⟩ := H $$ %e %rfl
  ipureintro; exact hF.1

/-- `errStrOk` of `ok e`: `e` has no `Format` method and its `Error` is `Error() string`. -/
theorem errStrOk_methods (e : GoInterfaceOk) :
    errStrOk (GF := GF) (GoInterface.ok e) ⊢ ⌜methodSet e.ty !! go!"Format" = none ∧
      methodSet e.ty !! go!"Error" = some EtcdGrove.noArgStringSig⌝ := by
  unfold errStrOk
  iintro #H
  ihave ⟨-, %hF⟩ := H $$ %e %rfl
  ipureintro; exact hF

/-- **`errors.New(msg)`'s error is an `errStrOk`** (premise-fixes-4): Perennial's model allocates an
`*errors.errorString` (as Go does), whose method set (goose's) has no `Format`; its `Error()`
returns `msg`. -/
theorem wp_New_errStrOk [_root_.Perennial.errors.Assumptions] (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.errors.New)) (Val #msg))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }}) ∗
        errStrOk (GoInterface.ok err) }} := by
  have hF := go.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Format"
  have hE := go.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Error"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hF hE
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  ihave #HM : (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Error" #x)) (Val #())) {{ Φ }}) $$ []
  · imodintro
    iintro %Φ HΦ
    rw [method_unfold]
    wp_auto
    iexact HΦ
  isplitr
  · iexact HM
  iapply errStrOk_ok _ ⟨hF, hE⟩
  unfold errorStringSpec
  iintro !> %Φ HΦ
  iapply HM
  inext
  iapply HΦ

/-- **`fmt.Errorf(format, args...)`'s error is an `errStrOk`**, for arguments of predeclared basic
types (premise-fixes-4): from Perennial's `fmt.wp_Errorf` (fmtmodel, 2026-11-20; until then over its
previous model, `errors.New(format)`), whose error has `Error() string`, no `Format`, and an `Error()`
returning the message. -/
theorem wp_Errorf_errStrOk [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    (format : GoString) (args_sl : GoSlice) (args : List GoAny)
    (hwf : _root_.Perennial.fmt.ArgsWf args) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errStrOk (GoInterface.ok err) }} := by
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  ihave Hok := _root_.Perennial.fmt.argsOk_of_argsWf (GF := GF)
    (mv := _root_.Perennial.fmt.errorfVerbs) (format := format) hwf
  wp_apply (_root_.Perennial.fmt.wp_Errorf format args_sl args (DFrac.own 1)) $$ [$Hpkg $Hsl $Hok]
    as %err ⟨-, %s, -, Herr⟩
  iunfold _root_.Perennial.fmt.errorfErr at Herr
  icases Herr with ⟨%hp, #HE, -⟩
  iapply HΦ
  iapply errStrOk_ok _ ⟨hp.2.1, hp.2.2.1⟩
  unfold errorStringSpec
  iintro !> %Ψ HΨ
  iapply HE
  inext
  iapply HΨ

theorem statusErrOk_nil : ⊢ statusErrOk (GF := GF) GoInterface.nil := by
  unfold statusErrOk
  iintro !> %e %h
  cases h

/-- The message clause of a call's precondition, for a `nil` error: vacuous, at any `m`. -/
theorem errMsgAt_nil (m : GoString) :
    ⊢ ∀ e : GoInterfaceOk, ⌜GoInterface.nil = GoInterface.ok e⌝ → errorMsgIs (GF := GF) e m := by
  iintro %e %h
  cases h

/-- **The message an error grpc's `status` accepts stably returns, fixed at a call** (fromerror-wand,
2026-11-18): what `status.FromError.spec`'s (and its callers') message parameter `m` is taken from. -/
theorem statusErrOk_msg (err : GoInterface) :
    statusErrOk (GF := GF) err ⊢
      ∃ m : GoString, ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ → errorMsgIs e m := by
  iintro #H
  cases err with
  | nil =>
    iexists go!""
    iintro %e %h
    cases h
  | ok e0 =>
    unfold statusErrOk
    icases H $$ %e0 %rfl with ⟨⟨%m, #Hm⟩, -⟩
    iexists m
    iintro %e %h
    cases h
    iexact Hm


/-- An error grpc's `status` accepts has some code (errdesc stage 2a). -/
theorem statusErrOk_code (err : GoInterface) :
    statusErrOk (GF := GF) err ⊢ ∃ c : w32, statusCodeIs err c := by
  iintro #H
  cases err with
  | nil =>
    iexists W32 0
    unfold statusCodeIs
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  | ok e0 =>
    unfold statusErrOk
    icases H $$ %e0 %rfl with ⟨-, -, #Hm, -⟩
    unfold grpcErrMethodsOk
    icases Hm with ⟨Hg, -⟩
    by_cases hg : methodSet e0.ty !! go!"GRPCStatus" = some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])
    · ihave ⟨%s, %c, %m, #Hst⟩ := Hg $$ %hg
      iexists c
      unfold statusCodeIs
      iright; iright
      iexists e0, s, m
      iframe Hst
      ipureintro; exact ⟨rfl, hg⟩
    · iexists W32 2
      unfold statusCodeIs
      iright; ileft
      iexists e0
      ipureintro; exact ⟨rfl, hg, rfl⟩

/-- **A context error wrapped by `%w`** (one or more levels; errorf-wrap, 2026-11-06; persistent):
`rangeKeys`' `fmt.Errorf("rangeKeys: context cancelled: %w", ctx.Err())` (`kvstore_txn.go:121`) and
`executeTxn`'s wrapping of it (`txn.go:162`): a chain of `fmt.Errorf` `%w` errors (`fmt.wrapChain`,
each level the model's error or Go's `*fmt.wrapError`) ending at `context.Canceled`'s or
`context.DeadlineExceeded`'s value (`context.isCtxErr`). -/
def ctxWrapErr (err : GoInterface) : IProp GF :=
  iprop(∃ (pres : List GoString) (c : GoInterface),
    ⌜pres ≠ []⌝ ∗ EtcdGrove.fmt.wrapChain pres err c ∗ context.isCtxErr c)

instance ctxWrapErr_persistent (err : GoInterface) : Persistent (ctxWrapErr (GF := GF) err) := by
  unfold ctxWrapErr; infer_instance

/-- **A handler's error, as grpc's server and the prometheus interceptor take it** (errorf-wrap,
2026-11-06; persistent): one grpc's `status` accepts (`statusErrOk`), or a context error wrapped by
`%w` (`ctxWrapErr`), which `togRPCError` passes through as it is (`errors.Is` sees the context
error). Go's server answers the latter with the context error's code (`status.FromContextError`),
grpc-prometheus's `FromError` with `Unknown`, neither panicking (`notes/axiom-review/errorf-wrap.md`).
The handler contracts' result (`grpcHandlerOk`, `grpcMethodOk`, `srvInterceptorOk`). -/
def srvErrOk (err : GoInterface) : IProp GF :=
  iprop(statusErrOk err ∨ ctxWrapErr err)

instance srvErrOk_persistent (err : GoInterface) : Persistent (srvErrOk (GF := GF) err) := by
  unfold srvErrOk; infer_instance

theorem srvErrOk_of_statusErrOk (err : GoInterface) :
    statusErrOk (GF := GF) err ⊢ srvErrOk err := by
  iintro #H
  unfold srvErrOk
  ileft
  iexact H

theorem srvErrOk_nil : ⊢ srvErrOk (GF := GF) GoInterface.nil := by
  iapply srvErrOk_of_statusErrOk
  iapply statusErrOk_nil

/-- A pointer type is not `EtcdError`'s (a named struct type). -/
theorem ptrTy_ne_etcdError (T : go.GoType) :
    go.GoType.PointerType T ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty := by
  intro h
  unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty at h
  cases h

theorem modelErrIs_descIs [EtcdGrove.ErrorStringLeaf] (ii : GoInterfaceOk) (pre : GoString) :
    EtcdGrove.fmt.modelErrIs (GF := GF) ii pre ⊢
      ∃ s : GoString, descIs (GoInterface.ok ii) (pre ++ s) := by
  iintro #H
  iunfold EtcdGrove.fmt.modelErrIs at H
  icases H with ⟨%x, %hx, %s, -, #He⟩
  subst hx
  iexists s
  iapply (descIs_of_msg _ _ (ptrTy_ne_etcdError _) (by rw [EtcdGrove.ErrorStringLeaf.noGRPC]; simp))
  unfold errorMsgIs
  imodintro
  iexact He

theorem wrapErrIs_descIs (ii : GoInterfaceOk) (inner : GoInterface) (pre : GoString) :
    EtcdGrove.fmt.wrapErrIs (GF := GF) ii inner pre ⊢
      ∃ s : GoString, descIs (GoInterface.ok ii) (pre ++ s) := by
  iintro #H
  iunfold EtcdGrove.fmt.wrapErrIs at H
  icases H with ⟨%hm, ⟨%s, #He⟩, -⟩
  obtain ⟨⟨T, l, hT, -⟩, -, -, -, hg, -, -⟩ := hm
  iexists s
  iapply (descIs_of_msg _ _ (by rw [hT]; exact ptrTy_ne_etcdError _) (by rw [hg]; simp))
  unfold errorMsgIs
  imodintro
  iexact He

/-- **`fmt.Errorf(pre ++ "%w", inner)`'s description starts with `pre`** (proved; errdesc stage 2b,
2026-11-21: until then `fmt.ErrorfWrap`'s post said so of the pure `errDesc`, conditional on Go's
`Unwrap`): the model's `*errors.errorString` and Go's `*fmt.wrapError` have no `GRPCStatus`, and their
`Error()` stably returns `pre ++ s`. -/
theorem errorfWrap_descIs [EtcdGrove.ErrorStringLeaf] (ii : GoInterfaceOk) (inner : GoInterface)
    (pre : GoString) :
    EtcdGrove.fmt.errorfWrapIs (GF := GF) ii inner pre ⊢
      ∃ s : GoString, descIs (GoInterface.ok ii) (pre ++ s) := by
  iintro #H
  iunfold EtcdGrove.fmt.errorfWrapIs at H
  icases H with (#H | #H)
  · iapply modelErrIs_descIs $$ H
  · iapply wrapErrIs_descIs $$ H

/-- **A `ctxWrapErr` has some description** (its outer level's). -/
theorem ctxWrapErr_descIs [EtcdGrove.ErrorStringLeaf] (err : GoInterface) :
    ctxWrapErr (GF := GF) err ⊢ ∃ m : GoString, descIs err m := by
  iintro #H
  unfold ctxWrapErr
  icases H with ⟨%pres, %c, %hp, #Hch, -⟩
  cases pres with
  | nil => exact absurd rfl hp
  | cons pre ps =>
    rw [EtcdGrove.fmt.wrapChain_cons]
    icases Hch with ⟨%ii, %he, Hl⟩
    subst he
    icases Hl with (#Hm | ⟨%mid, #Hw, -⟩)
    · ihave ⟨%s, #Hd⟩ := modelErrIs_descIs $$ Hm
      iexists _; iexact Hd
    · ihave ⟨%s, #Hd⟩ := wrapErrIs_descIs $$ Hw
      iexists _; iexact Hd

/-- **A handler's error has some description**. -/
theorem srvErrOk_descIs [EtcdGrove.ErrorStringLeaf] (err : GoInterface) :
    srvErrOk (GF := GF) err ⊢ ∃ m : GoString, descIs err m := by
  iintro #H
  unfold srvErrOk
  icases H with (#H | #H)
  · iapply statusErrOk_descIs $$ H
  · iapply ctxWrapErr_descIs $$ H

/-- **A `%w` of a context error is a `ctxWrapErr`** (`rangeKeys`'). -/
theorem ctxWrapErr_wrap (ii : GoInterfaceOk) (c : GoInterface) (pre : GoString) :
    EtcdGrove.fmt.errorfWrapIs (GF := GF) ii c pre -∗ context.isCtxErr c -∗
      ctxWrapErr (GoInterface.ok ii) := by
  iintro #Hw #Hc
  unfold ctxWrapErr
  iexists [pre], c
  isplitr
  · ipureintro; simp
  iframe Hc
  rw [EtcdGrove.fmt.wrapChain_cons]
  iexists ii
  isplitr
  · ipureintro; rfl
  iunfold EtcdGrove.fmt.errorfWrapIs at Hw
  icases Hw with (#Hm | #Hw)
  · ileft; iexact Hm
  · iright; iexists c; iframe Hw; (try rw [EtcdGrove.fmt.wrapChain_nil]); ipureintro; rfl

/-- **A `%w` of a `ctxWrapErr` is one** (`executeTxn`'s wrapping of `rangeKeys`' error). -/
theorem ctxWrapErr_wrap2 (ii : GoInterfaceOk) (e : GoInterface) (pre : GoString) :
    EtcdGrove.fmt.errorfWrapIs (GF := GF) ii e pre -∗ ctxWrapErr e -∗
      ctxWrapErr (GoInterface.ok ii) := by
  iintro #Hw #He
  unfold ctxWrapErr
  icases He with ⟨%pres, %c, -, #Hch, #Hc⟩
  iexists (pre :: pres), c
  isplitr
  · ipureintro; simp
  iframe Hc
  rw [EtcdGrove.fmt.wrapChain_cons]
  iexists ii
  isplitr
  · ipureintro; rfl
  iunfold EtcdGrove.fmt.errorfWrapIs at Hw
  icases Hw with (#Hm | #Hw)
  · ileft; iexact Hm
  · iright; iexists e; iframe Hw Hch

/-- **A `ctxWrapErr`'s `Error()` returns**, as `fmt` needs of a `%w` argument. -/
theorem ctxWrapErr_stringMethodSpec [_root_.Perennial.fmt.Assumptions] (ii : GoInterfaceOk) :
    ctxWrapErr (GF := GF) (GoInterface.ok ii) ⊢ _root_.Perennial.fmt.stringMethodSpec ii go!"Error" := by
  iintro #He
  unfold ctxWrapErr
  icases He with ⟨%pres, %c, %Hp, #Hch, -⟩
  cases pres with
  | nil => exact absurd rfl Hp
  | cons pre ps =>
    rw [EtcdGrove.fmt.wrapChain_cons]
    icases Hch with ⟨%ii', %Hii, Hch⟩
    cases Hii
    icases Hch with (#Hm | ⟨%mid, #Hw, -⟩)
    · iunfold EtcdGrove.fmt.modelErrIs at Hm
      icases Hm with ⟨%x, -, %s, -, #Hs⟩
      unfold _root_.Perennial.fmt.stringMethodSpec
      iintro !> %Φ HΦ
      iapply Hs
      inext
      iapply HΦ
    · iunfold EtcdGrove.fmt.wrapErrIs at Hw
      icases Hw with ⟨-, ⟨%s, #Hs⟩, -⟩
      unfold _root_.Perennial.fmt.stringMethodSpec
      iintro !> %Φ HΦ
      iapply Hs
      inext
      iapply HΦ

/-- **A `ctxWrapErr` is one `fmt` formats by its `Error()`** (`fmtErrorOk`: `Error() string`, no
`Format`), as `fmt.ErrorfWrap` needs of its `%w` argument (fmt soundness, 2026-11-18): the chain's
head is the model's `*errors.errorString` (its method set) or Go's `*fmt.wrapError`
(`fmt.wrapErrIs`'s facts). -/
theorem ctxWrapErr_fmtErrorOk [_root_.Perennial.fmt.Assumptions] (ii : GoInterfaceOk) :
    ctxWrapErr (GF := GF) (GoInterface.ok ii) ⊢ EtcdGrove.fmtErrorOk (GoInterface.ok ii) := by
  iintro #He
  ihave #Hs := ctxWrapErr_stringMethodSpec ii $$ He
  simp only [EtcdGrove.fmtErrorOk]
  isplit
  rotate_left
  · iexact Hs
  unfold ctxWrapErr
  icases He with ⟨%pres, %c, %Hp, #Hch, -⟩
  cases pres with
  | nil => exact absurd rfl Hp
  | cons pre ps =>
    rw [EtcdGrove.fmt.wrapChain_cons]
    icases Hch with ⟨%ii', %Hii, Hch⟩
    cases Hii
    icases Hch with (#Hm | ⟨%mid, #Hw, -⟩)
    · iunfold EtcdGrove.fmt.modelErrIs at Hm
      icases Hm with ⟨%x, %hx, -⟩
      subst hx
      ipureintro
      have h1 := (go.MethodSetIs.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Format")
      have h2 := (go.MethodSetIs.method_set_is
        (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Error")
      simp only [go.methodSetLookup] at h1 h2
      exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
    · iunfold EtcdGrove.fmt.wrapErrIs at Hw
      icases Hw with ⟨%Hm, -, -⟩
      ipureintro
      exact ⟨Hm.2.2.2.2.2.1, Hm.2.2.2.2.2.2⟩

/-- A stable `Error()` returns (`errorStringSpec`). -/
theorem errorMsgIs_errorStringSpec (e : GoInterfaceOk) (m : GoString) :
    errorMsgIs (GF := GF) e m ⊢ errorStringSpec e := by
  unfold errorMsgIs errorStringSpec
  iintro #H !> %Φ HΦ
  iapply H
  inext
  iapply HΦ

/-- An error grpc's `status` accepts has an `Error()` returning some string. -/
theorem errStrOk_of_statusErrOk (err : GoInterface) :
    statusErrOk (GF := GF) err ⊢ errStrOk err := by
  unfold statusErrOk errStrOk
  iintro #H !> %e %h
  ihave ⟨⟨%m, #He⟩, -, -, %hF, -⟩ := H $$ %e %h
  isplitl
  · iapply errorMsgIs_errorStringSpec $$ He
  · ipureintro; exact hF

/-- The `Error()` of an error with a known message (`errors.wp_New`'s) returns some string. -/
theorem errorStringSpec_of_msg (e : GoInterfaceOk) (msg : GoString) :
    iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }}) ⊢ errorStringSpec e := by
  unfold errorStringSpec
  iintro #H !> %Φ HΦ
  iapply H
  inext
  iapply HΦ

/-- **The messages of the `errors.New` errors a unary call of the client can return** (D37):
io's `EOF`, which grpc's `invoke` may return as it is (its `toRPCErr` passes `io.EOF` through and
turns every other error into a status error, or keeps one carrying a status: grpc v1.84,
`rpc_util.go`), and context's `Canceled` (a caller's context's `Err()`, which the client's
`toErr` returns in place of a canceled call's status). Every other error such a call returns has
another dynamic type (a grpc status error, an `rpctypes.EtcdError`, context's
`deadlineExceededError`). -/
def clientErrMsgs : List GoString := [go!"EOF", go!"context canceled"]

/-- **An error that is no caller's own `errors.New` value** (persistent; D37): if it is an
`*errors.errorString`, it is a pointer `x` (what `errors.New` returns) whose cell holds one of
`clientErrMsgs` for good (the `s` field, which only `errors.New` writes: `errStrCell`). A caller's
`errors.New(msg)` error, `msg` not among them, is then a different value (`errCellOk_ne`), and, the
client's errors being leaves (`clientErr`), not `errors.Is` it either; and comparing it with `==`
compares pointers (`errCellOk_ptr`). What a program that tells its own errors apart from the
client's needs (Kubernetes' storage test: `errDeleteRejected`, `errUpdateRejected`). -/
def errCellOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ ii : GoInterfaceOk,
    ⌜err = GoInterface.ok ii ∧
      ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty⌝ →
    ∃ (x : Loc) (m : GoString), ⌜ii.v = #x ∧ m ∈ clientErrMsgs⌝ ∗
      x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ m)

instance errCellOk_persistent (err : GoInterface) : Persistent (errCellOk (GF := GF) err) := by
  unfold errCellOk; infer_instance

theorem errCellOk_nil : ⊢ errCellOk (GF := GF) GoInterface.nil := by
  unfold errCellOk
  iintro !> %ii %h
  exact absurd h.1 nofun

/-- An error of a dynamic type other than `*errors.errorString`. -/
theorem errCellOk_of_ty (e : GoInterfaceOk)
    (h : e.ty ≠ go.GoType.PointerType _root_.Perennial.errors.errorString.ty) :
    ⊢ errCellOk (GF := GF) (GoInterface.ok e) := by
  unfold errCellOk
  iintro !> %ii %he
  obtain ⟨he, ht⟩ := he
  injection he with he
  subst he
  exact absurd ht h

/-- An `*errors.errorString` whose cell holds one of `clientErrMsgs`. -/
theorem errCellOk_of_cell (x : Loc) (m : GoString) (hm : m ∈ clientErrMsgs) :
    x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ m ⊢
      errCellOk (GF := GF)
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  unfold errCellOk
  iintro #Hc !> %ii %he
  obtain ⟨he, -⟩ := he
  injection he with he
  subst he
  iexists x, m
  iframe Hc
  ipureintro; exact ⟨rfl, hm⟩

/-- **A client error is not a caller's `errors.New(msg)` value** of a message `msg` not among
`clientErrMsgs`. -/
theorem errCellOk_ne (err : GoInterface) (y : Loc) (msg : GoString) (hmsg : msg ∉ clientErrMsgs) :
    errCellOk (GF := GF) err ⊢ y.[_root_.Perennial.errors.errorString, go!"s"] ↦□ msg -∗
      ⌜err ≠ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #y⌝ := by
  unfold errCellOk
  iintro #H #Hy
  by_cases he : err = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #y
  · have hh : err = GoInterface.ok
          ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #y⟩ ∧
        go.GoType.PointerType _root_.Perennial.errors.errorString.ty =
          go.GoType.PointerType _root_.Perennial.errors.errorString.ty := ⟨he, rfl⟩
    ihave ⟨%x, %m, %hxm, #Hm⟩ := H $$ %_ %hh
    obtain ⟨hx, hm⟩ := hxm
    have hxy : y = x := go.intoVal_inj (V := Loc) hx
    subst hxy
    icombine Hy Hm gives %h
    exact absurd (h ▸ hm) hmsg
  · ipureintro; exact he

/-- **A client error of type `*errors.errorString` holds a pointer** (what `errors.New` returns),
so that `==` on it compares pointers. -/
theorem errCellOk_ptr (ii : GoInterfaceOk) :
    errCellOk (GF := GF) (GoInterface.ok ii) ⊢
      ⌜ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty →
        ∃ l : Loc, ii.v = #l⌝ := by
  unfold errCellOk
  iintro #H
  by_cases ht : ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty
  · have hh : GoInterface.ok ii = GoInterface.ok ii ∧
        ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty := ⟨rfl, ht⟩
    ihave ⟨%x, %m, %hxm, -⟩ := H $$ %ii %hh
    ipureintro; exact fun _ => ⟨x, hxm.1⟩
  · ipureintro; exact fun h => absurd h ht

end errstr

section ctxErrStr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A context error's `Error()` returns** (`context.wp_isCtxErr_Error`), as `fmt` needs of a
`%w` argument. -/
theorem isCtxErr_stringMethodSpec [context.Assumptions] [_root_.Perennial.fmt.Assumptions]
    (ii : GoInterfaceOk) :
    context.isCtxErr (GF := GF) (GoInterface.ok ii) ⊢ _root_.Perennial.fmt.stringMethodSpec ii go!"Error" := by
  iintro #He
  unfold _root_.Perennial.fmt.stringMethodSpec
  iintro !> %Φ HΦ
  wp_apply (context.wp_isCtxErr_Error (GoInterface.ok ii) ii rfl) $$ He as %s -
  iapply HΦ

/-- **A context error is one `fmt` formats by its `Error()`** (`fmtErrorOk`): `Canceled`'s
`*errors.errorString` or `DeadlineExceeded`'s `deadlineExceededError`, by their method sets (fmt
soundness, 2026-11-18: what `fmt.ErrorfWrap` needs of its `%w` argument). -/
theorem isCtxErr_fmtErrorOk [context.Assumptions] [_root_.Perennial.fmt.Assumptions]
    (ii : GoInterfaceOk) :
    context.isCtxErr (GF := GF) (GoInterface.ok ii) ⊢ EtcdGrove.fmtErrorOk (GoInterface.ok ii) := by
  iintro #He
  ihave #Hs := isCtxErr_stringMethodSpec ii $$ He
  simp only [EtcdGrove.fmtErrorOk]
  isplit
  rotate_left
  · iexact Hs
  iunfold context.isCtxErr at He
  icases He with (⟨-, %x, %hx, -⟩ | ⟨-, %hv⟩)
  · rw [interface.mkOk] at hx; cases hx
    ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
  · rw [interface.mkOk] at hv; cases hv
    ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩

end ctxErrStr


end go_etcd_io.etcd.cache.v3

end Perennial
