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
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.cache.v3

section desc

/-- **An error's description** (opaque; D29, 2026-10-21): what `rpctypes.ErrorDesc(err)` returns,
the status message (`status.FromError(err).Message()`), which for an error that is not a status
error is its `Error()` (`Spec/google_golang_org/grpc/status/FromError.lean`). grpc's `FromError`
reads the status embedded in the error value, so the description is a function of the error, as
its code is (`statusCode`); nothing more is said of it. -/
opaque errDesc [FfiSyntax] : GoInterface → GoString

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

/-- **An error that is not a refusal** (D29): `nil`, or one whose description is not a refusal's. -/
def noRefusal [FfiSyntax] (err : GoInterface) : Prop :=
  err = GoInterface.nil ∨ errDesc err ∉ refusalDescs

end desc

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

instance protobuf_pragma_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  define_is_pkg_init iprop(True)
instance protobuf_pragma_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  build_get_is_pkg_init_wf

instance protobuf_impl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  define_is_pkg_init iprop(True)
instance protobuf_impl_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  build_get_is_pkg_init_wf

instance protoimpl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  define_is_pkg_init iprop(True)
instance protoimpl_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  build_get_is_pkg_init_wf

instance mvccpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  define_is_pkg_init iprop(True)
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

-- `protoreflect` (names only), before `authpb`, whose translation imports it (the auth plan's S1,
-- 2026-10-23: `authpb`'s messages and getters are translated with bodies, `authpb.toml`).
instance protoreflect_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  define_is_pkg_init iprop(True)
instance protoreflect_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
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

-- `google.golang.org/grpc/metadata` (types and names only), before `grpc`, which imports it
-- (unit W-W: grpc's `ClientStream`/`ServerStream` name `metadata.MD`; moved here from
-- `server/v3/auth/Base.lean`)
namespace google_golang_org.grpc.metadata

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.metadata :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.metadata :=
  build_get_is_pkg_init_wf

end google_golang_org.grpc.metadata

-- `grpc` (names only; `etcdserverpb`'s streams are its generic interfaces, 2026-10-12: the
-- request path's `RaftKV` names `KV_RangeStreamServer`), before `etcdserverpb`, which imports it
instance grpc_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc :=
  define_is_pkg_init iprop(True)
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

/-- A generated `ServiceDesc` of service `sn` for the interface `T`, with distinct method and
stream names. -/
def pbDescOk (sd : Loc) (sn : GoString) (T : go.GoType) : IProp GF :=
  iprop(∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
    pbDescIs sd sn (interface.mkOk (go.GoType.PointerType T) #(null : Loc)) mds sds ∗
    ⌜(mds.map (·.MethodName') ++ sds.map (·.StreamName')).Nodup⌝)

instance pbDescOk_persistent (sd : Loc) (sn : GoString) (T : go.GoType) :
    Persistent (pbDescOk (GF := GF) sd sn T) := by
  unfold pbDescOk; infer_instance

/-- **`etcdserverpb`'s six `ServiceDesc`s** (`rpc_grpc.pb.go`: generated literals, never written;
item 8, 2026-10-17: until then an assumption of `v3rpc.Server`, `svcDescsOk`): their service names,
handler types and distinct method and stream names; the KV service's methods and the Watch
service's stream exactly (2026-10-18: the Watch stream a client stream, `ClientStreams`, which
`grpc.ClientConn.NewStream`'s spec asks of its descriptor; and the Lease service's stream, the client
lease's keep-alive). -/
abbrev etcdserverpbDescs : IProp GF :=
  iprop((∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.KV_ServiceDesc) go!"etcdserverpb.KV"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.KVServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
          [(go!"Range", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Range_Handler), (go!"Put", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Put_Handler),
           (go!"DeleteRange", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_DeleteRange_Handler),
           (go!"Txn", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Txn_Handler), (go!"Compact", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Compact_Handler)] ∧
        sds.map (·.StreamName') = [go!"RangeStream"]⌝) ∗
    (∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Watch_ServiceDesc) go!"etcdserverpb.Watch"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.WatchServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds = [] ∧ sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val))) =
        [(go!"Watch", @! go_etcd_io.etcd.api.v3.etcdserverpb._Watch_Watch_Handler)] ∧
        sds.map (·.ClientStreams') = [true]⌝) ∗
    pbDescOk (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Lease_ServiceDesc) go!"etcdserverpb.Lease" go_etcd_io.etcd.api.v3.etcdserverpb.LeaseServer.ty ∗
    pbDescOk (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Cluster_ServiceDesc) go!"etcdserverpb.Cluster" go_etcd_io.etcd.api.v3.etcdserverpb.ClusterServer.ty ∗
    pbDescOk (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Auth_ServiceDesc) go!"etcdserverpb.Auth" go_etcd_io.etcd.api.v3.etcdserverpb.AuthServer.ty ∗
    pbDescOk (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Maintenance_ServiceDesc) go!"etcdserverpb.Maintenance"
      go_etcd_io.etcd.api.v3.etcdserverpb.MaintenanceServer.ty ∗
    -- (item 1, the client lease, 2026-10-18) the Lease service's one stream, `LeaseKeepAlive`, a
    -- client stream (what `grpc.ClientConn.NewStream`'s spec asks of its descriptor)
    (∃ (ssl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
      structFieldRef google_golang_org.grpc.ServiceDesc go!"Streams"
        (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Lease_ServiceDesc) ↦□ ssl ∗ ssl ↦*□ sds ∗
      ⌜sds.map (·.ClientStreams') = [true]⌝))

/-- **`etcdserverpb`'s fact** (item 8, 2026-10-17: moved here from `v3rpc`'s `sortNameMaps`): the
enumerations' name maps `checkRangeRequest` looks the sort order and target up in
(`RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`: generated `map[int32]string`
literals), fixed maps whose keys are the enumerations' values, `0` to `2` and `0` to `4`; and its
six `ServiceDesc`s (`etcdserverpbDescs`). -/
abbrev etcdserverpbInit : IProp GF :=
  iprop((∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortOrder_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝) ∗
    (∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortTarget_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝) ∗
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

/-- **The methods grpc's `status` and Go's `errors.Is` call on the error `e` return**
(persistent; unit P3a), if `e`'s type has them (both are called through a type assertion):
`GRPCStatus() *Status` (`status.FromError`/`Code`/`Convert`) and `Is(error) bool`
(`errors.Is`, for any target). -/
def grpcErrMethodsOk (e : GoInterfaceOk) : IProp GF :=
  iprop((⌜methodSet e.ty !! go!"GRPCStatus" =
      some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])⌝ →
    □ ∀ Φ : val → IProp GF, ▷ (∀ s : Loc, Φ #s) -∗
      WP (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #())) {{ Φ }}) ∗
    (⌜methodSet e.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool])⌝ →
    □ ∀ (target : GoInterface) (Φ : val → IProp GF), ▷ (∀ b : Bool, Φ #b) -∗
      WP (App (Val #(methods e.ty go!"Is" e.v)) (Val #target)) {{ Φ }}))

/-- **An error grpc's `status` functions accept** (persistent; unit P3a): `nil`, or a leaf error
(`errors.isLeafError`: no `Unwrap` or `As` method, so `status.FromError`'s and `errors.Is`'s walks
of its error tree only check it) whose `Error()` returns some string (`errorStringSpec`:
`FromError` calls it unless the error is a status error) and whose `GRPCStatus()` and `Is`, if it
has them, return (`grpcErrMethodsOk`). What `status.FromError` (`Spec/google_golang_org/grpc/
status/FromError.lean`), `status.Code`, `errors.Is` (`Spec/errors/IsStatusErr.lean`), and through
them `rpctypes.Error` and the client's retry interceptor, need. -/
def statusErrOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ →
    errorStringSpec e ∗ ⌜errors.isLeafError e⌝ ∗ grpcErrMethodsOk e)

instance statusErrOk_persistent (err : GoInterface) : Persistent (statusErrOk (GF := GF) err) := by
  unfold statusErrOk; infer_instance

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
(unit P3a). -/
def rpctypesEtcdErrorTy : Prop :=
  (∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩) ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none

/-- `rpctypes`' package facts: the two errors the store returns; `ErrCompacted.Error()`
(the watcher's `Compact` puts it in the cancel response) returns some string, and so does
`ErrFutureRev.Error()` (`WatchResponse.Err` returns it; both are `EtcdError`s, whose `Error`
returns their description); and (unit P3a: `rpctypes.Error` is translated) the map
`errStringToError` (never written after init) whose values (the `ErrGRPC*` errors, `status.Error`'s
`*status.Error`s) grpc's `status.FromError` accepts (`statusErrOk`), `EtcdError`'s method set
(`rpctypesEtcdErrorTy`), the `EtcdError` values the client's retry interceptor compares with
(`ErrUserEmpty`, `ErrInvalidAuthToken`, `ErrAuthOldRevision`: `Error` of an `ErrGRPC*`) and its
`ErrGRPCNotSupportedForLearner` (a `*status.Error`, a pointer); and (item 8, 2026-10-17: moved here
from `auth`'s facts, so that `rpctypes`' initializer proves them) the token keys
`TokenFieldNameGRPC`, `TokenFieldNameSwagger` (fixed strings). -/
abbrev rpctypesInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
    □ (∀ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e -∗
      errorStringSpec e) ∗
    (∃ (mref : Loc) (m : GMap GoString GoInterface),
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.errStringToError ↦□ mref ∗ mref ↦$□ m ∗
      □ (∀ (k : GoString) (v : GoInterface), ⌜m !! k = some v⌝ → statusErrOk v) ∗
      -- (D29, 2026-10-21) each value's description is its key (`ErrorDesc(ErrGRPCx): ErrGRPCx`)
      ⌜∀ (k : GoString) (v : GoInterface), m !! k = some v → errDesc v = k⌝) ∗
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
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: rpc not supported for learner"⌝) ∗
    (∃ s : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameGRPC ↦□ s) ∗
    (∃ s : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.TokenFieldNameSwagger ↦□ s) ∗
    -- (item 8, 2026-10-17: moved here from `v3rpc`'s facts) the `ErrGRPC*` errors the gRPC
    -- service's checks and interceptors return, fixed non-nil errors, and the metadata keys
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoSpace ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotCapable ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidClientAPIVersion ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader ↦□ GoInterface.ok e) ∗
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
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWatchCanceled ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
    -- (item 1, the client lease, 2026-10-18) `ErrNoLeader`, an `EtcdError` (the client's lease
    -- keep-alive loop compares a stream's error with it)
    (∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrNoLeader ↦□
        interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x))

instance rpctypes_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  define_is_pkg_init rpctypesInit
instance rpctypes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  build_get_is_pkg_init_wf

-- The names-only packages of `clientv3.Client`'s field types.

-- `net` (names only; unit P3a: the type of grpc's `peer.Peer`'s fields; item 5: grpc's
-- `credentials` imports it, for `TransportCredentials`'s handshakes).
instance net_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.net :=
  define_is_pkg_init iprop(True)
instance net_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net :=
  build_get_is_pkg_init_wf

instance grpc_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.credentials :=
  define_is_pkg_init iprop(True)
instance grpc_credentials_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.credentials :=
  build_get_is_pkg_init_wf

-- grpc's `peer` (names only; unit P3a: the retry interceptor's `peer.Peer`).
instance grpc_peer_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.peer :=
  define_is_pkg_init iprop(True)
instance grpc_peer_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.peer :=
  build_get_is_pkg_init_wf

instance clientv3_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials :=
  define_is_pkg_init iprop(True)
instance clientv3_credentials_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials :=
  build_get_is_pkg_init_wf

instance clientv3_resolver_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver :=
  define_is_pkg_init iprop(True)
instance clientv3_resolver_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver :=
  build_get_is_pkg_init_wf

-- Names only (item 5, client construction, branch `construct`): what `clientv3.New`'s dial
-- names (the type of `Config.TLS`, grpc's keepalive parameters and insecure credentials, an
-- endpoint's credentials requirement, the default logger); `logutil`'s instance moved here from
-- `etcdserver/BaseApply.lean` (stage R8b), now that `clientv3` imports it.
instance tls_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.crypto.tls :=
  define_is_pkg_init iprop(True)
instance tls_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.crypto.tls :=
  build_get_is_pkg_init_wf
instance grpc_keepalive_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.keepalive :=
  define_is_pkg_init iprop(True)
instance grpc_keepalive_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.keepalive :=
  build_get_is_pkg_init_wf
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

-- zap imports zapcore (translated since the merge with the server's names-only zap).
instance zapcore_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  define_is_pkg_init iprop(True)
instance zapcore_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  build_get_is_pkg_init_wf

instance zap_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap :=
  define_is_pkg_init iprop(True)
instance zap_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap :=
  build_get_is_pkg_init_wf

-- protobuf's `proto` (`clientv3.cloneCompare` calls `proto.Clone`; names only; `protoreflect`,
-- which it imports, is above `authpb`).
instance proto_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  define_is_pkg_init iprop(True)
instance proto_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  build_get_is_pkg_init_wf

/-- **A backoff function** (`clientv3.backoffFunc`, `func(attempt uint) time.Duration`) that
returns (persistent; unit P3a: the retry interceptor's `waitRetryBackoff` calls it). -/
def backoffOk (bf : GoFunc) : IProp GF :=
  iprop(□ ∀ (a : w64) (Φ : val → IProp GF), ▷ (∀ d : w64, Φ #d) -∗
    WP (App (Val #bf) (Val #a)) {{ Φ }})

instance backoffOk_persistent (bf : GoFunc) : Persistent (backoffOk (GF := GF) bf) := by
  unfold backoffOk; infer_instance

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
    globalAddr go_etcd_io.etcd.client.v3.LeaseResponseChSize ↦□ (W64 16 : w64))

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
`fmt.Errorf`'s `%w` of it calls it, `fmt.argsOk`). -/
abbrev cacheInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrNotReady ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrCacheTimeout ↦□ GoInterface.ok e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e -∗ errorStringSpec e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e -∗
      errorStringSpec e))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  define_is_pkg_init cacheInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  build_get_is_pkg_init_wf

end init

section errstr
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A non-nil error `err`'s `Error()` returns some string (`errorStringSpec`; persistent): what
`fmt`'s `%v`/`%w` of it needs (`fmt.argsOk`). -/
def errStrOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ → errorStringSpec e)

instance errStrOk_persistent (err : GoInterface) : Persistent (errStrOk (GF := GF) err) := by
  unfold errStrOk; infer_instance

theorem errStrOk_nil : ⊢ errStrOk (GF := GF) GoInterface.nil := by
  unfold errStrOk
  iintro !> %e %h
  cases h

theorem errStrOk_ok (e : GoInterfaceOk) : errorStringSpec (GF := GF) e ⊢ errStrOk (GoInterface.ok e) := by
  unfold errStrOk
  iintro #H !> %e' %h
  cases h
  iexact H

/-- `errStrOk` of `ok e` gives `errorStringSpec e`. -/
theorem errStrOk_elim (e : GoInterfaceOk) : errStrOk (GF := GF) (GoInterface.ok e) ⊢ errorStringSpec e := by
  unfold errStrOk
  iintro #H
  iapply H
  ipureintro; rfl

theorem statusErrOk_nil : ⊢ statusErrOk (GF := GF) GoInterface.nil := by
  unfold statusErrOk
  iintro !> %e %h
  cases h

/-- An error grpc's `status` accepts has an `Error()` returning some string. -/
theorem errStrOk_of_statusErrOk (err : GoInterface) :
    statusErrOk (GF := GF) err ⊢ errStrOk err := by
  unfold statusErrOk errStrOk
  iintro #H !> %e %h
  ihave ⟨#He, -⟩ := H $$ %e %h
  iexact He

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
`*errors.errorString` at `x`, the cell of `x` holds one of `clientErrMsgs` for good (the `s`
field, which only `errors.New` writes: `errStrCell`). A caller's `errors.New(msg)` error, `msg`
not among them, is then a different value (`errCellOk_ne`), and, the client's errors being leaves
(`clientErr`), not `errors.Is` it either. What a program that tells its own errors apart from the
client's needs (Kubernetes' storage test: `errDeleteRejected`, `errUpdateRejected`). -/
def errCellOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ x : Loc,
    ⌜err = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x⌝ →
    ∃ m : GoString, ⌜m ∈ clientErrMsgs⌝ ∗ x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ m)

instance errCellOk_persistent (err : GoInterface) : Persistent (errCellOk (GF := GF) err) := by
  unfold errCellOk; infer_instance

theorem errCellOk_nil : ⊢ errCellOk (GF := GF) GoInterface.nil := by
  unfold errCellOk
  iintro !> %x %h
  cases h

/-- An error of a dynamic type other than `*errors.errorString`. -/
theorem errCellOk_of_ty (e : GoInterfaceOk)
    (h : e.ty ≠ go.GoType.PointerType _root_.Perennial.errors.errorString.ty) :
    ⊢ errCellOk (GF := GF) (GoInterface.ok e) := by
  unfold errCellOk
  iintro !> %x %he
  injection he with he
  exact absurd (congrArg GoInterfaceOk.ty he) h

/-- An `*errors.errorString` whose cell holds one of `clientErrMsgs`. -/
theorem errCellOk_of_cell (x : Loc) (m : GoString) (hm : m ∈ clientErrMsgs) :
    x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ m ⊢
      errCellOk (GF := GF)
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  unfold errCellOk
  iintro #Hc !> %y %he
  have hy : x = y := by
    injection he with he
    injection he with _ hv
    exact go.intoVal_inj (V := Loc) hv
  subst hy
  iexists m
  iframe Hc
  ipureintro; exact hm

/-- **A client error is not a caller's `errors.New(msg)` value** of a message `msg` not among
`clientErrMsgs`. -/
theorem errCellOk_ne (err : GoInterface) (y : Loc) (msg : GoString) (hmsg : msg ∉ clientErrMsgs) :
    errCellOk (GF := GF) err ⊢ y.[_root_.Perennial.errors.errorString, go!"s"] ↦□ msg -∗
      ⌜err ≠ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #y⌝ := by
  unfold errCellOk
  iintro #H #Hy
  by_cases he : err = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #y
  · ihave ⟨%m, %hm, #Hm⟩ := H $$ %y %he
    icombine Hy Hm gives %h
    exact absurd (h ▸ hm) hmsg
  · ipureintro; exact he

end errstr

end go_etcd_io.etcd.cache.v3

end Perennial
