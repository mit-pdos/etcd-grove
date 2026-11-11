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
public import Spec.fmt.ErrorfWrap
public import Proof.google_golang_org.grpc.status.ErrDesc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.cache.v3

section desc

-- `errDesc` (an error's description, D29): `Proof/google_golang_org/grpc/status/ErrDesc.lean` (N1b).

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

/-- **An error that is not a refusal** (D29): `nil`, or one whose description is not a refusal's. -/
def noRefusal [GooseExts] (err : GoInterface) : Prop :=
  err = GoInterface.nil ∨ errDesc err ∉ refusalDescs

end desc

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
service's stream exactly ((the auth plan's E3zb) the Auth service's methods too; (the lease-src plan, 2026-11-02) the Lease
service's methods and stream; 2026-10-18: the Watch stream a client stream, `ClientStreams`, which
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
          [(go!"LeaseKeepAlive", @! go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseKeepAlive_Handler)]⌝) ∗
    pbDescOk (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.Cluster_ServiceDesc) go!"etcdserverpb.Cluster" go_etcd_io.etcd.api.v3.etcdserverpb.ClusterServer.ty ∗
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

/-- **The error value `e`'s `Error()` returns `m`, the same string on every call** (persistent;
fromerror-stable, 2026-11-06): what `status.FromError` needs to take the string as the error's
description (`errDesc`): it calls `Error()` on each call, so an `Error()` that reads mutable state
(`examples/axiomcx/flipdesc`, `notes/axiom-review/invoker-filled.md`) has no one description.
Stronger than `errorStringSpec` (`errorMsgIs_errorStringSpec`), which the printing paths keep. -/
def errorMsgIs (e : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errorMsgIs_persistent (e : GoInterfaceOk) (m : GoString) :
    Persistent (errorMsgIs (GF := GF) e m) := by
  unfold errorMsgIs; infer_instance

/-- **The methods grpc's `status` and Go's `errors.Is` call on the error `e` return**
(persistent; unit P3a), if `e`'s type has them (both are called through a type assertion):
`GRPCStatus() *Status` (`status.FromError`/`Code`/`Convert`) and `Is(error) bool`
(`errors.Is`, for any target). (fromerror-stable, 2026-11-06) `GRPCStatus()` returns one fixed
status `s` (grpc's `*Status` is immutable: `Proto()` clones, nothing exported writes it), so the
code and message `status.FromError` reads are the error's (`statusCode`, `errDesc`); and `Is`
returns `true` only for a target with the same description (`errors.IsStatusErr`'s
post: an `Is` that answered `true` regardless would refute it). -/
def grpcErrMethodsOk (e : GoInterfaceOk) : IProp GF :=
  iprop((⌜methodSet e.ty !! go!"GRPCStatus" =
      some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])⌝ →
    ∃ s : Loc, □ ∀ Φ : val → IProp GF, ▷ Φ #s -∗
      WP (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #())) {{ Φ }}) ∗
    (⌜methodSet e.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool])⌝ →
    □ ∀ (target : GoInterface) (Φ : val → IProp GF),
      ▷ (∀ b : Bool, ⌜b = true → errDesc (GoInterface.ok e) = errDesc target⌝ -∗ Φ #b) -∗
      WP (App (Val #(methods e.ty go!"Is" e.v)) (Val #target)) {{ Φ }}))

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
fmtarg`). -/
def statusErrOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ →
    (∃ m : GoString, errorMsgIs e m) ∗ ⌜errors.isLeafError e⌝ ∗ grpcErrMethodsOk e ∗
    ⌜methodSet e.ty !! go!"Format" = none⌝)

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
(unit P3a), and no `Format` method (premise-fixes-4: `fmt` prints it with its `Error`). -/
def rpctypesEtcdErrorTy : Prop :=
  (∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩) ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Format" = none

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
`TokenFieldNameGRPC`, `TokenFieldNameSwagger` (`"token"`, `"authorization"`; the strings since the
auth plan's E2c). -/
abbrev rpctypesInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e ∗
      -- (k8s etcd3 7c) its description
      ⌜errDesc (GoInterface.ok e) = futureRevDesc⌝ ∗
      -- (premise-fixes-4) no `Format` method: `fmt` prints it through `Error()`
      ⌜methodSet e.ty !! go!"Format" = none⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ↦□ GoInterface.ok e ∗
      errorStringSpec e ∗ ⌜errDesc (GoInterface.ok e) = compactedDesc⌝ ∗
      ⌜methodSet e.ty !! go!"Format" = none⌝) ∗
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
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: rpc not supported for learner"⌝ ∗
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
    (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWatchCanceled ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
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
      ⌜errDesc (GoInterface.ok e) = futureRevDesc⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCCompacted ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = compactedDesc⌝) ∗
    -- (k8s etcd3 7c, HS-1) the descriptions of the `ErrGRPC*` errors `v3rpc`'s checks and
    -- interceptors return (`error.go`)
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: key is not provided"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: key not found"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: value is provided"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: lease is provided"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: too many operations in txn request"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: duplicate key given in txn request"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidClientAPIVersion ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: invalid client api version"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: invalid sort option"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoSpace ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: mvcc: database space exceeded"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: no leader"⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotCapable ↦□ GoInterface.ok e ∗
      ⌜errDesc (GoInterface.ok e) = go!"etcdserver: not capable"⌝))

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
`fmt.Errorf`'s `%w` of it calls it, `fmt.argsOk`, which since premise-fixes-4 also asks that its
type, `*errors.errorString`, have no `Format` method). -/
abbrev cacheInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrNotReady ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrCacheTimeout ↦□ GoInterface.ok e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e -∗ errorStringSpec e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e -∗
      errorStringSpec e ∗ ⌜methodSet e.ty !! go!"Format" = none⌝))

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
has no `Format` method (premise-fixes-4, 2026-11-10: else `fmt` calls `Format`): what `fmt`'s
`%v`/`%w` of it needs (`fmt.argsOk`). -/
def errStrOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ →
    errorStringSpec e ∗ ⌜methodSet e.ty !! go!"Format" = none⌝)

instance errStrOk_persistent (err : GoInterface) : Persistent (errStrOk (GF := GF) err) := by
  unfold errStrOk; infer_instance

theorem errStrOk_nil : ⊢ errStrOk (GF := GF) GoInterface.nil := by
  unfold errStrOk
  iintro !> %e %h
  cases h

theorem errStrOk_ok (e : GoInterfaceOk) (hF : methodSet e.ty !! go!"Format" = none) :
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
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hF
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
  iapply errStrOk_ok _ hF
  unfold errorStringSpec
  iintro !> %Φ HΦ
  iapply HM
  inext
  iapply HΦ

/-- **`fmt.Errorf(format, args...)`'s error is an `errStrOk`**, for arguments of predeclared basic
types (premise-fixes-4): Perennial's model returns `errors.New(format)` (`wp_New_errStrOk`), and so
does Go for arguments none of which is an error (no `%w` wrapping): an `*errors.errorString`. -/
theorem wp_Errorf_errStrOk [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    (format : GoString) (args_sl : GoSlice) (args : List GoAny)
    (_hwf : _root_.Perennial.fmt.ArgsWf args) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); errStrOk (GoInterface.ok err) }} := by
  wp_start as _
  wp_apply wp_New_errStrOk as %err ⟨-, #Herr⟩
  iapply HΦ
  iexact Herr

theorem statusErrOk_nil : ⊢ statusErrOk (GF := GF) GoInterface.nil := by
  unfold statusErrOk
  iintro !> %e %h
  cases h

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
    ctxWrapErr (GF := GF) (GoInterface.ok ii) ⊢ EtcdGrove.fmt.stringMethodSpec ii go!"Error" := by
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
      icases Hm with ⟨-, %s, #Hs⟩
      unfold EtcdGrove.fmt.stringMethodSpec
      iintro !> %Φ HΦ
      iapply Hs
      inext
      iapply HΦ
    · iunfold EtcdGrove.fmt.wrapErrIs at Hw
      icases Hw with ⟨-, ⟨%s, #Hs⟩, -⟩
      unfold EtcdGrove.fmt.stringMethodSpec
      iintro !> %Φ HΦ
      iapply Hs
      inext
      iapply HΦ

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
  ihave ⟨⟨%m, #He⟩, -, -, %hF⟩ := H $$ %e %h
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
    context.isCtxErr (GF := GF) (GoInterface.ok ii) ⊢ EtcdGrove.fmt.stringMethodSpec ii go!"Error" := by
  iintro #He
  unfold EtcdGrove.fmt.stringMethodSpec
  iintro !> %Φ HΦ
  wp_apply (context.wp_isCtxErr_Error (GoInterface.ok ii) ii rfl) $$ He as %s -
  iapply HΦ

end ctxErrStr


end go_etcd_io.etcd.cache.v3

end Perennial
