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
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init
public import Spec.fmt.ErrorfWrap
public import Proof.google_golang_org.grpc.status.ErrDesc
public import Proof.go_uber_org.zap.PkgInit
public import Proof.google_golang_org.grpc.status.StatusRO

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.cache.v3

section desc

-- `errDesc` (an error's description, D29): `Proof/google_golang_org/grpc/status/ErrDesc.lean` (N1b).

/-- **The two read errors' descriptions** (k8s etcd3 stage 7c): `rpctypes.ErrGRPCFutureRev`'s and
`rpctypes.ErrGRPCCompacted`'s (`error.go:32-33`), which the server's `togRPCError` maps mvcc's
`ErrFutureRev` and `ErrCompacted` to, and the client's `rpctypes.ErrFutureRev`/`ErrCompacted` carry. -/
def futureRevDesc : GoString := go!"etcdserver: mvcc: required revision is a future revision"

def compactedDesc : GoString := go!"etcdserver: mvcc: required revision has been compacted"

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

instance protobuf_impl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  define_is_pkg_init iprop(True)

instance protoimpl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  define_is_pkg_init iprop(True)

instance mvccpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  define_is_pkg_init iprop(True)

-- `etcdserverpb` names `membershippb`'s and `authpb`'s messages (2026-10-12: the server's apply
-- package's requests): types and names only, `True` as the others
instance membershippb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.membershippb :=
  define_is_pkg_init iprop(True)

-- `protoreflect` (names only), before `authpb`, whose translation imports it (the auth plan's S1,
-- 2026-10-23: `authpb`'s messages and getters are translated with bodies, `authpb.toml`).
instance protoreflect_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  define_is_pkg_init iprop(True)

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

-- `google.golang.org/grpc/metadata` (types and names only), before `grpc`, which imports it
-- (unit W-W: grpc's `ClientStream`/`ServerStream` name `metadata.MD`; moved here from
-- `server/v3/auth/Base.lean`)
namespace google_golang_org.grpc.metadata

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.metadata :=
  define_is_pkg_init iprop(True)

end google_golang_org.grpc.metadata

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

/-- A generated `ServiceDesc` of service `sn` for the interface `T`, with distinct method and
stream names. -/
def pbDescOk (sd : Loc) (sn : GoString) (T : go.GoType) : IProp GF :=
  iprop(∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
    pbDescIs sd sn (interface.mkOk (go.GoType.PointerType T) #(null : Loc)) mds sds ∗
    ⌜(mds.map (·.MethodName') ++ sds.map (·.StreamName')).Nodup ∧ ∀ sd ∈ sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝)

/-- **`etcdserverpb`'s six `ServiceDesc`s** (`rpc_grpc.pb.go`: generated literals, never written;
item 8, 2026-10-17: until then an assumption of `v3rpc.Server`, `svcDescsOk`): their service names,
handler types and distinct method and stream names; the KV service's methods and the Watch
service's stream exactly ((the auth plan's E3zb) the Auth service's methods too; (the lease-src plan, 2026-11-02) the Lease
service's methods and stream; 2026-10-18: the Watch stream a client stream, `ClientStreams`, which
`grpc.ClientConn.NewStream`'s spec asks of its descriptor; and the Lease service's stream, the client
lease's keep-alive; per-type stage B, B1b: every stream descriptor of KV, Lease, Cluster and
Maintenance sets `ClientStreams` or `ServerStreams`, what `RegisterService` asks). -/
abbrev etcdserverpbDescs : IProp GF :=
  iprop((∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
      pbDescIs (globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.KV_ServiceDesc) go!"etcdserverpb.KV"
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.KVServer.ty) #(null : Loc)) mds sds ∗
      ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
          [(go!"Range", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Range_Handler), (go!"Put", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Put_Handler),
           (go!"DeleteRange", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_DeleteRange_Handler),
           (go!"Txn", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Txn_Handler), (go!"Compact", @! go_etcd_io.etcd.api.v3.etcdserverpb._KV_Compact_Handler)] ∧
        sds.map (·.StreamName') = [go!"RangeStream"] ∧ ∀ sd ∈ sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝) ∗
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

instance grpc_codes_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  define_is_pkg_init iprop(True)

/-- The error value `e`'s `Error()` returns some string (and does not panic). -/
def errorStringSpec (e : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

/-- **The error value `e`'s `Error()` returns `m`, the same string on every call** (persistent;
fromerror-stable, 2026-11-06): what `status.FromError` needs to take the string as the error's
description (`errDesc`): it calls `Error()` on each call, so an `Error()` that reads mutable state
(`examples/axiomcx/flipdesc`, `notes/axiom-review/invoker-filled.md`) has no one description.
Stronger than `errorStringSpec` (`errorMsgIs_errorStringSpec`), which the printing paths keep. -/
def errorMsgIs (e : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

/-- **The methods grpc's `status` and Go's `errors.Is` call on the error `e` return**
(persistent; unit P3a), if `e`'s type has them (both are called through a type assertion):
`GRPCStatus() *Status` (`status.FromError`/`Code`/`Convert`) and `Is(error) bool`
(`errors.Is`, for any target). (fromerror-stable, 2026-11-06) `GRPCStatus()` returns one fixed
status `s`, so the code and message `status.FromError` reads are the error's (`statusCode`,
`errDesc`); and `Is` returns `true` only for a target with the same description
(`errors.IsStatusErr`'s post: an `Is` that answered `true` regardless would refute it).
(k8s 7f-5a-P step 5, E1, approved by etcd-grove-81 2026-11-15) The status `s` is read-only with the
error's code (`grpcStatusRO s (statusCode e)`): grpc's `*Status` is not immutable in Go (a
whole-struct assignment `*s = *t` from any package copies its unexported fields); the fact is a
guarantee of the producer that built `s` (with `status.New`/`Error`) and never writes it after, as
grpc and etcd do (`examples/premisefix/grpcstatusro`; `notes/k8s-7f5a-draft.md` §11.2); a status
may be shared (package-level `status.Error` values). -/
def grpcErrMethodsOk (e : GoInterfaceOk) : IProp GF :=
  iprop((⌜methodSet e.ty !! go!"GRPCStatus" =
      some (go.Signature [] false
        [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])⌝ →
    ∃ s : Loc, (□ ∀ Φ : val → IProp GF, ▷ Φ #s -∗
      WP (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #())) {{ Φ }}) ∗
      EtcdGrove.grpcStatusRO s (EtcdGrove.statusCode (GoInterface.ok e))) ∗
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

-- The names-only target of the alias `grpc/status.Status` (imported by `grpc/status` since
-- `client/v3/leasing` names it).
instance grpc_internal_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.internal.status :=
  define_is_pkg_init iprop(True)

instance grpc_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.status :=
  define_is_pkg_init iprop(True)

/-- **The method set of `rpctypes.EtcdError`** is `{Code, Error}` (`error.go`), as far as
grpc's and Go's `errors` functions look (Go's typing, which the model lacks: method sets are
uninterpreted): no `As` or `Unwrap` method (a leaf error), no `GRPCStatus` and no `Is` method
(unit P3a), and no `Format` method (premise-fixes-4: `fmt` prints it with its `Error`). -/
def rpctypesEtcdErrorTy : Prop :=
  (∀ v : val, errors.isLeafError ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, v⟩) ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"GRPCStatus" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Is" = none ∧
  methodSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty !! go!"Format" = none

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
auth plan's E2c). -/
abbrev rpctypesInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e ∗
      -- (k8s etcd3 7c) its description
      ⌜errDesc (GoInterface.ok e) = futureRevDesc⌝ ∗
      -- (premise-fixes-4) no `Format` method: `fmt` prints it through `Error()`
      ⌜methodSet e.ty !! go!"Format" = none⌝ ∗
      -- (k8s etcd3 7e-2, D1) an `EtcdError` value (`TestRpctypesErrTypes`)
      ⌜∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
        GoInterface.ok e = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x⌝) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ↦□ GoInterface.ok e ∗
      errorStringSpec e ∗ ⌜errDesc (GoInterface.ok e) = compactedDesc⌝ ∗
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

-- The names-only packages of `clientv3.Client`'s field types.

-- `net` (names only; unit P3a: the type of grpc's `peer.Peer`'s fields; item 5: grpc's
-- `credentials` imports it, for `TransportCredentials`'s handshakes).
instance net_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.net :=
  define_is_pkg_init iprop(True)

instance grpc_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.credentials :=
  define_is_pkg_init iprop(True)

-- grpc's `peer` (names only; unit P3a: the retry interceptor's `peer.Peer`).
instance grpc_peer_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.peer :=
  define_is_pkg_init iprop(True)

instance clientv3_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials :=
  define_is_pkg_init iprop(True)

instance clientv3_resolver_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver :=
  define_is_pkg_init iprop(True)

-- Names only (item 5, client construction, branch `construct`): what `clientv3.New`'s dial
-- names (the type of `Config.TLS`, grpc's keepalive parameters and insecure credentials, an
-- endpoint's credentials requirement, the default logger); `logutil`'s instance moved here from
-- `etcdserver/BaseApply.lean` (stage R8b), now that `clientv3` imports it.
instance tls_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.crypto.tls :=
  define_is_pkg_init iprop(True)
instance grpc_keepalive_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.keepalive :=
  define_is_pkg_init iprop(True)
instance grpc_insecure_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure :=
  define_is_pkg_init iprop(True)
instance clientv3_endpoint_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.endpoint :=
  define_is_pkg_init iprop(True)
instance logutil_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.logutil :=
  define_is_pkg_init iprop(True)

-- protobuf's `proto` (`clientv3.cloneCompare` calls `proto.Clone`; names only; `protoreflect`,
-- which it imports, is above `authpb`).
instance proto_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  define_is_pkg_init iprop(True)

/-- **A backoff function** (`clientv3.backoffFunc`, `func(attempt uint) time.Duration`) that
returns (persistent; unit P3a: the retry interceptor's `waitRetryBackoff` calls it). -/
def backoffOk (bf : GoFunc) : IProp GF :=
  iprop(□ ∀ (a : w64) (Φ : val → IProp GF), ▷ (∀ d : w64, Φ #d) -∗
    WP (App (Val #bf) (Val #a)) {{ Φ }})

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

-- `k8s.io/utils/third_party/forked/golang/btree`: `Proof/k8s_io/.../btree/Init.lean`.

end init

section errstr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

end errstr

section ctxErrStr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

end ctxErrStr

end go_etcd_io.etcd.cache.v3

end Perennial
