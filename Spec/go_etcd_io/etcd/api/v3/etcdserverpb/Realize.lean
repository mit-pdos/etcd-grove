/-
# etcdserverpb (batch 3h): the realization of the client's message and stub slots

The laws over the client's vocabulary (1b's `ApiWatch.lean`, 1c's `ApiClient.lean`/`ApiLease.lean`):
the watch messages' and the non-KV messages' relation to protobuf's content (`watchReqOwn_msgAt`,
`reqOwn_msgAt`, `replyOwn_msgAt`), the fields of the lease replies the client's lessor copies
(`replyOwn_lease*`), `UserAddOptions` (`userAddOptsAt_unfold`), `StatusResponse`
(`statusRespOwn_msgAt`). The stubs' constructors (`NewKVClient.spec`, ...) are in their own files
and import this module.

**Laws offered by 2b** (`v3rpc/ApiWatch.lean`: `watchReqOwn_unfold`, `wireWatchRespOwn_unfold`,
`wireWatchRespOwn_persist`) are accepted as stated: they are this batch's obligations (the field
realization of `watchReqOwn`, `wireWatchRespOwn`), not restated here. A create's raw key `""` models
the key `"\x00"` (`createRange`), as 1b asked (round 1, item 4).

**Integration I3**: 1b's watch messages (`EventM`, `WireWatchReq`, `WireWatchRespM`, `eventOwn`,
`watchReqOwn`, `wireWatchRespOwn`) now live in W0's `api/v3/Wire.lean`; this module realizes them
there as before (`*_msgAt` below). W0's new laws `eventOwn_persist`, `eventOwn_discard_persistent`
and `msgOwn_discard_persistent` (integration I1) are this batch's obligations too: each message
predicate is `∃ c, Proto.msgAt T p dq c ∗ ⌜holds c m⌝` (the relation laws), and `Proto.msgAt`'s
`persist` and its persistence at `DFrac.discard` (`Proto/Api.lean`) give them (`protoRest` likewise:
the bookkeeping fields under `msgAt`). The watch contract (`ClientV3.watchSpec`, 2a's, now in
the client's `ApiWatch.lean`) is stated over `watchReqHolds`/`watchRespHolds`, which integration X
moved to `Api.lean` with `eventHolds`, `watch_holds_fun`, `watch_holds_depth` (the client's
`ApiWatch` cannot import this module, which imports it).

**Realizing W0's call-error laws** (client-core's request 4): `errorsIs_callErr_eof` holds because
grpc returns `io.EOF` itself only at a stream's clean end and never wraps it (`cliRecv_recv`,
`cliSend_send`: `globalAddr io.EOF ↦□ err`), and its other errors are statuses (`statusErr_ty`:
`*status.Error`, whose `Is` matches statuses only), context errors or `EtcdError`s;
`callErr_errorsNew`'s `io.EOF` disjunct is the same stream end; W0's `protoRest_persist` is
`Proto.msgAt_persist` read through each message's relation law (`protoRest` is the bookkeeping
under `msgAt`). `wireStreamAt_recv`'s non-EOF error is `cliRecv_recv`'s status or own error.

**Intended realization**: as `Api.lean`'s (each predicate the field-level predicate of its unfold
law; `msgAt` of each type the same; each relation "the content's fields are the model's").

**Not realizable today** (the translation, `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`, names
only): the fields of `Member`, `MemberAddResponse`, `MemberListResponse`, `AlarmResponse`,
`StatusResponse` (1c's `Client.Sync`, `MemberList`, `Status` snippets). Their contents are related to
the models (`replyOwn_msgAt`, `bodyHolds`), so gRPC transports them; reading a field in Go needs the
struct translated (an open question of the batch report).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import Spec.go_etcd_io.etcd.client.v3.ApiWatch
public import Spec.go_etcd_io.etcd.client.v3.ApiLease
public import GeneratedProof.go_etcd_io.etcd.api.v3.authpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.api.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def watchReqOwn_msgAt.spec : Prop := ∀ p dq r,
  watchReqOwn (GF := GF) p dq r ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.WatchRequest.ty p dq c ∗ ⌜watchReqHolds c r⌝
def wireWatchRespOwn_msgAt.spec : Prop := ∀ p dq m,
  wireWatchRespOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.WatchResponse.ty p dq c ∗ ⌜watchRespHolds c m⌝
def eventOwn_msgAt.spec : Prop := ∀ p dq e,
  eventOwn (GF := GF) p dq e ⊣⊢ ∃ c, Proto.msgAt mvccpb.Event.ty p dq c ∗ ⌜eventHolds c e⌝

/-- **A non-KV request** (1c's `reqOwn`): `msgAt` of its type holding its model. -/
def reqOwn_msgAt.spec : Prop := ∀ p dq rq,
  reqOwn (GF := GF) p dq rq ⊣⊢ ∃ c, Proto.msgAt (reqType rq) p dq c ∗ ⌜reqHolds c rq⌝

/-- **A reply** (1c's `replyOwn`, owned): `msgAt` of its type holding the body (`replyModels`). -/
def replyOwn_msgAt.spec : Prop := ∀ p b,
  replyOwn (GF := GF) p b ⊣⊢
    ∃ c, Proto.msgAt (bodyType b) p (DFrac.own 1) c ∗ ⌜replyModels go!"" b c⌝

/-- **The lease replies' fields** (the client's `lessor.Grant`, `TimeToLive`, `Leases` copy them):
the header (some, possibly `nil`), the model's ids and TTLs, lent until given back. -/
def replyOwn_lease.spec : Prop :=
  (∀ (p : Loc) (id ttl : Int), replyOwn (GF := GF) p (.leaseGrant id ttl) ⊢
    ∃ (h : Loc) (ho : Option HeaderM) (e : GoString),
      p.[etcdserverpb.LeaseGrantResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[etcdserverpb.LeaseGrantResponse, go!"ID"] ↦ W64 id ∗
      p.[etcdserverpb.LeaseGrantResponse, go!"TTL"] ↦ W64 ttl ∗
      p.[etcdserverpb.LeaseGrantResponse, go!"Error"] ↦ e ∗
      (p.[etcdserverpb.LeaseGrantResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
       p.[etcdserverpb.LeaseGrantResponse, go!"ID"] ↦ W64 id ∗
       p.[etcdserverpb.LeaseGrantResponse, go!"TTL"] ↦ W64 ttl ∗
       p.[etcdserverpb.LeaseGrantResponse, go!"Error"] ↦ e -∗ replyOwn p (.leaseGrant id ttl))) ∧
  (∀ (p : Loc) (id ttl gttl : Int) (ks : List Key),
    replyOwn (GF := GF) p (.leaseTimeToLive id ttl gttl ks) ⊢
    ∃ (h : Loc) (ho : Option HeaderM) (ksl : GoSlice) (kps : List GoSlice),
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Header"] ↦ h ∗
        optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"ID"] ↦ W64 id ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"TTL"] ↦ W64 ttl ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"GrantedTTL"] ↦ W64 gttl ∗
      p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Keys"] ↦ ksl ∗ ksl ↦* kps ∗
      ([∗list] s; k ∈ kps; ks, s ↦*□ k) ∗
      (p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Header"] ↦ h ∗
        optOwn respHeaderOwn h (DFrac.own 1) ho ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"ID"] ↦ W64 id ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"TTL"] ↦ W64 ttl ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"GrantedTTL"] ↦ W64 gttl ∗
       p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Keys"] ↦ ksl ∗ ksl ↦* kps -∗
       replyOwn p (.leaseTimeToLive id ttl gttl ks))) ∧
  (∀ (p : Loc) (ids : List Int), replyOwn (GF := GF) p (.leaseLeases ids) ⊢
    ∃ (h : Loc) (ho : Option HeaderM) (lsl : GoSlice) (lps : List Loc),
      p.[etcdserverpb.LeaseLeasesResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[etcdserverpb.LeaseLeasesResponse, go!"Leases"] ↦ lsl ∗ lsl ↦* lps ∗
      ([∗list] l; id ∈ lps; ids, l.[etcdserverpb.LeaseStatus, go!"ID"] ↦ W64 id) ∗
      (p.[etcdserverpb.LeaseLeasesResponse, go!"Header"] ↦ h ∗
        optOwn respHeaderOwn h (DFrac.own 1) ho ∗
       p.[etcdserverpb.LeaseLeasesResponse, go!"Leases"] ↦ lsl ∗ lsl ↦* lps ∗
       ([∗list] l; id ∈ lps; ids, l.[etcdserverpb.LeaseStatus, go!"ID"] ↦ W64 id) -∗
       replyOwn p (.leaseLeases ids)))

/-- **`UserAddWithOptions`' options** (1c's `userAddOptsAt`): `nil` (a password required), or a
read-only `authpb.UserAddOptions` whose `NoPassword` is `noPw`. -/
def userAddOptsAt_unfold.spec : Prop := ∀ (p : Loc) (noPw : Bool),
  userAddOptsAt (GF := GF) p noPw ⊣⊢
    ⌜p = null ∧ noPw = false⌝ ∨
    (protoRest authpb.UserAddOptions p DFrac.discard ∗
      p.[authpb.UserAddOptions, go!"NoPassword"] ↦□ noPw)

/-- **A `StatusResponse`** (1c's `statusRespOwn`, no model: the client reads nothing of it but
passes it on): an owned message of that type. -/
def statusRespOwn_msgAt.spec : Prop := ∀ p,
  statusRespOwn (GF := GF) p ⊣⊢ ∃ c, Proto.msgAt etcdserverpb.StatusResponse.ty p (DFrac.own 1) c

/-! ### The client's gRPC slots (verify-round, A6-provability F7)

1c's `AttemptTriple` (`ApiClient.lean`) is stated over three slots of 2a/3h's (`unaryArgs`,
`grpcCallOptsOk`, `grpcConnAt`) which had no law relating them to grpc's vocabulary, so no proof
could derive `AttemptTriple` from grpc's `attemptOk_call` nor the stubs' constructors use them.
Their meanings, as grpc's specs need them: -/

/-- The service of a request's method. -/
def svcOf : Req → GoString
  | .range _ | .put _ | .deleteRange _ | .txn _ | .compact .. => go!"KV"
  | .leaseGrant .. | .leaseRevoke _ | .leaseKeepAlive _ | .leaseTimeToLive .. | .leaseLeases =>
      go!"Lease"
  | .memberAdd .. | .memberRemove _ | .memberUpdate .. | .memberPromote _ | .memberList _ =>
      go!"Cluster"
  | .alarmList | .alarmDisarm _ | .alarmActivate _ => go!"Maintenance"
  | _ => go!"Auth"

/-- **The full gRPC method name of a request** (`/etcdserverpb.<Service>/<Method>`, the stubs'). -/
def methodOf (rq : Req) : GoString := go!"/etcdserverpb." ++ svcOf rq ++ go!"/" ++ reqRpc rq

/-- **The Go type of a request's reply message** (the method's, `V3rpc.etcdContract`'s). -/
def replyType : Req → go.GoType
  | .range _ => etcdserverpb.RangeResponse.ty
  | .put _ => etcdserverpb.PutResponse.ty
  | .deleteRange _ => etcdserverpb.DeleteRangeResponse.ty
  | .txn _ => etcdserverpb.TxnResponse.ty
  | .compact _ _ => etcdserverpb.CompactionResponse.ty
  | .leaseGrant _ _ => etcdserverpb.LeaseGrantResponse.ty
  | .leaseRevoke _ => etcdserverpb.LeaseRevokeResponse.ty
  | .leaseKeepAlive _ => etcdserverpb.LeaseKeepAliveResponse.ty
  | .leaseTimeToLive _ _ => etcdserverpb.LeaseTimeToLiveResponse.ty
  | .leaseLeases => etcdserverpb.LeaseLeasesResponse.ty
  | .authEnable => etcdserverpb.AuthEnableResponse.ty
  | .authDisable => etcdserverpb.AuthDisableResponse.ty
  | .authStatus => etcdserverpb.AuthStatusResponse.ty
  | .authenticate _ _ => etcdserverpb.AuthenticateResponse.ty
  | .userAdd _ _ _ => etcdserverpb.AuthUserAddResponse.ty
  | .userGet _ => etcdserverpb.AuthUserGetResponse.ty
  | .userList => etcdserverpb.AuthUserListResponse.ty
  | .userDelete _ => etcdserverpb.AuthUserDeleteResponse.ty
  | .userChangePassword _ _ => etcdserverpb.AuthUserChangePasswordResponse.ty
  | .userGrantRole _ _ => etcdserverpb.AuthUserGrantRoleResponse.ty
  | .userRevokeRole _ _ => etcdserverpb.AuthUserRevokeRoleResponse.ty
  | .roleAdd _ => etcdserverpb.AuthRoleAddResponse.ty
  | .roleGet _ => etcdserverpb.AuthRoleGetResponse.ty
  | .roleList => etcdserverpb.AuthRoleListResponse.ty
  | .roleDelete _ => etcdserverpb.AuthRoleDeleteResponse.ty
  | .roleGrantPermission _ _ => etcdserverpb.AuthRoleGrantPermissionResponse.ty
  | .roleRevokePermission _ _ _ => etcdserverpb.AuthRoleRevokePermissionResponse.ty
  | .memberAdd _ _ => etcdserverpb.MemberAddResponse.ty
  | .memberRemove _ => etcdserverpb.MemberRemoveResponse.ty
  | .memberUpdate _ _ => etcdserverpb.MemberUpdateResponse.ty
  | .memberPromote _ => etcdserverpb.MemberPromoteResponse.ty
  | .memberList _ => etcdserverpb.MemberListResponse.ty
  | .alarmList => etcdserverpb.AlarmResponse.ty
  | .alarmDisarm _ => etcdserverpb.AlarmResponse.ty
  | .alarmActivate _ => etcdserverpb.AlarmResponse.ty

/-- **The content a reply answer arrives as**: a success body's (`replyModels`), or
`LeaseTimeToLive`'s not-found answer as the `-1` reply (`lease.go:66-73`; 2a's `ansOutcome`). -/
def ansContent (m : GoString) (rq : Req) (res : Resp) (c : Proto.Content) : Prop :=
  match rq, res with
  | .leaseTimeToLive id _, .err .leaseNotFound => replyModels m (.leaseTimeToLive id (-1) 0 []) c
  | _, .ok b => replyModels m b c
  | _, _ => False

/-- **A unary call's arguments, realized** (1c's `unaryArgs` slot): the method is the request's,
the request message (a share, given back) holds a content modelling `rq` whose range ends are
`nil` or non-empty (the client's `OpM.emptyEnd` scope: so the member decodes the same model,
`holds_norm`) and, for a compaction, a revision not `0` (what `V3rpc.etcdUnary` takes); the reply
holder is a fresh owned message of the method's reply type; and `R` of each reply answer follows
from the request's share and the holder holding the answer's content. -/
def unaryArgs_msgAt.spec : Prop := ∀ (method : GoString) (req reply : GoInterface) (rq : Req)
    (R : Resp → IProp GF),
  unaryArgs (GF := GF) method req reply rq R ⊣⊢
    ∃ (pq pr : Loc) (dq : DFrac) (c r0 : Proto.Content),
      ⌜method = methodOf rq ∧ req = Proto.msgVal (reqType rq) pq ∧
        reply = Proto.msgVal (replyType rq) pr ∧ reqModels method c rq ∧ endsOk c ∧
        (∀ r ph, rq = .compact r ph → r ≠ 0)⌝ ∗
      Proto.msgAt (reqType rq) pq dq c ∗ Proto.msgAt (replyType rq) pr (DFrac.own 1) r0 ∗
      (∀ (res : Resp) (c' : Proto.Content), ⌜replyAns rq res ∧ ansContent method rq res c'⌝ -∗
        Proto.msgAt (reqType rq) pq dq c -∗ Proto.msgAt (replyType rq) pr (DFrac.own 1) c' -∗ R res)

/-- **The call options grpc's invoker accepts, realized** (1c's `grpcCallOptsOk` slot): a read-only
slice of options each `Grpc.callOptOk`. -/
def grpcCallOptsOk_unfold.spec : Prop := ∀ (sl : GoSlice),
  grpcCallOptsOk (GF := GF) sl ⊣⊢
    ∃ vs : List GoInterface, sl ↦*□ vs ∗ [∗list] v ∈ vs, Grpc.callOptOk v

/-- **A gRPC client connection, realized** (1c's `grpcConnAt` slot): one grpc's `NewClient` made
(`Grpc.connAt`, any resolver, interceptors and credentials). -/
def grpcConnAt_of.spec : Prop := ∀ (cc : Loc) (A : GoString → IProp GF) (ui si : Option val)
    (R : Grpc.MD → IProp GF),
  Grpc.connAt cc A ui si R ⊢ grpcConnAt cc


/-- **A connection reaching one member, realized** (1c's `grpcConnVia` slot; client-core's request
1): one grpc made whose resolver reports `ep` alone. With it, every attempt goes to `ep`
(`attemptOk_call`'s `A`), so the answering member's `leaseFact` (`V3rpc.etcdUnary` at `ep`) gives
1c's `viaFact`. -/
def grpcConnVia_unfold.spec : Prop := ∀ (cc : Loc) (ep : GoString),
  grpcConnVia (GF := GF) cc ep ⊣⊢
    ∃ (A : GoString → IProp GF) (ui si : Option val) (R : Grpc.MD → IProp GF),
      Grpc.connAt cc A ui si R ∗ □ (∀ ep', A ep' -∗ ⌜ep' = ep⌝)

end laws

end EtcdServerPb
end EtcdGrove
end Perennial
