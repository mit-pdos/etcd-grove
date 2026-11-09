/-
# etcd's gRPC services (batch 2a): `server/v3/etcdserver/api/v3rpc`, all but `watch.go` (2b)

The handlers a member registers with grpc (`v3rpc.Server`): KV, Lease, Cluster, Auth,
Maintenance (and Watch, 2b's), their interceptors, the quota wrappers, the error mapping. This
file is the vocabulary their specs share, and the **realization of W0's `servesAt`**: a member
serves etcd at `ep` when `ep` is bound (grpc's `addrAt`) to **etcd's contracts** (`etcdContract γ`),
one per method, each the server's half of the client's shape (W0's `KV.*Triple`, 1c's `CallTriple`).

## The contract of a unary method (`etcdUnary γ m`)

A caller of method `m` hands over, with a request whose content models `rq` (`reqModels`, 3h's
decoding) and metadata the member authenticates as `who` (`mdPrin`, 2c/3d's slot), its update
`callAU γ who rq rep Q` (1c's: persistent if `rep`; a read's must be persistent, the member firing
it at the state it reads and possibly at earlier ones), and three ways to finish, one of which the
member takes (`∧`):

1. **answered**: the member fired the update with the answer `res` (`Step who rq σ σ' res`, a
   refusal included: `Step.refuse`), and sends the outcome `ansOutcome m res o` (the reply's content
   for `.ok b`, `replyModels`; a status with `e`'s description for `.err e`): the caller gets `Φ o`
   from `Q σ σ' res`;
2. **refused unfired**: a token refusal (`errRetryAuth`) or a learner's refusal, the update given
   back with the status (the client's interceptor resends or fires the refusal itself, 1c);
3. **unsettled**: a status that settles nothing (`indefMsg`: no description of a definite, mapped
   etcd error): `Φ` without the update (which the member may still fire: a write's entry may commit
   after the timeout).

This is W0's firing discipline (`req/..._api_v3rpc.md` item 3) in grpc's shape (`Grpc.UnarySpec`,
the urpc style W0 asked for): **at most once** for an exclusive update holds because the member
fires it only from the entry's apply (2c/2d), grpc runs a call's handler at most once per attempt
(`Grpc.attemptOk_call`), and the client resends only after (2), which fired nothing.

The maintenance RPCs that answer from the member and change no modelled state (`Status`, `Hash`,
`HashKV`, `Defragment`, `MoveLeader`, `Downgrade`) have `etcdLocal`: no update, any outcome.
Streams: `rangeStreamSpec γ` (this file), `kaSpec γ` (keep-alives: nothing modelled), `snapSpec`
(the backend's bytes: nothing modelled), `watchSpec γ` (**slot, 2b**).

## Vocabulary

* Pure: `etcdMethods`/`etcdStreams` (the method table: full names and message types),
  `ansOutcome`, `indefMsg`, `maxTxnOpsMax` (`4999`: `issues/etcd-txn-nested-depth-apply-panic.md`).
* **Slots of other batches**, named here so the contracts can be written (each to be identified
  with its owner's predicate at integration):
  `reqModels m c rq`, `replyModels m b c`, `chunkModels c m` (3h: what a request's or a reply's
  content models; functional in the content), `mdPrin γ md who` (2c/3d: a request with incoming
  metadata `md` is authenticated as `who`, or refused with a refusal; introduced from a token
  (`tokenOf`) or no token), `srvOk s γ` (2c/2e: the started `*EtcdServer` `s` of a member of `γ`, its
  request-path methods meeting the shapes of `req/go_etcd_io_etcd_server_v3_etcdserver.md`,
  "from 2a"), `watchSpec γ` (2b).
* Ghost state of a streamed range: `rsReq g who r Q` (persistent, agreeing: the stream `g` carries
  the read `r` of `who` with `Q`; allocated by the client from grpc's `streamKey g`),
  `rsChunk g j m` (persistent: the `j`-th chunk sent is `m`). Intended realization: a ghost map
  from stream names, in the KV service's invariant.
* Handles (persistent): `kvServerAt p s γ` (`*kvServer`), `quotaKVAt q p s γ` (`*quotaKVServer`
  over it), `leaseServerAt`, `quotaLeaseAt`, `authServerAt`, `clusterServerAt`, `maintAt`
  (`*maintenanceServer`), `authMaintAt` (`*authMaintenanceServer`), `headerAt h s γ` (a `header`
  value), `authAdminAt aa s γ`, `quotaAlarmerAt qa s γ`, `notifierAt n`.

## Laws

`servesAt_addr` (W0's `servesAt` is `ep` bound to etcd's contracts), `rsReq_alloc`, `rsReq_agree`,
`handles_persistent`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto

/-- The `--max-txn-ops` etcd's specs admit (`issues/etcd-txn-nested-depth-apply-panic.md`: above it a
nested transaction the gRPC check accepts can exceed protobuf's decoding depth at apply). -/
def maxTxnOpsMax : Nat := 4999

/-- **A status message that settles nothing**: no description of a definite etcd error that the
client maps (`Rpctypes.mapped`). -/
def indefMsg (msg : GoString) : Prop :=
  ∀ e : EtcdErr, Rpctypes.mapped e = true → msg = Rpctypes.desc e → e.indefinite = true

/-- **Slot (3h)**: the content `c` of a request of method `m` models `rq`. -/
opaque reqModels (m : GoString) (c : Content) (rq : Req) : Prop

/-- **Slot (3h)**: the content `c` of a reply of method `m` carries the success body `b` (the
reply's header revision the body's; the other header fields any). -/
opaque replyModels (m : GoString) (b : RespBody) (c : Content) : Prop

/-- **Slot (3h)**: the content `c` of a `RangeStreamResponse` carries the chunk `m`. -/
opaque chunkModels (c : Content) (m : RangeRespM) : Prop

/-- **The outcome a member sends for the answer `res`** of a request of method `m`. -/
def ansOutcome (m : GoString) (res : Resp) (o : Outcome) : Prop :=
  match res with
  | .ok b => ∃ c, o = .ok c ∧ replyModels m b c
  | .err e => ∃ code, o = .status code (Rpctypes.desc e)

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **Slot (2c/3d)**: a request with incoming metadata `md` is authenticated as `who` (or refused
with a refusal: an invalid token). -/
opaque mdPrin (γ : Cluster) (md : MD) (who : Principal) : IProp GF := iprop(True)

/-- **Slot (2c/2e)**: the started server `s` of a member of `γ`. -/
opaque srvOk (s : Loc) (γ : Cluster) : IProp GF := iprop(True)

/-- **The contract of etcd's unary method `m`** (see the header). -/
def etcdUnary (γ : Cluster) (m : GoString) : UnarySpec (GF := GF) :=
  fun md c Φ => iprop(∃ (who : Principal) (rq : Req) (rep : Bool) (Q : State → State → Resp → IProp GF),
    ⌜reqModels m c rq ∧ (rq.isRead = true → rep = true)⌝ ∗ mdPrin γ md who ∗ callAU γ who rq rep Q ∗
    ((∀ (σ σ' : State) (res : Resp) (o : Outcome), ⌜ansOutcome m res o⌝ -∗ Q σ σ' res -∗ Φ o) ∧
     (callAU γ who rq rep Q -∗ ∀ (e : EtcdErr) (code : w32),
        ⌜errRetryAuth e = true ∨ e = .notSupportedForLearner⌝ -∗ Φ (.status code (Rpctypes.desc e))) ∧
     (∀ (code : w32) (msg : GoString), ⌜indefMsg msg⌝ -∗ Φ (.status code msg))))

/-- **The contract of a member-local maintenance RPC**: no update; any outcome. -/
def etcdLocal : UnarySpec (GF := GF) := fun _ _ Φ => iprop(∀ o : Outcome, Φ o)

/-- **A streamed range's request is `r` of `who`, its update's result `Q`** (persistent). -/
opaque rsReq (g : StreamName) (who : Principal) (r : RangeReq) (Q : State → State → Resp → IProp GF) :
  IProp GF := iprop(True)

/-- **The `j`-th chunk of the streamed range `g` is `m`** (persistent). -/
opaque rsChunk (g : StreamName) (j : Nat) (m : RangeRespM) : IProp GF := iprop(True)

/-- **`RangeStream`'s contract**: the one request with the caller's persistent update (W0's
`RemoteKV.RangeStreamTriple`); each chunk recorded; the end: the update's `Q` with the answer the
chunks make (`streamMatches`), or a linearized error, or (after a chunk) `ErrCompacted` with no `Q`
(the pinned revision compacted between chunks), or a status that settles nothing. -/
def rangeStreamSpec (γ : Cluster) : StreamSpec (GF := GF) where
  up := fun g md i c => iprop(⌜i = 0⌝ ∗ ∃ (who : Principal) (r : RangeReq) (Q : State → State → Resp → IProp GF),
    ⌜reqModels go!"/etcdserverpb.KV/RangeStream" c (.range r)⌝ ∗ mdPrin γ md who ∗ rsReq g who r Q ∗
    □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜Step who (.range r) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }>)
  dn := fun g _ j c => iprop(∃ m, ⌜chunkModels c m⌝ ∗ rsChunk g j m)
  fin := fun g _ n e => iprop(∃ (who : Principal) (r : RangeReq) (Q : State → State → Resp → IProp GF)
      (ms : List RangeRespM), rsReq g who r Q ∗ ⌜ms.length = n⌝ ∗ ([∗list] j ↦ m ∈ ms, rsChunk g j m) ∗
    match e with
    | none => ∃ (σ σ' : State) (rev : Nat) (a : RangeAns), Q σ σ' (.ok (.range rev a)) ∗
        ⌜streamMatches r ms rev a⌝
    | some (_, msg) => (∃ (σ σ' : State) (e : EtcdErr), Q σ σ' (.err e) ∗ ⌜msg = Rpctypes.desc e⌝) ∨
        ⌜n ≠ 0 ∧ msg = Rpctypes.desc .compacted⌝ ∨ ⌜indefMsg msg⌝)

/-- **`LeaseKeepAlive`'s contract**: keep-alive requests, responses about some lease with some TTL
(W0's model: a keep-alive says nothing), nothing at the end (1c's `kaSendAt`/`kaRecvAt`). -/
def kaSpec (γ : Cluster) : StreamSpec (GF := GF) where
  up := fun _ md _ c => iprop(∃ (who : Principal) (id : Int),
    ⌜reqModels go!"/etcdserverpb.Lease/LeaseKeepAlive" c (.leaseKeepAlive id)⌝ ∗ mdPrin γ md who)
  dn := fun _ _ _ _ => iprop(True)
  fin := fun _ _ _ _ => iprop(True)

/-- **`Snapshot`'s contract**: the backend's bytes, nothing modelled. -/
def snapSpec : StreamSpec (GF := GF) where
  up := fun _ _ _ _ => iprop(True)
  dn := fun _ _ _ _ => iprop(True)
  fin := fun _ _ _ _ => iprop(True)

/-- **Slot (2b)**: the `Watch` stream's contract (2b's handler, 1b's client:
`Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`'s wire protocol). -/
opaque watchSpec (γ : Cluster) : StreamSpec (GF := GF) :=
  { up := fun _ _ _ _ => iprop(True), dn := fun _ _ _ _ => iprop(True), fin := fun _ _ _ _ => iprop(True) }

/-- **etcd's contracts** at a member's client address: every unary method of the KV, Lease,
Cluster, Maintenance and Auth services, and the four streams. -/
def etcdContract (γ : Cluster) : AddrContract (GF := GF) where
  unary := fun m =>
    if False then none
  else if m = go!"/etcdserverpb.KV/Range" then some (go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.KV/Put" then some (go_etcd_io.etcd.api.v3.etcdserverpb.PutRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.PutResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.KV/DeleteRange" then some (go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.DeleteRangeResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.KV/Txn" then some (go_etcd_io.etcd.api.v3.etcdserverpb.TxnRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.KV/Compact" then some (go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Lease/LeaseGrant" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseGrantResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Lease/LeaseRevoke" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Lease/LeaseTimeToLive" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseTimeToLiveResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Lease/LeaseLeases" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Cluster/MemberAdd" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberAddRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberAddResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Cluster/MemberRemove" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberRemoveRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberRemoveResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Cluster/MemberUpdate" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberUpdateRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberUpdateResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Cluster/MemberList" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberListRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberListResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Cluster/MemberPromote" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MemberPromoteRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MemberPromoteResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Maintenance/Alarm" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AlarmRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AlarmResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Maintenance/Status" then some (go_etcd_io.etcd.api.v3.etcdserverpb.StatusRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.StatusResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/Defragment" then some (go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.DefragmentResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/Hash" then some (go_etcd_io.etcd.api.v3.etcdserverpb.HashRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.HashResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/HashKV" then some (go_etcd_io.etcd.api.v3.etcdserverpb.HashKVRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.HashKVResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/MoveLeader" then some (go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.MoveLeaderResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Maintenance/Downgrade" then some (go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.DowngradeResponse.ty, etcdLocal)
  else if m = go!"/etcdserverpb.Auth/AuthEnable" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthEnableRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthEnableResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/AuthDisable" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthDisableRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthDisableResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/AuthStatus" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthStatusRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthStatusResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/Authenticate" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/UserAdd" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserAddRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserAddResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/UserGet" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGetRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGetResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/UserList" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserListRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserListResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/UserDelete" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserDeleteRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserDeleteResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/UserChangePassword" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserChangePasswordRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserChangePasswordResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/UserGrantRole" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGrantRoleRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserGrantRoleResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/UserRevokeRole" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserRevokeRoleRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthUserRevokeRoleResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/RoleAdd" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleAddRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleAddResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/RoleGet" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGetRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGetResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/RoleList" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleListRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleListResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/RoleDelete" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleDeleteRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleDeleteResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/RoleGrantPermission" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGrantPermissionRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleGrantPermissionResponse.ty, etcdUnary γ m)
  else if m = go!"/etcdserverpb.Auth/RoleRevokePermission" then some (go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleRevokePermissionRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.AuthRoleRevokePermissionResponse.ty, etcdUnary γ m)
    else none
  stream := fun m =>
    if False then none
  else if m = go!"/etcdserverpb.KV/RangeStream" then some (go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.RangeStreamResponse.ty, rangeStreamSpec γ)
  else if m = go!"/etcdserverpb.Watch/Watch" then some (go_etcd_io.etcd.api.v3.etcdserverpb.WatchRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.WatchResponse.ty, watchSpec γ)
  else if m = go!"/etcdserverpb.Lease/LeaseKeepAlive" then some (go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse.ty, kaSpec γ)
  else if m = go!"/etcdserverpb.Maintenance/Snapshot" then some (go_etcd_io.etcd.api.v3.etcdserverpb.SnapshotRequest.ty, go_etcd_io.etcd.api.v3.etcdserverpb.SnapshotResponse.ty, snapSpec)
    else none

/-- **W0's `servesAt`, realized**: `ep` is bound to etcd's contracts. -/
def servesAt_addr.spec : Prop := ∀ (γ : Cluster) (ep : GoString),
  servesAt (GF := GF) γ ep ⊣⊢ addrAt ep (etcdContract γ)

/-- A streamed range's parameters, fixed by the client with the stream's key. -/
def rsReq_alloc.spec : Prop := ∀ g who r (Q : State → State → Resp → IProp GF),
  streamKey (GF := GF) g ⊢ |==> rsReq g who r Q

def rsReq_agree.spec : Prop := ∀ g who who' r r' (Q Q' : State → State → Resp → IProp GF),
  rsReq (GF := GF) g who r Q ∗ rsReq g who' r' Q' ⊢ ⌜who = who' ∧ r = r'⌝ ∗ ▷ (∀ σ σ' res, Q σ σ' res ≡ Q' σ σ' res)

/-! ### Handles of the service objects -/

/-- A `*kvServer` over the server `s` (`NewKVServer`'s: its header of `s`, `kv` the server, `aa`
over it, `maxTxnOps` at most `maxTxnOpsMax`). -/
opaque kvServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- A `*quotaKVServer` `q` wrapping the `KVServer` value `kv` (a `*kvServer`'s) over `s`. -/
opaque quotaKVAt (q : Loc) (kv : GoInterface) (s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque leaseServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque quotaLeaseAt (q : Loc) (ls : GoInterface) (s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque authServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque clusterServerAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- A `*maintenanceServer` over `s` (`NewMaintenanceServer`'s inner value). -/
opaque maintAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- An `*authMaintenanceServer` (the registered maintenance value). -/
opaque authMaintAt (p s : Loc) (γ : Cluster) : IProp GF := iprop(True)
/-- A `header` value of `s` (cluster and member ids, the raft status getter, the revision). -/
opaque headerAt (h : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header) (s : Loc) (γ : Cluster) :
  IProp GF := iprop(True)
opaque authAdminAt (aa : Loc) (s : Loc) (γ : Cluster) : IProp GF := iprop(True)
opaque quotaAlarmerAt (qa : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer) (s : Loc)
  (γ : Cluster) : IProp GF := iprop(True)
/-- A `notifier` (the health notifier) value. -/
opaque notifierAt (n : GoInterface) : IProp GF := iprop(True)

def handles_persistent.spec : Prop :=
  (∀ p s γ, Persistent (kvServerAt (GF := GF) p s γ)) ∧
  (∀ q kv s γ, Persistent (quotaKVAt (GF := GF) q kv s γ)) ∧
  (∀ p s γ, Persistent (leaseServerAt (GF := GF) p s γ)) ∧
  (∀ q l s γ, Persistent (quotaLeaseAt (GF := GF) q l s γ)) ∧
  (∀ p s γ, Persistent (authServerAt (GF := GF) p s γ)) ∧
  (∀ p s γ, Persistent (clusterServerAt (GF := GF) p s γ)) ∧
  (∀ p s γ, Persistent (maintAt (GF := GF) p s γ)) ∧
  (∀ p s γ, Persistent (authMaintAt (GF := GF) p s γ)) ∧
  (∀ h s γ, Persistent (headerAt (GF := GF) h s γ)) ∧
  (∀ aa s γ, Persistent (authAdminAt (GF := GF) aa s γ)) ∧
  (∀ qa s γ, Persistent (quotaAlarmerAt (GF := GF) qa s γ)) ∧
  (∀ n, Persistent (notifierAt (GF := GF) n)) ∧
  (∀ γ md who, Persistent (mdPrin (GF := GF) γ md who)) ∧
  (∀ s γ, Persistent (srvOk (GF := GF) s γ)) ∧
  (∀ g j m, Persistent (rsChunk (GF := GF) g j m)) ∧
  (∀ g who r Q, Persistent (rsReq (GF := GF) g who r Q))

/-! ### The shape of a unary handler's spec -/

/-- **A unary handler `f` of method `m`** (a service method `(ctx, req) → (resp, err)`, `P` its
receiver's handle): a run with the thread's token, the run's context, the request (owned: grpc
decoded it for this run) and the method's contract returns the token and `unaryOut`. Its instance at
the registered service value is what `Grpc.start` needs of each registration (with the generated
handler's decoding, 3h). -/
def HandlerTriple (f : val) (P : IProp GF) (S : UnarySpec (GF := GF)) (reqT repT : go.GoType) : Prop :=
  ∀ (ctx : GoInterface) (md : MD) (q : Loc) (c : Content) (Φ : Outcome → IProp GF),
  {{ P ∗ threadTok ∗ rpcCtx ctx md ∗ msgAt reqT q (DFrac.own 1) c ∗ S md c Φ }}
    (App (App (Val f) (Val #ctx)) (Val #q))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      unaryOut repT (msgVal repT resp) err Φ }}

end res

end V3rpc
end EtcdGrove
end Perennial
