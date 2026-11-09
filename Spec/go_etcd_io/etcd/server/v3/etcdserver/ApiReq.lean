/-
# etcd's server: the request path (batch 2c), vocabulary

What `v3_server.go` (`EtcdServer.Range`, `RangeStream`, `Put`, `DeleteRange`, `Txn`, `Compact`,
the lease, alarm and auth methods, `raftRequest`, `processInternalRaftRequestOnce`, `doSerialize`)
gives its callers: the gRPC handlers (2a), the server's own internal requesters (the lessor's
revocations and checkpoints, the compactor, the alarms, `publishV3`, the cluster version, 2d/2e).
Namespace `EtcdServer`, shared with the apply thread (2d, `ApiApply.lean`) and the lifecycle (2e,
`ApiBoot.lean`, whose `isServer s γ` is the handle every spec here takes).

## The shape, in words

**Each call is the client's contract at the server** (W0's `KV.*Triple`, `ClientV3.CallTriple`):
the caller hands an atomic update over W0's `etcdState γ` (persistent for a read, `Req.isRead`, and
for the requests the client resends) and gets back one of three outcomes:

1. **fired**: the update fired once (a write: at its entry's commit, with the answer its apply
   computes; a read: at the state the member read), and the reply is that answer: the reply message
   on success, or the server-side error of the answer's `EtcdErr` (`srvErrOf`), which 2a's
   `togRPCError` maps to rpctypes' value;
2. **not fired, given back** (`srvUnfired`): the request never took effect and never will (a
   refusal before proposing: too many requests, too large, an invalid token; a stale auth revision
   at the apply, which the client's interceptor resends; or an error after which nothing was
   proposed); the update is returned, so the client may resend it (K4: "a write rejected for a stale
   auth revision is not fired");
3. **unsettled** (`srvIndef`): an error after which the request may still take effect (a timeout,
   a lost leader, the server stopping, a context's error); the update is gone (it may fire later,
   inside the cluster's invariant).

The relation the update is fired by is `srvStep who rq`: W0's `Step`, and, **for a linearizable
read only, the race of `nonissues/etcd-doserialize-auth-enable-race.md`** (`authRace`): a read whose
permission check ran while auth was disabled is answered from a state where auth is enabled,
without the check. That disjunct is what the code does; the client's contract (`Step` alone) holds
only once the race is closed: a fix on the fork, or a scope premise (no `AuthEnable` while reads are
in flight). **Decision for the user** (`notes/specs-only/batch-2c.md`).

**The principal** of a request is the one its context names, `reqPrin ctx who` (the server reads it
with `AuthInfoFromCtx`: a token's user, a TLS certificate's common name, or none).

**Internal requests** (`raftRequest`'s other callers) are modelled by `IrrBody`: a client request
`Req` (lease revocations by the lessor, compactions by the compactor, alarm lists and disarms), an
alarm's activation, a member's publication, or a request with no observable effect (a lease
checkpoint, the cluster version, the downgrade info). Their callers hold W0's `envUpd`, from which
they build the update `raftRequest` takes (`irrStep`; an environment step whose apply changes
nothing is the identity, which an update built from `envUpd` answers by aborting it).

## Vocabulary

* `srvErrOf err e` (pure, opaque): `err` is a server-side error value that `togRPCError` maps to
  rpctypes' error `e` (`mvcc.ErrCompacted` for `.compacted`, `auth.ErrPermissionDenied` for
  `.permissionDenied`, `errors.ErrTimeout` for `.timeout`, `context.Canceled` for `.canceled`, ...).
  Laws: `srvErrOf_ne_nil`, `srvErrOf_fun`; `readErr_indef` (the read loop's errors are indefinite).
* `srvIndef err`, `srvUnfired err` (pure, transparent): the error classes of outcomes 3 and 2. An
  error `togRPCError` does not map (a gRPC `Unknown` at the client) is in both.
* `reqPrin ctx who` (persistent, opaque): the request context's principal (realized by 2a's gRPC
  metadata and 3d's `AuthInfoFromCtx`; introduction laws are theirs).
* `srvStep who rq` (transparent): the relation the server's updates are fired by (see above).
* `reqReply γ rq res p err` (transparent): the reply message `p` of request `rq` for the answer
  `res`, W0's (`getReply`, `putReply`, ..., `ClientV3.ansReply`, `ClientV3.authReply`); `srvReply`
  the server's return pair (the error a server error, not rpctypes').
* `IrrBody`, `irrStep`, `irrOwn p ir` (opaque; provisional, 3h's: the `InternalRaftRequest` message
  at `p` with exactly `ir`'s field set, its `Header` and `ID` unset), `respTy`, `irrReply`: the
  internal request's model and its reply.
* `applyResult x ir res` (transparent): the apply's `*apply.Result` at `x` (3a builds it, 2d
  delivers it through the wait registry): `Err` the answer's error or `nil`, `Resp` the reply,
  `Physc` a channel closed once a physical compaction is done (or `nil`), `Trace` a trace
  (`traceAt`, provisional, 4b's).
* `txnMsgDepth`: the protobuf nesting depth of a transaction (`issues/etcd-txn-nested-depth-
  apply-panic.md`: a write transaction is decoded by every member's apply, which panics above
  10000 levels).

## Intended realization

`reqPrin ctx who`: `AuthInfoFromCtx`'s contract at `ctx` (3d): it returns `nil` (then `who = none`),
an `AuthInfo` naming `who`'s user at some auth revision, or `ErrInvalidAuthToken`. The cluster
side (2d's cluster invariant, `ApiApply.lean`): the proposals' registry (each pending request id's
deposited update and its result's ghost name), the wait registry's answer predicate (`Wait.listAt
s.w γw P` with `P id x` := `x` is an `*apply.Result` for the entry of request `id`, carrying the `Q`
of the requester's update fired at the entry's commit, or the update itself for an apply refusal of
outcome 2), the **read registry** (each registered persistent read update, fired at every history
point from its registration on: `req/go_etcd_io_etcd_server_v3_etcdserver.md`, "from 2c").

## Requirement snippets

`examples/specreq/etcdserverreq/`: `kv.go` (the KV entry points as the gRPC handler and the
internal requesters call them: a put then a linearizable range, a serializable range, a read-only
and a write `Txn`, a `Compact` from the compactor, the response type assertions), `lease.go` (grant,
revoke from the lessor with the root context, renew, time-to-live, leases), `auth.go`
(authenticate, the admin calls), `read.go` (the read loop).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.client.v3.ApiClient
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.apply

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## The relation of the server's updates -/

/-- `σ` with auth disabled. -/
def authOff (σ : State) : State := { σ with auth := { σ.auth with enabled := false } }

/-- **The relation the server fires its callers' updates by**: W0's `Step`, and, for a read only,
`doSerialize`'s race with `AuthEnable` (`nonissues/etcd-doserialize-auth-enable-race.md`): the
answer of the step at the state with auth disabled, at a state where it is enabled. And
`LeaseRenew`'s permission refusal (`checkLeaseRenew`: `IsPutPermitted` of the lease's keys), which
W0's `leaseStep` lacks for `leaseKeepAlive` (requested of W0, `req/go_etcd_io_etcd_api_v3.md`, "from
2c": the disjunct goes once the model has it). -/
def srvStep (who : Principal) (rq : Req) (σ σ' : State) (res : Resp) : Prop :=
  Step who rq σ σ' res ∨
  (rq.isRead = true ∧ σ.auth.enabled = true ∧ σ' = σ ∧ Step who rq (authOff σ) (authOff σ) res) ∨
  ((∃ id, rq = .leaseKeepAlive id) ∧ σ' = σ ∧ res = .err (AuthState.permErr who))

/-! ## Internal requests -/

/-- **What an `InternalRaftRequest` asks** (the model `raftRequest` takes). -/
inductive IrrBody where
  /-- a client request (KV writes, compactions, lease grants and revocations, auth, alarm list
  and disarm) -/
  | req (rq : Req)
  /-- an alarm raised (`AlarmRequest_ACTIVATE`: the quota, the corruption check) -/
  | alarmActivate (al : Alarm)
  /-- a member's attributes published (`ClusterMemberAttrSet`, `publishV3`) -/
  | publish (id : Nat) (name : GoString) (urls : List GoString)
  /-- no observable effect: a lease checkpoint, the cluster version, the downgrade info -/
  | noop

/-- The effect of an internal request (by principal `who`). -/
def irrStep (who : Principal) : IrrBody → State → State → Resp → Prop
  | .req rq => srvStep who rq
  | .alarmActivate al => fun σ σ' _ => σ' = { σ with alarms := σ.alarms ++ [al] } ∨ σ' = σ
  | .publish id name urls => fun σ σ' _ =>
      ((∃ m ∈ σ.members, m.id = id) ∧
        σ' = { σ with members := σ.members.map (fun m =>
          if m.id = id then { m with name := name, clientURLs := urls } else m) }) ∨ σ' = σ
  | .noop => fun σ σ' _ => σ' = σ

-- The protobuf nesting depth of a `RequestOp` (itself `1`, its request `2`, a nested transaction's
-- `TxnRequest` `2` plus what it holds: a `Compare` one level below it, its operations theirs).
mutual
def opMsgDepth : RequestOp → Nat
  | .empty => 1
  | .txn cmps succ fail =>
      2 + max (if cmps = [] then 0 else 1) (max (opsMsgDepth succ) (opsMsgDepth fail))
  | _ => 2
def opsMsgDepth : List RequestOp → Nat
  | [] => 0
  | op :: ops => max (opMsgDepth op) (opsMsgDepth ops)
end

/-- The protobuf nesting depth of a `TxnRequest`'s messages (the `TxnRequest` itself `1`). -/
def txnMsgDepth (t : TxnReq) : Nat :=
  1 + max (if t.compare = [] then 0 else 1) (max (opsMsgDepth t.success) (opsMsgDepth t.failure))

/-- **An internal request every member's apply can decode**: a write transaction at most `9999`
messages deep below the `InternalRaftRequest` (protobuf-go's limit is `10000`;
`issues/etcd-txn-nested-depth-apply-panic.md`). -/
def IrrBody.depthOk : IrrBody → Prop
  | .req (.txn t) => txnMsgDepth t + 1 ≤ 10000
  | _ => True

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

open go_etcd_io.etcd.api.v3.etcdserverpb in
/-- The Go type of the reply to a request (`*pb.<Kind>Response`). -/
def respTy : Req → go.GoType
  | .range _ => RangeResponse.ty
  | .put _ => PutResponse.ty
  | .deleteRange _ => DeleteRangeResponse.ty
  | .txn _ => TxnResponse.ty
  | .compact .. => CompactionResponse.ty
  | .leaseGrant .. => LeaseGrantResponse.ty
  | .leaseRevoke _ => LeaseRevokeResponse.ty
  | .leaseKeepAlive _ => LeaseKeepAliveResponse.ty
  | .leaseTimeToLive .. => LeaseTimeToLiveResponse.ty
  | .leaseLeases => LeaseLeasesResponse.ty
  | .authEnable => AuthEnableResponse.ty
  | .authDisable => AuthDisableResponse.ty
  | .authStatus => AuthStatusResponse.ty
  | .authenticate .. => AuthenticateResponse.ty
  | .userAdd .. => AuthUserAddResponse.ty
  | .userGet _ => AuthUserGetResponse.ty
  | .userList => AuthUserListResponse.ty
  | .userDelete _ => AuthUserDeleteResponse.ty
  | .userChangePassword .. => AuthUserChangePasswordResponse.ty
  | .userGrantRole .. => AuthUserGrantRoleResponse.ty
  | .userRevokeRole .. => AuthUserRevokeRoleResponse.ty
  | .roleAdd _ => AuthRoleAddResponse.ty
  | .roleGet _ => AuthRoleGetResponse.ty
  | .roleList => AuthRoleListResponse.ty
  | .roleDelete _ => AuthRoleDeleteResponse.ty
  | .roleGrantPermission .. => AuthRoleGrantPermissionResponse.ty
  | .roleRevokePermission .. => AuthRoleRevokePermissionResponse.ty
  | .memberAdd .. => MemberAddResponse.ty
  | .memberRemove _ => MemberRemoveResponse.ty
  | .memberUpdate .. => MemberUpdateResponse.ty
  | .memberPromote _ => MemberPromoteResponse.ty
  | .memberList _ => MemberListResponse.ty
  | .alarmList => AlarmResponse.ty
  | .alarmDisarm _ => AlarmResponse.ty

/-- **`err` is a server-side error that `togRPCError` maps to rpctypes' `e`** (see the header). -/
opaque srvErrOf (err : GoInterface) (e : EtcdErr) : Prop

/-- **An error after which the request may still take effect** (outcome 3): not `nil`, and of an
indefinite kind if `togRPCError` maps it. -/
def srvIndef (err : GoInterface) : Prop :=
  err ≠ GoInterface.nil ∧ ∀ e, srvErrOf err e → e.indefinite = true

/-- **An error of a request that never takes effect** (outcome 2): not `nil`, a refusal or an
indefinite kind if mapped. -/
def srvUnfired (err : GoInterface) : Prop :=
  err ≠ GoInterface.nil ∧ ∀ e, srvErrOf err e → e.refusal = true ∨ e.indefinite = true

def srvErrOf_ne_nil.spec : Prop := ∀ err e, srvErrOf err e → err ≠ GoInterface.nil

/-- An error value maps to one `EtcdErr` (`toGRPCErrorMap` is a map). -/
def srvErrOf_fun.spec : Prop := ∀ err e e', srvErrOf err e → srvErrOf err e' → e = e'

/-- The read loop's errors are indefinite (`ErrStopped`, `ErrLeaderChanged`, `ErrTimeout`, raft's
`ErrStopped`: unmapped, a gRPC `Unknown`; `context.Canceled`, `DeadlineExceeded`). -/
def readErr_indef.spec : Prop := ∀ err, Read.readErr err → srvIndef err

end errs

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The request context `ctx` authenticates as `who`** (persistent; see the header). -/
opaque reqPrin (ctx : GoInterface) (who : Principal) : IProp GF := iprop(True)

def reqPrin_persistent.spec : Prop := ∀ ctx who, Persistent (reqPrin (GF := GF) ctx who)

/-- (provisional, 3h's) **`p` is an `InternalRaftRequest` asking `ir`** (owned; `Header` and `ID`
unset). -/
opaque irrOwn (p : Loc) (ir : IrrBody) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is an `AlarmRequest` asking `ir`** (`.req .alarmList` for `GET`,
`.req (.alarmDisarm al)` for `DEACTIVATE`, `.alarmActivate al` for `ACTIVATE`; fraction `dq`). -/
opaque alarmReqOwn (p : Loc) (dq : DFrac) (ir : IrrBody) : IProp GF := iprop(True)

/-- (provisional, 2a's) **The send end of a range stream** (`KV_RangeStreamServer` value `rs`,
exclusive): the range `r` of principal `who` whose caller's update has result `Q`, the chunks `ms`
sent so far, `fin` once the terminal chunk (with its header, the update's `Q` delivered to the
client through the stream) was sent. The server-side mirror of W0's `wireStreamAt`; its send laws
are 2a's (`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`, "from 2c"). -/
opaque rsSink (rs : GoInterface) (γ : Cluster) (who : Principal) (r : RangeReq)
  (Q : State → State → Resp → IProp GF) (ms : List RangeRespM) (fin : Bool) : IProp GF := iprop(True)

/-- (provisional, 3f's and 2d's) **`w` is member `s`'s watchable store** (`mvcc.WatchableKV`), at the
member's applied history of `γ`. Persistent. -/
opaque srvWatchable (s : Loc) (γ : Cluster) (w : GoInterface) : IProp GF := iprop(True)

/-- (provisional, 4b's) **`tr` is a trace** (`*traceutil.Trace`, possibly `nil`): its methods are
safe to call. -/
opaque traceAt (tr : Loc) : IProp GF := iprop(True)

/-- **The reply message `p` of request `rq` for the answer `res`** (W0's reply predicates). -/
def reqReply (γ : Cluster) (rq : Req) : Resp → Loc → GoInterface → IProp GF :=
  match rq with
  | .range _ => ClientV3.getReply
  | .put _ => ClientV3.putReply
  | .deleteRange _ => ClientV3.deleteReply
  | .txn _ => ClientV3.txnReply
  | .compact .. => ClientV3.compactReply
  | .authenticate name _ => ClientV3.authReply γ name
  | _ => ClientV3.ansReply

/-- **What a server method returns for the answer `res`**: the reply (success), or `nil` and a
server-side error of the answer's `EtcdErr`. -/
def srvReply (reply : Resp → Loc → GoInterface → IProp GF) (res : Resp) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  match res with
  | .err e => iprop(⌜resp = null ∧ srvErrOf err e⌝)
  | .ok _ => reply res resp err

/-- **An internal request's reply** as a `proto.Message`: a client request's reply message (its
dynamic type `*pb.<Kind>Response`); anything for the others (no caller reads it). -/
def irrReply (γ : Cluster) (ir : IrrBody) (res : Resp) (resp : GoInterface) : IProp GF :=
  match ir with
  | .req rq => iprop(∃ p : Loc, ⌜resp = interface.mkOk (go.GoType.PointerType (respTy rq)) #p⌝ ∗
      reqReply γ rq res p GoInterface.nil)
  | _ => iprop(True)

/-- **The apply's result `x` for `ir` answered `res`** (`*apply.Result`, read-only). -/
def applyResult (γ : Cluster) (x : Loc) (ir : IrrBody) (res : Resp) : IProp GF :=
  iprop(∃ (resp : GoInterface) (err : GoInterface) (ph : Loc) (tr : Loc),
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Resp"] ↦□ resp ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Err"] ↦□ err ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Physc"] ↦□ ph ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Trace"] ↦□ tr ∗
    traceAt tr ∗ (⌜ph = null⌝ ∨ Read.recvAny ph) ∗
    match res with
    | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ irrReply γ ir res resp)
    | .err e => iprop(⌜srvErrOf err e⌝))

/-! ## The call shape -/

/-- **A server call** `e` for request `rq` by `who` (the update persistent if `rep`), `P` the
caller's resources, `B` given back, `reply` the success reply: outcome 1 (fired, with its reply),
2 (not fired: the update given back) or 3 (unsettled). -/
def SrvCallTriple (e : Expr) (P B : IProp GF) (γ : Cluster) (who : Principal) (rq : Req)
    (rep : Bool) (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (Q : State → State → Resp → IProp GF),
  {{ P ∗ □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep who rq σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((∃ σ σ' res, Q σ σ' res ∗ srvReply reply res resp err) ∨
       (⌜resp = null ∧ srvUnfired err⌝ ∗
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep who rq σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>) ∨
       ⌜resp = null ∧ srvIndef err⌝) }}

end vocab

end EtcdServer
end EtcdGrove
end Perennial
