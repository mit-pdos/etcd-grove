/-
# etcd's server: the request path (batch 2c), vocabulary

What `v3_server.go` (`EtcdServer.Range`, `RangeStream`, `Put`, `DeleteRange`, `Txn`, `Compact`,
the lease, alarm and auth methods, `raftRequest`, `processInternalRaftRequestOnce`, `doSerialize`)
gives its callers: the gRPC handlers (2a), the server's own internal requesters (the lessor's
revocations and checkpoints, the compactor, the alarms, `publishV3`, the cluster version, the
health checks: 2d/2e). Namespace `EtcdServer`, shared with the apply thread (2d, `ApiApply.lean`)
and the lifecycle (2e, `ApiBoot.lean`, whose `isServer s γ` is the handle every spec here takes).
The error values are in `errors/Api.lean` (`srvErrOf`, `srvErrVal`, `srvErrShape`, `srvIndef`,
`srvUnfired`).

## The shape, in words

**Each call is the client's contract at the server** (W0's `KV.*Triple`, `ClientV3.CallTriple`):
the caller hands an atomic update over W0's `etcdState γ` (persistent for a read, `Req.isRead`; one
-shot otherwise) with the auth-table bound `lo` of its call (W0's `authLb`, `Step`'s `lo`) and gets
back one of three outcomes (`SrvCallTriple`):

1. **fired**: the update fired once (a write: at its entry's commit, with the answer its apply
   computes; a read: at the state the member read), and the reply is that answer: the reply message
   on success, or a server error of the answer's `EtcdErr` (`srvErrOf`);
2. **not fired, given back** (`srvUnfired`): the request never took effect and never will (a
   refusal before proposing: too many requests, too large, an invalid token; a stale auth revision
   at the apply, which the client's interceptor resends; an error before anything was proposed);
3. **unsettled** (`srvIndef`): an error after which the request may still take effect.

Every returned error carries `srvErrShape` (a context's error, or a mapped leaf sentinel, or an
unmapped error with its message): what 2a's `togRPCError` and the callers' `errors.Is` need.

**The principal** (`reqPrin ctx p tls`). The server reads it with `AuthInfoFromCtx` (`v3_server.go:
1206`): with auth enabled and a token, the token's user; otherwise the TLS client certificate's common
name when `--client-cert-auth` is set (`AuthInfoFromTLS`), else none. So a context determines two
principals: `p`, the one used with auth enabled (the token's user, else the certificate's name: W0's
`ctxPrin`'s), and `tls`, the certificate's name (none without `--client-cert-auth`), used with auth
disabled. With auth disabled no check of `Step` depends on the principal, except one: **a write whose
header was filled while auth was disabled and that is applied after `AuthEnable`** (which keeps the
auth revision, so the apply's revision check passes) is checked as `tls`
(`nonissues/etcd-write-tls-principal-auth-enable.md`). The relation the server fires updates by is
therefore `srvStep p tls rq`: W0's `Step p rq`, or, for a write, `Step tls rq`; it is `Step p` when
`tls = p` (or `tls = none`: a principal-less write is refused, `ErrUserEmpty`, with auth on). One
more disjunct, `emptyRangeStep`: a range of the empty key (the health checks), which the server
reads as the key `""` where W0's model answers the gRPC layer's `ErrEmptyKey`. The `doSerialize`
race of round 0 is gone: W0's `Step` checks a read's permission at an auth table at or after the
call's `lo` (`deniedSince`, `authOffSince`), which is what the code does; so is `LeaseRenew`'s
permission error (W0's `leaseKeepAlive` has it).

**Internal requests** (`raftRequest`'s other callers) are modelled by `IrrBody`: a client request
`Req`, `Authenticate`'s token (`.authToken`: fired iff the auth revision is still the checked one),
an alarm's activation, a member's publication, or nothing observable (a lease checkpoint, the
cluster version, the downgrade info). Only a client request's (and `.authToken`'s) commit fires the
proposer's update (`IrrBody.fires`); an alarm or a publication is an environment step the cluster's
invariant takes by the `envUpd` the server holds.

## Vocabulary

* `srvStep p tls rq σ σ' res lo` (transparent): see above.
* `reqPrin ctx p tls` (persistent, opaque): the request context's two principals. Introduction:
  `reqPrin_noIncoming` (a context with no incoming gRPC metadata and no peer, `ctxNoIncoming`: the
  internal requesters' `s.ctx`, `context.Background()` and their children), `reqPrin_child`,
  `reqPrin_value`; 3d's `WithRoot` spec (`req/go_etcd_io_etcd_server_v3_auth.md`); 2a's handler
  contexts (`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`: `reqPrin_of_md` in 2a's module,
  which imports this one).
* `ctxNoIncoming ctx` (persistent, opaque) with `ctxNoIncoming_background`, `_child`, `_value`.
* `reqReply γ rq`, `srvReply`: the replies (W0's and 1c's reply predicates), the server's return.
* `IrrBody`, `irrStep`, `IrrBody.fires`, `IrrBody.wf` (the validation the gRPC layer does, and the
  depth bound: `issues/etcd-txn-nested-depth-apply-panic.md`), `IrrBody.backOk`, `respTy`,
  `irrReply`, `irrOwn p dq ir` (provisional, 3h's), `applyResult`.
* `txnChecked t` (pure, opaque; provisional, 2a's: `checkTxnRequest`'s `nil`) with the
  introduction `txnChecked_small` (a flat transaction of at most one comparison and one operation per
  branch, each valid).
* `rangeStreamOk r` (pure): the default order and no revision filters (`checkRangeStreamRequest`).
* `alarmReqOwn p dq ir` (provisional, 3h's), `rsSink rs γ p r ms` (provisional, 2a's: a range stream's
  send end), `srvWatchable s γ w` (provisional, 2d's and 3f's) with `srvWatchable_persistent`,
  `srvWatchable_mvcc`, `traceAt tr` (4b's).
* `SrvCallTriple e P B γ p tls rq rep reply`: the three-outcome call shape.
* `txnMsgDepth`.

## Intended realization

`reqPrin ctx p tls`: `AuthInfoFromCtx`'s contract at `ctx` (3d): with auth enabled it returns the
token's user (`p`) or `ErrInvalidAuthToken`; without a token, or with auth disabled, `AuthInfoFromTLS`'s
user (`tls`) or `nil`. The cluster side (2d's cluster invariant, `ApiApply.lean`): the proposals'
registry (each pending request id's deposited update), the wait registry's answer predicate
(`Wait.listAt s.w γw P`: for a normal entry's id, a non-nil `*apply.Result` carrying the `Q` of the
requester's update fired at the entry's commit, or the update itself for outcome 2; for a conf
change's id, a non-nil `*confChangeResponse`), the **read registry** (each registered persistent
read update, fired at every history point from its registration on).

## Requirement snippets

`examples/specreq/etcdserverreq/`: `kv.go`, `lease.go`, `auth.go`, `read.go`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Spec.go_etcd_io.etcd.client.v3.ApiClient
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.errors.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.apply
public import GeneratedProof.google_golang_org.grpc.peer

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire
open Classical

/-! ## The relation of the server's updates -/

/-- **A range of the empty key** (`key = []`, `rangeEnd = []`: the health checks' form), which the
server reads as the single key `""` (W0's `kvStep` answers it with the gRPC layer's `ErrEmptyKey`,
which the server does not compute): no key is empty (`etcdLb_keyNonEmpty`), so an empty answer, a
revision error, or a permission refusal, at the current history or a member's view. -/
def emptyRangeStep (p : Principal) (rq : Req) (σ σ' : State) (res : Resp) : Prop :=
  ∃ r, rq = .range r ∧ r.key = [] ∧ r.rangeEnd = [] ∧ σ' = σ ∧
    (res = .err (AuthState.permErr p) ∨
     ∃ v, (if r.serializable then σ.kv.IsView v else v = σ.kv) ∧
       ((∃ e, r.revErr v = some e ∧ res = .err e) ∨
        r.revErr v = none ∧ res = .ok (.range v.rev { kvs := [], more := false, count := 0 })))

/-- **The relation the server fires its callers' updates by** (see the header): W0's `Step` as the
principal `p`, or, for a write, as the certificate's `tls`; and the empty-key range. -/
def srvStep (p tls : Principal) (rq : Req) (σ σ' : State) (res : Resp) (lo : Nat) : Prop :=
  Step p rq σ σ' res lo ∨ (rq.isRead = false ∧ Step tls rq σ σ' res lo) ∨
  emptyRangeStep p rq σ σ' res

/-! ## Internal requests -/

/-- **What an `InternalRaftRequest` asks** (the model `raftRequest` takes). -/
inductive IrrBody where
  /-- a client request (KV writes, compactions, lease grants and revocations, auth, alarm list
  and disarm) -/
  | req (rq : Req)
  /-- `Authenticate`'s token for user `name` (password `pw`, checked at auth revision `rev`) -/
  | authToken (name pw : GoString) (rev : Nat)
  /-- an alarm raised (`AlarmRequest_ACTIVATE`: the quota, the corruption check) -/
  | alarmActivate (al : Alarm)
  /-- a member's attributes published (`ClusterMemberAttrSet`, `publishV3`) -/
  | publish (id : Nat) (name : GoString) (urls : List GoString)
  /-- no observable effect: a lease checkpoint, the cluster version, the downgrade info -/
  | noop

/-- Whether the request's commit fires its proposer's update: a client request's, `Authenticate`'s
token's; an alarm or a publication is an environment step the cluster's invariant takes by its
`envUpd` (2e's `isServer`), a `.noop` changes nothing. -/
def IrrBody.fires : IrrBody → Bool
  | .req _ | .authToken .. => true
  | _ => false

/-- The relation of the proposer's update (`fires`), or the effect of the entry (the others). -/
def irrStep (p tls : Principal) (lo : Nat) : IrrBody → State → State → Resp → Prop
  | .req rq => fun σ σ' res => srvStep p tls rq σ σ' res lo
  | .authToken name pw _ => fun σ σ' res => srvStep p tls (.authenticate name pw) σ σ' res lo
  | .alarmActivate al => fun σ σ' _ => σ' = { σ with alarms := σ.alarms ++ [al] } ∨ σ' = σ
  | .publish id name urls => fun σ σ' _ =>
      ((∃ m ∈ σ.members, m.id = id) ∧
        σ' = { σ with members := σ.members.map (fun m =>
          if m.id = id then { m with name := name, clientURLs := urls } else m) }) ∨ σ' = σ
  | .noop => fun σ σ' _ => σ' = σ

/-- **The answers of a request whose update the commit gives back** (outcome 2 at the apply): an
apply refusal (`ErrAuthOldRevision`), or a token issued after the auth revision moved since the
password check (`Authenticate` retries with the update). -/
def IrrBody.backOk (ir : IrrBody) (res : Resp) : Prop :=
  (∃ e, res = .err e ∧ e.refusal = true) ∨ ((∃ n pw r, ir = .authToken n pw r) ∧ ∃ b, res = .ok b)

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

/-- (provisional, 2a's) **`t` passes the gRPC layer's validation** (`checkTxnRequest` and
`checkRequestOp` at the server's `--max-txn-ops`: the operations' own checks at every level, no key
written twice, `checkIntervals`). 2a's law gives it from `checkTxnRequest`'s `nil`;
`txnChecked_small` for the simplest transactions. -/
opaque txnChecked (t : TxnReq) : Prop

/-- A flat valid operation: a range, put or delete W0's `RequestOp.valid` accepts. -/
def opFlatValid : RequestOp → Prop
  | .range r => r.key ≠ [] ∧ r.validSort
  | .put p => p.invalid = none
  | .deleteRange d => d.key ≠ []
  | _ => False

/-- **A small transaction passes the gRPC layer's checks**: at most one comparison (with a key) and
one flat valid operation per branch (`--max-txn-ops ≥ 1`, `NewServer`'s configuration; one
operation per branch writes no key twice). -/
def txnChecked_small.spec : Prop := ∀ (t : TxnReq),
  t.compare.length ≤ 1 → (∀ c ∈ t.compare, c.key ≠ []) →
  t.success.length ≤ 1 → t.failure.length ≤ 1 →
  (∀ op ∈ t.success, opFlatValid op) → (∀ op ∈ t.failure, opFlatValid op) → txnChecked t

/-- **What the server needs of a request it proposes** (the gRPC layer's checks, which the server
does not repeat: it would apply an empty key or an `IgnoreValue` put with a value; and the depth
every member's apply can decode: `issues/etcd-txn-nested-depth-apply-panic.md`). -/
def IrrBody.wf : IrrBody → Prop
  | .req (.put p) => p.invalid = none
  | .req (.deleteRange d) => d.key ≠ []
  | .req (.txn t) => txnChecked t ∧ txnMsgDepth t + 1 ≤ 10000
  | .req (.compact rev _) => rev ≠ 0
  | _ => True

/-- `checkRangeStreamRequest`: the default order, no revision filters (the paging needs both). -/
def rangeStreamOk (r : RangeReq) : Prop :=
  isDefaultOrdering r.sortTarget r.sortOrder ∧ ¬ r.hasRevFilters

section types
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

end types

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The read loop's errors are unsettled ones (`ErrStopped`, `ErrLeaderChanged`, `ErrTimeout`;
raft's `ErrStopped`, unmapped; a context's error, never mapped: `srvErrOf_notCtx`). -/
def readErr_indef.spec : Prop := ∀ err, Read.readErr (GF := GF) err ⊢ ⌜srvIndef err⌝

/-- The read loop's errors have the returned errors' shape. -/
def readErr_shape.spec : Prop := ∀ err, Read.readErr (GF := GF) err ⊢ srvErrShape err

/-! ### The principal -/

/-- **The request context `ctx`'s principals** (persistent; see the header): `p` with auth
enabled, `tls` (the client certificate's name) with auth disabled. -/
opaque reqPrin (ctx : GoInterface) (p tls : Principal) : IProp GF := iprop(True)

/-- **`ctx` carries no incoming gRPC metadata and no peer** (persistent): what the server's internal
requesters' contexts are (`s.ctx`, `context.Background()`, their children). -/
opaque ctxNoIncoming (ctx : GoInterface) : IProp GF := iprop(True)

def reqPrin_persistent.spec : Prop := ∀ ctx p tls, Persistent (reqPrin (GF := GF) ctx p tls)
def ctxNoIncoming_persistent.spec : Prop := ∀ ctx, Persistent (ctxNoIncoming (GF := GF) ctx)

/-- No token, no certificate: no principal. -/
def reqPrin_noIncoming.spec : Prop := ∀ ctx, ctxNoIncoming (GF := GF) ctx ⊢ reqPrin ctx none none

def ctxNoIncoming_background.spec : Prop :=
  ⊢ ctxNoIncoming (GF := GF) (GoInterface.ok context.backgroundCtxVal)

/-- Children (`WithCancel`, `WithTimeout`) keep the principals and the absence of metadata. -/
def reqPrin_child.spec : Prop := ∀ ctx ctx' p tls,
  reqPrin (GF := GF) ctx p tls ∗ Context.ctxChild ctx ctx' ⊢ reqPrin ctx' p tls

def ctxNoIncoming_child.spec : Prop := ∀ ctx ctx',
  ctxNoIncoming (GF := GF) ctx ∗ Context.ctxChild ctx ctx' ⊢ ctxNoIncoming ctx'

/-- A `WithValue` at another key than the incoming metadata's and the peer's keeps them. -/
def reqPrin_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk) p tls,
  reqPrin (GF := GF) ctx p tls ∗ Context.ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ google_golang_org.grpc.metadata.mdIncomingKey.ty ∧
      ki.ty ≠ google_golang_org.grpc.peer.peerKey.ty⌝ ⊢ reqPrin ctx' p tls

def ctxNoIncoming_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk),
  ctxNoIncoming (GF := GF) ctx ∗ Context.ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ google_golang_org.grpc.metadata.mdIncomingKey.ty ∧
      ki.ty ≠ google_golang_org.grpc.peer.peerKey.ty⌝ ⊢ ctxNoIncoming ctx'

/-! ### Messages and slots -/

/-- (provisional, 3h's) **`p` is an `InternalRaftRequest` asking `ir`** (the outer struct owned,
its `Header` any, `ID` `0`; the inner request messages at fraction `dq`). 3h's laws wrap a request
message into one (`&pb.InternalRaftRequest{Put: r}`) and take it back out. -/
opaque irrOwn (p : Loc) (dq : DFrac) (ir : IrrBody) : IProp GF := iprop(True)

/-- (provisional, 3h's) **`p` is an `AlarmRequest` asking `ir`** (`.req .alarmList` for `GET`,
`.req (.alarmDisarm al)` for `DEACTIVATE`, `.alarmActivate al` for `ACTIVATE`; fraction `dq`). -/
opaque alarmReqOwn (p : Loc) (dq : DFrac) (ir : IrrBody) : IProp GF := iprop(True)

/-- (provisional, 2a's) **The send end of a range stream** (`KV_RangeStreamServer` value `rs`,
exclusive): the range `r` of principal `p`, the chunks `ms` sent so far. Sending appends a chunk
(any: the server sends its pages as it reads them); `rs.Context()` is a context with `reqPrin`
of `p`. Its laws are 2a's (`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`, "from 2c"). The
caller's update's `Q` is not sent with a chunk: `RangeStream` gives it with a `nil` return. -/
opaque rsSink (rs : GoInterface) (γ : Cluster) (p tls : Principal) (r : RangeReq)
  (ms : List RangeRespM) : IProp GF := iprop(True)

/-- (provisional, 3f's and 2d's) **`w` is member `s`'s watchable store** (`mvcc.WatchableKV`), whose
history is the member's applied prefix of `γ`'s. Persistent. -/
opaque srvWatchable (s : Loc) (γ : Cluster) (w : GoInterface) : IProp GF := iprop(True)

def srvWatchable_persistent.spec : Prop := ∀ s γ w, Persistent (srvWatchable (GF := GF) s γ w)

/-- The watchable store is mvcc's (3f's `watchableAt`); the bridge of its store names to `γ`'s
history is 2d's (`req/`). -/
def srvWatchable_mvcc.spec : Prop := ∀ s γ w,
  srvWatchable (GF := GF) s γ w ⊢ ∃ γs, Mvcc.watchableAt w γs

/-- (provisional, 4b's) **`tr` is a trace** (`*traceutil.Trace`, possibly `nil`): its methods are
safe to call. -/
opaque traceAt (tr : Loc) : IProp GF := iprop(True)

/-! ### Replies -/

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
server error of the answer's `EtcdErr`, with its shape. -/
def srvReply (reply : Resp → Loc → GoInterface → IProp GF) (res : Resp) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  match res with
  | .err e => iprop(⌜resp = null ∧ srvErrOf err e⌝ ∗ srvErrShape err)
  | .ok _ => reply res resp err

/-- **An internal request's reply** as a `proto.Message`: a client request's (and `Authenticate`'s
token's) reply message, its dynamic type `*pb.<Kind>Response`; anything for the others (no caller
reads it). -/
def irrReply (γ : Cluster) (ir : IrrBody) (res : Resp) (resp : GoInterface) : IProp GF :=
  match ir with
  | .req rq => iprop(∃ p : Loc, ⌜resp = interface.mkOk (go.GoType.PointerType (respTy rq)) #p⌝ ∗
      reqReply γ rq res p GoInterface.nil)
  | .authToken name pw _ => iprop(∃ p : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType (respTy (.authenticate name pw))) #p⌝ ∗
      ClientV3.authReply γ name res p GoInterface.nil)
  | _ => iprop(True)

/-- **The apply's result `x` for `ir` answered `res`** (`*apply.Result`, non-nil, read-only). -/
def applyResult (γ : Cluster) (x : Loc) (ir : IrrBody) (res : Resp) : IProp GF :=
  iprop(⌜x ≠ null⌝ ∗ ∃ (resp : GoInterface) (err : GoInterface) (ph : Loc) (tr : Loc),
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Resp"] ↦□ resp ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Err"] ↦□ err ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Physc"] ↦□ ph ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Trace"] ↦□ tr ∗
    traceAt tr ∗ (⌜ph = null⌝ ∨ Read.recvAny ph) ∗
    match res with
    | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ irrReply γ ir res resp)
    | .err e => iprop(⌜srvErrOf err e⌝ ∗ srvErrShape err))

/-! ## The call shape -/

/-- **A server call** `e` for request `rq` by the principals `p`, `tls` (the update persistent if
`rep`; the caller's auth-table bound `lo`), `P` the caller's resources, `B` given back, `reply` the
success reply: outcome 1 (fired, with its reply), 2 (not fired: the update given back) or 3
(unsettled); every error with its shape. -/
def SrvCallTriple (e : Expr) (P B : IProp GF) (γ : Cluster) (p tls : Principal) (rq : Req)
    (rep : Bool) (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (lo : Nat) (Q : State → State → Resp → IProp GF),
  {{ P ∗ authLb γ lo ∗ □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls rq σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((∃ σ σ' res, Q σ σ' res ∗ srvReply reply res resp err) ∨
       (⌜resp = null ∧ srvUnfired err⌝ ∗ srvErrShape err ∗
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls rq σ σ' res lo⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>) ∨
       (⌜resp = null ∧ srvIndef err⌝ ∗ srvErrShape err)) }}

end vocab

end EtcdServer
end EtcdGrove
end Perennial
