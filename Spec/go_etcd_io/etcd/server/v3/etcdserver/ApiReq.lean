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
call's `lo` (`deniedSince`, `permittedSince`: W0's round 6), which is what the code does; so is `LeaseRenew`'s
permission error (W0's `leaseKeepAlive` has it).

**Internal requests** (`raftRequest`'s other callers) are modelled by 3h's `EtcdServerPb.IrrBody`
(re-exported here): a client request `Req`, `Authenticate`'s token (`.authToken name`), an alarm's
activation, a member's publication, or nothing observable (a lease checkpoint, the cluster version,
the downgrade info). The proposer's update is over a client request `aq` with `irrAsks ir (some aq)`:
a client request's own, the token's `authenticate` request (its password is the update's: the
message carries none), a client's alarm activation; the quota's activation and a publication carry
no update (`none`): an environment step the cluster's invariant takes by the `envUpd` the server
holds.

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
* `IrrBody` (3h's), `irrAsks`, `irrUpd`, `irrWf` (the validation the gRPC layer does, and the
  depth bound: `issues/etcd-txn-nested-depth-apply-panic.md`), `irrBackOk`, `respTy`,
  `irrReply`, `irrOwn p dq ir` (3h's, integration X), `applyResult` (its trace
  4b's `traceOpt`).
* `reqCtxOk ctx` (4b's `ctxTraceIs ctx none`, otel's `ctxSpanOk`): the request context's tracing,
  in every spec's pre; `ctxTrace ctx` (the context's trace, owned: `doSerialize`).
* `txnChecked t` (pure, opaque; provisional, 2a's: `checkTxnRequest`'s `nil`) with the
  introduction `txnChecked_small` (a flat transaction of at most one comparison and one operation per
  branch, each valid).
* `rangeStreamOk r` (pure): the default order and no revision filters (`checkRangeStreamRequest`).
* `alarmReqOwn p dq ir` (3h's), `rsSink rs γ p r ms` (provisional, 2a's: a range stream's
  send end), `srvWatchable s γ w` (provisional, 2d's and 3f's) with `srvWatchable_persistent`,
  `srvWatchable_mvcc`.
* `SrvCallTriple e P B γ p tls rq rep reply`: the three-outcome call shape.
* `txnMsgDepth` (3h's).

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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api
public import Spec.go_etcd_io.etcd.client.v3.ApiClient
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.errors.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiWatch
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.apply
public import GeneratedProof.google_golang_org.grpc.peer
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api
public import Spec.go_opentelemetry_io.otel.trace.Api

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

/-! ## Internal requests

The model of an `InternalRaftRequest` is 3h's `EtcdServerPb.IrrBody` (the message's content: a client
request, an alarm's activation, a member's publication, `Authenticate`'s token for a user, or nothing
observable), with its depth functions; this file re-exports them under `EtcdServer`. What the server
adds: the update the commit fires (`irrAsks`, `irrUpd`), the validation the server relies on
(`irrWf`), and the answers with which the update is given back (`irrBackOk`). -/

export EtcdServerPb (IrrBody opMsgDepth opsMsgDepth txnMsgDepth alarmReqOwn)

/-- **The update the commit of `ir` fires** (`ao`: the client request the proposer's atomic update
is over; `none`: no update). A client request fires its own; `Authenticate`'s token (`.authToken
name`) the `authenticate` request whose password the server checked before proposing (Go proposes
only the name and the token prefix: the password is the update's, not the message's); an alarm's
activation a client's `Alarm(ACTIVATE)` (W0's `Req.alarmActivate`), or none (the quota's and the
corruption checker's: an environment step the cluster's invariant takes by its `envUpd`); a
publication or a `.noop` none. -/
def irrAsks : IrrBody → Option Req → Prop
  | .req rq, ao => ao = some rq
  | .authToken name, ao => ∃ pw, ao = some (.authenticate name pw)
  | .alarmActivate al, ao => ao = none ∨ ao = some (.alarmActivate al)
  | _, ao => ao = none

/-- **The answers of a request whose update the commit gives back** (outcome 2 at the apply): an
apply refusal that is not indefinite (`ErrAuthOldRevision`), or a token issued after the auth state
moved since the password check (`Authenticate` retries with the update). -/
def irrBackOk (ir : IrrBody) (res : Resp) : Prop :=
  (∃ e, res = .err e ∧ e.refusal = true ∧ e.indefinite = false) ∨
  ((∃ n, ir = .authToken n) ∧ ∃ b, res = .ok b)

/-- (provisional, 2a's) **`t` passes the gRPC layer's validation** (`checkTxnRequest` and
`checkRequestOp` at the server's `--max-txn-ops`: the operations' own checks at every level, no key
written twice, `checkIntervals`). 2a's law gives it from `checkTxnRequest`'s `nil`;
`txnChecked_small` for the simplest transactions. -/
opaque txnChecked (t : TxnReq) : Prop

/-- **The gRPC layer's checks make a transaction safe for the apply** (3b's `Txn.txnSafe`: no key
written twice on a path, the fork's fix of `issues/etcd-txn-delete-then-ignore-put.md`; 3b's
request, integration I3 item (e)). -/
def txnChecked_safe.spec : Prop := ∀ (t : TxnReq), txnChecked t → Txn.txnSafe t

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
every member's apply can decode, 3h's `IrrBody.depthOk`: `issues/etcd-txn-nested-depth-apply-panic.md`). -/
def irrWf : IrrBody → Prop
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
  | .alarmActivate _ => AlarmResponse.ty

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
opaque reqPrin [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ctx : GoInterface) (p tls : Principal) : IProp GF := iprop(True)

/-- **`ctx` carries no incoming gRPC metadata and no peer** (persistent): what the server's internal
requesters' contexts are (`s.ctx`, `context.Background()`, their children). Integration I3/I4: 2a's
`Grpc.ctxInMD`/`ctxPeerCN` at `none` (their background/child/value laws give this file's). -/
def ctxNoIncoming (ctx : GoInterface) : IProp GF :=
  iprop(Grpc.ctxInMD ctx none ∗ Grpc.ctxPeerCN ctx none)

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

/-- **`p` is an `InternalRaftRequest` asking `ir`** (the outer struct owned, its `Header` unset,
`ID` `0`; the inner request message at fraction `dq`): 3h's `EtcdServerPb.irrOwn` (integration X: a
writer wraps the request message its caller lent it, `&pb.InternalRaftRequest{Put: r}`, by
`irrOwn_wrap`, and takes it back by `irrOwn_unwrap`). -/
abbrev irrOwn (p : Loc) (dq : DFrac) (ir : IrrBody) : IProp GF := EtcdServerPb.irrOwn p dq ir

/-- (provisional, 2a's) **The send end of a range stream** (`KV_RangeStreamServer` value `rs`,
exclusive): the range `r` of principal `p`, the chunks `ms` sent so far. Sending appends a chunk
(any: the server sends its pages as it reads them); `rs.Context()` is a context with `reqPrin`
of `p`. Its laws are 2a's (`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`, "from 2c"). The
caller's update's `Q` is not sent with a chunk: `RangeStream` gives it with a `nil` return. -/
opaque rsSink [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rs : GoInterface) (γ : Cluster) (p tls : Principal) (r : RangeReq)
  (ms : List RangeRespM) : IProp GF := iprop(True)

/-- (provisional, 3f's and 2d's) **`w` is member `s`'s watchable store** (`mvcc.WatchableKV`), whose
history is the member's applied prefix of `γ`'s. Persistent. -/
opaque srvWatchable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : Cluster) (w : GoInterface) : IProp GF := iprop(True)

def srvWatchable_persistent.spec : Prop := ∀ s γ w, Persistent (srvWatchable (GF := GF) s γ w)

/-- The watchable store is mvcc's (3f's `watchableAt`); the bridge of its store names to `γ`'s
history is 2d's (`req/`). -/
def srvWatchable_mvcc.spec : Prop := ∀ s γ w,
  srvWatchable (GF := GF) s γ w ⊢ ∃ γs, Mvcc.watchableAt w γs

/-- **The watchable store is the member's mvcc store, its history the cluster's** (3f's bridge,
`req/`, "from 3f", item 3; integration I4): every `mvccLb` of it is a view of a state the cluster
has been in (the apply thread fires `End`'s notification only for a committed entry, `Restore` only
for a committed point's image). -/
def srvWatchable_hist.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (w : GoInterface) (γm : Mvcc.MvccName) (h : KVHist),
    srvNode (GF := GF) s γ id ∗ srvWatchable s γ.etcd w ∗ Mvcc.watchableAt w γm ∗ Mvcc.mvccLb γm h ⊢
      srvMvcc s γm ∗ |={⊤}=> ∃ σ, EtcdModel.etcdLb γ.etcd σ ∗ ⌜KVHist.IsView σ.kv h⌝

/-- **The request context's tracing** (4b's, otel's): no `traceutil` trace in it (each method
installs its own: `EnsureTrace`), and its otel span usable (`Tracer.Start`, `SpanFromContext`).
Persistent; the incoming gRPC context's (2a), the internal requesters' (`ctxTraceIs_background`,
`ctxSpanOk_background`, their children). -/
def reqCtxOk (ctx : GoInterface) : IProp GF :=
  iprop(TraceUtil.ctxTraceIs ctx none ∗ OtelTrace.ctxSpanOk ctx)

/-- **The trace a context carries, owned** (`doSerialize`'s `traceutil.Get`: the trace the caller's
`EnsureTrace` installed). -/
def ctxTrace (ctx : GoInterface) : IProp GF :=
  iprop(∃ o, TraceUtil.ctxTraceIs ctx o ∗
    match o with
    | none => iprop(True)
    | some t => TraceUtil.traceOwn t)

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

/-- **An internal request's reply** as a `proto.Message`: a client request's reply message (its
dynamic type `*pb.<Kind>Response`), `Authenticate`'s token's (an `*AuthenticateResponse`), an
alarm activation's (an `*AlarmResponse`, as a client's `Alarm(ACTIVATE)` reads it); anything for
the others (no caller reads it). -/
def irrReply (γ : Cluster) (ir : IrrBody) (res : Resp) (resp : GoInterface) : IProp GF :=
  match ir with
  | .req rq => iprop(∃ p : Loc, ⌜resp = interface.mkOk (go.GoType.PointerType (respTy rq)) #p⌝ ∗
      reqReply γ rq res p GoInterface.nil)
  | .authToken name => iprop(∃ p : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.api.v3.etcdserverpb.AuthenticateResponse.ty) #p⌝ ∗
      ClientV3.authReply γ name res p GoInterface.nil)
  | .alarmActivate al => iprop(∃ p : Loc,
      ⌜resp = interface.mkOk (go.GoType.PointerType (respTy (.alarmActivate al))) #p⌝ ∗
      reqReply γ (.alarmActivate al) res p GoInterface.nil)
  | _ => iprop(True)

/-- **The proposer's update for `ao`** (`irrAsks`): the caller's atomic update over `etcdState γ`
by `srvStep` of the request `aq` (persistent if `rep`), or nothing (`none`). -/
def irrUpd (γ : Cluster) (p tls : Principal) (lo : Nat) (ao : Option Req) (rep : Bool)
    (Q : State → State → Resp → IProp GF) : IProp GF :=
  match ao with
  | some aq => iprop(□?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
      <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls aq σ σ' res lo⌝ ∗ etcdState γ σ',
         COMM Q σ σ' res }>)
  | none => iprop(True)

/-- The update's `Q` fired (`True` without an update). -/
def irrFired (ao : Option Req) (Q : State → State → Resp → IProp GF) (σ σ' : State) (res : Resp) :
    IProp GF :=
  match ao with
  | some _ => Q σ σ' res
  | none => iprop(True)

/-- **The apply's result `x` for `ir` answered `res`** (`*apply.Result`, non-nil, its fields
read-only; its trace owned: 4b's `traceOpt`, exclusive, handed from the apply thread). -/
def applyResult (γ : Cluster) (x : Loc) (ir : IrrBody) (res : Resp) : IProp GF :=
  iprop(⌜x ≠ null⌝ ∗ ∃ (resp : GoInterface) (err : GoInterface) (ph : Loc) (tr : Loc),
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Resp"] ↦□ resp ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Err"] ↦□ err ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Physc"] ↦□ ph ∗
    x.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Trace"] ↦□ tr ∗
    TraceUtil.traceOpt tr ∗ (⌜ph = null⌝ ∨ Read.recvAny ph) ∗
    match res with
    | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ irrReply γ ir res resp)
    | .err e => iprop(⌜srvErrOf err e⌝ ∗ srvErrShape err))

/-- **The answers a server call fires** (outcome 1): not a token refusal (`ErrUserEmpty`,
`ErrAuthOldRevision`, `ErrInvalidAuthToken`: the client's interceptor resends with a new token, so
1c's `AttemptTriple` needs the update back) nor the learner's. The apply-time ones (`isOpPermitted`'s
`ErrUserEmpty` after an `AuthEnable`, `ErrAuthOldRevision`) change nothing, so the cluster's invariant
gives the update back (`irrBackOk`); the ones before proposing are outcome 2 already. 2a's
`V3rpc.firedAns` (integration I3/I4). -/
def srvFiredAns (res : Resp) : Prop :=
  ∀ e, res = .err e → ClientV3.errRetryAuth e = false ∧ e ≠ .notSupportedForLearner

/-- **`srvStep` is `Step` at the handler's calls** (2a's composition; integration I3/I4): with the
certificate's name none or the principal itself, no empty-key range (2a's check), and a fired
answer, `srvStep p tls` is W0's `Step p` (a principal-less write with auth on is only refused with
`ErrUserEmpty`, which is not fired). -/
def srvStep_step.spec : Prop := ∀ (p tls : Principal) (rq : Req) σ σ' res lo,
  (tls = none ∨ tls = p) → (∀ r, rq = .range r → r.key ≠ []) → srvFiredAns res →
  srvStep p tls rq σ σ' res lo → Step p rq σ σ' res lo

/-! ## The call shape -/

/-- **A server call** `e` for request `rq` by the principals `p`, `tls` (the update persistent if
`rep`; the caller's auth-table bound `lo`), `P` the caller's resources, `B` given back, `reply` the
success reply: outcome 1 (fired, with its reply), 2 (not fired: the update given back) or 3
(unsettled); every error with its shape. Outcome 1 fires no token or learner refusal
(`srvFiredAns`). -/
def SrvCallTriple (e : Expr) (P B : IProp GF) (γ : Cluster) (p tls : Principal) (rq : Req)
    (rep : Bool) (reply : Resp → Loc → GoInterface → IProp GF) : Prop :=
  ∀ (lo : Nat) (Q : State → State → Resp → IProp GF),
  {{ P ∗ authLb γ lo ∗ □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls rq σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    e
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); B ∗
      ((∃ σ σ' res, ⌜srvFiredAns res⌝ ∗ Q σ σ' res ∗ srvReply reply res resp err) ∨
       (⌜resp = null ∧ srvUnfired err⌝ ∗ srvErrShape err ∗
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls rq σ σ' res lo⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>) ∨
       (⌜resp = null ∧ srvIndef err⌝ ∗ srvErrShape err)) }}

end vocab

end EtcdServer
end EtcdGrove
end Perennial
