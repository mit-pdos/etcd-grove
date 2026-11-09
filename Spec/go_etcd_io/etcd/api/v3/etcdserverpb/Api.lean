/-
# etcd's v3 API messages (batch 3h): `etcdserverpb` (and `mvccpb`'s `KeyValue`)

The KV messages' ownership predicates are W0's (`api/v3/Wire.lean`: `rangeReqOwn`, ..., opaque,
with field-by-field unfold laws), the watch messages' 1b's (`client/v3/ApiWatch.lean`), the other
RPCs' 1c's (`reqOwn`, `replyOwn`, `client/v3/ApiClient.lean`); this batch **realizes** them: it
fixes what a message's protobuf content (`Proto.Content`, 2a) means for each model, which is what
gRPC transports between a client and a member (`Grpc.UnarySpec`'s contents) and what protobuf's
`Clone`/`Merge`/`Marshal` act on. It also specifies the generated code of the package: the getters,
the client stubs (`NewKVClient`, `kVClient.Put`, ...), the server-side handlers
(`_KV_Range_Handler`, ...) and registrations (`RegisterKVServer`, ...), and the descriptors'
initial values.

This module holds what does not mention the client's vocabulary (the server batches import it);
`Realize.lean` holds the laws over 1b's and 1c's predicates and the stubs' client-facing specs.

## The relations: what a content holds

One opaque relation per model, between a content and a model value (`reqHolds c rq`, `bodyHolds c
b`, `rangeRespHolds c m`, ...). Each is **functional in the content** (`holds_fun`: a content is
one message, so it holds one model; protobuf's `Content` is a value, so a content received over
gRPC holds what the sent one held: no law relates two addresses or two heaps), and each W0
predicate is `msgAt` of a content holding its model (`<pred>_msgAt`). They are relations, not
functions, because W0's model types have no `Inhabited` instance an opaque function would need;
they are not required to be total (a content of another message type holds no model of this one).

**Intended realization.** `Proto.msgAt T.ty p dq c` is realized for each etcdserverpb type `T` as
W0's field-level predicate (its unfold law's right side), the content `c` being the value of those
fields (proto3: a scalar is set iff non-zero) and of the unknown fields kept in `protoRest`; each
relation is "the content's fields are the model's" (`reqHolds c (.range r)`: `c` is a
`RangeRequest` content whose fields are `r`'s). The relation laws are then the unfold laws read
through that realization; the functional laws hold because the field values are a function of the
content.

## 2a's slots, realized

`V3rpc.reqModels m c rq`, `replyModels m b c`, `chunkModels c m` (2a's `v3rpc/Api.lean`, opaque
slots) are this module's `reqModels`, `replyModels`, `chunkModels` (transparent over the relations).

## Depth and size

Every etcd message but the transaction's is at most three levels deep (`holds_depth`: a reply, its
header or its key-values, a `KeyValue`'s nothing). A transaction nests as its model (`Req.nest`);
the bound is the server's to keep (`checkTxnRequest`, `--max-txn-ops`: 2a, 2c). Sizes are grpc's
workload premise (`Grpc.msgsFit`), not this package's.

## Requirement snippets

`examples/specreq/etcdserverpb/`: `getters.go` (a transaction's responses read through the
getters, nil-safe headers, the comparison's key, a range's sort names), `stubs.go` (the KV stub
over a client's connection, the watch stub's stream, a streamed range's chunks merged).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Wire
public import Spec.google_golang_org.grpc.Api
public import Spec.PkgInit.go_etcd_io.etcd.api.v3.etcdserverpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

/-! ## The relations (opaque) -/

/-- **The content `c` is a request message modelled by `rq`** (its Go type `reqType rq`). -/
opaque reqHolds (c : Proto.Content) (rq : Req) : Prop
/-- **The content `c` is the success reply of a non-KV RPC answered `b`** (Go type `bodyType b`;
the header's fields any). -/
opaque bodyHolds (c : Proto.Content) (b : RespBody) : Prop
opaque respHeaderHolds (c : Proto.Content) (m : HeaderM) : Prop
opaque keyValueHolds (c : Proto.Content) (m : KeyValueM) : Prop
opaque rangeRespHolds (c : Proto.Content) (m : RangeRespM) : Prop
opaque putRespHolds (c : Proto.Content) (m : PutRespM) : Prop
opaque deleteRespHolds (c : Proto.Content) (m : DeleteRespM) : Prop
opaque responseOpHolds (c : Proto.Content) (m : ResponseOpM) : Prop
opaque txnRespHolds (c : Proto.Content) (m : TxnRespM) : Prop
opaque compactRespHolds (c : Proto.Content) (m : CompactRespM) : Prop
opaque compareHolds (c : Proto.Content) (m : EtcdModel.Compare) : Prop
opaque requestOpHolds (c : Proto.Content) (m : RequestOp) : Prop
/-- **The content `c` is a `RangeStreamResponse` carrying the chunk `m`.** -/
opaque chunkHolds (c : Proto.Content) (m : RangeRespM) : Prop

/-- **Every range end of the content is `nil` or non-empty** (opaque, pure): the `RangeEnd` of a
`RangeRequest`, `DeleteRangeRequest`, `Compare` or `WatchCreateRequest`, nested ones included. -/
opaque endsOk : Proto.Content → Prop

section types
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The Go type of a request's message. -/
def reqType : Req → go.GoType
  | .range _ => etcdserverpb.RangeRequest.ty
  | .put _ => etcdserverpb.PutRequest.ty
  | .deleteRange _ => etcdserverpb.DeleteRangeRequest.ty
  | .txn _ => etcdserverpb.TxnRequest.ty
  | .compact _ _ => etcdserverpb.CompactionRequest.ty
  | .leaseGrant _ _ => etcdserverpb.LeaseGrantRequest.ty
  | .leaseRevoke _ => etcdserverpb.LeaseRevokeRequest.ty
  | .leaseKeepAlive _ => etcdserverpb.LeaseKeepAliveRequest.ty
  | .leaseTimeToLive _ _ => etcdserverpb.LeaseTimeToLiveRequest.ty
  | .leaseLeases => etcdserverpb.LeaseLeasesRequest.ty
  | .authEnable => etcdserverpb.AuthEnableRequest.ty
  | .authDisable => etcdserverpb.AuthDisableRequest.ty
  | .authStatus => etcdserverpb.AuthStatusRequest.ty
  | .authenticate _ _ => etcdserverpb.AuthenticateRequest.ty
  | .userAdd _ _ _ => etcdserverpb.AuthUserAddRequest.ty
  | .userGet _ => etcdserverpb.AuthUserGetRequest.ty
  | .userList => etcdserverpb.AuthUserListRequest.ty
  | .userDelete _ => etcdserverpb.AuthUserDeleteRequest.ty
  | .userChangePassword _ _ => etcdserverpb.AuthUserChangePasswordRequest.ty
  | .userGrantRole _ _ => etcdserverpb.AuthUserGrantRoleRequest.ty
  | .userRevokeRole _ _ => etcdserverpb.AuthUserRevokeRoleRequest.ty
  | .roleAdd _ => etcdserverpb.AuthRoleAddRequest.ty
  | .roleGet _ => etcdserverpb.AuthRoleGetRequest.ty
  | .roleList => etcdserverpb.AuthRoleListRequest.ty
  | .roleDelete _ => etcdserverpb.AuthRoleDeleteRequest.ty
  | .roleGrantPermission _ _ => etcdserverpb.AuthRoleGrantPermissionRequest.ty
  | .roleRevokePermission _ _ _ => etcdserverpb.AuthRoleRevokePermissionRequest.ty
  | .memberAdd _ _ => etcdserverpb.MemberAddRequest.ty
  | .memberRemove _ => etcdserverpb.MemberRemoveRequest.ty
  | .memberUpdate _ _ => etcdserverpb.MemberUpdateRequest.ty
  | .memberPromote _ => etcdserverpb.MemberPromoteRequest.ty
  | .memberList _ => etcdserverpb.MemberListRequest.ty
  | .alarmList => etcdserverpb.AlarmRequest.ty
  | .alarmDisarm _ => etcdserverpb.AlarmRequest.ty
  | .alarmActivate _ => etcdserverpb.AlarmRequest.ty

/-- The Go type of a success reply's message. -/
def bodyType : RespBody → go.GoType
  | .range _ _ => etcdserverpb.RangeResponse.ty
  | .put _ _ => etcdserverpb.PutResponse.ty
  | .deleteRange _ _ _ => etcdserverpb.DeleteRangeResponse.ty
  | .txn _ _ _ => etcdserverpb.TxnResponse.ty
  | .compact => etcdserverpb.CompactionResponse.ty
  | .leaseGrant _ _ => etcdserverpb.LeaseGrantResponse.ty
  | .leaseRevoke => etcdserverpb.LeaseRevokeResponse.ty
  | .leaseKeepAlive _ _ => etcdserverpb.LeaseKeepAliveResponse.ty
  | .leaseTimeToLive _ _ _ _ => etcdserverpb.LeaseTimeToLiveResponse.ty
  | .leaseLeases _ => etcdserverpb.LeaseLeasesResponse.ty
  | .authEnable => etcdserverpb.AuthEnableResponse.ty
  | .authDisable => etcdserverpb.AuthDisableResponse.ty
  | .authStatus _ _ => etcdserverpb.AuthStatusResponse.ty
  | .authenticate => etcdserverpb.AuthenticateResponse.ty
  | .userAdd => etcdserverpb.AuthUserAddResponse.ty
  | .userGet _ => etcdserverpb.AuthUserGetResponse.ty
  | .userList _ => etcdserverpb.AuthUserListResponse.ty
  | .userDelete => etcdserverpb.AuthUserDeleteResponse.ty
  | .userChangePassword => etcdserverpb.AuthUserChangePasswordResponse.ty
  | .userGrantRole => etcdserverpb.AuthUserGrantRoleResponse.ty
  | .userRevokeRole => etcdserverpb.AuthUserRevokeRoleResponse.ty
  | .roleAdd => etcdserverpb.AuthRoleAddResponse.ty
  | .roleGet _ => etcdserverpb.AuthRoleGetResponse.ty
  | .roleList _ => etcdserverpb.AuthRoleListResponse.ty
  | .roleDelete => etcdserverpb.AuthRoleDeleteResponse.ty
  | .roleGrantPermission => etcdserverpb.AuthRoleGrantPermissionResponse.ty
  | .roleRevokePermission => etcdserverpb.AuthRoleRevokePermissionResponse.ty
  | .memberAdd _ _ => etcdserverpb.MemberAddResponse.ty
  | .memberRemove _ => etcdserverpb.MemberRemoveResponse.ty
  | .memberUpdate _ => etcdserverpb.MemberUpdateResponse.ty
  | .memberPromote _ => etcdserverpb.MemberPromoteResponse.ty
  | .memberList _ => etcdserverpb.MemberListResponse.ty
  | .alarm _ => etcdserverpb.AlarmResponse.ty

end types

/-! ## The watch messages' relations (integration X: from `Realize.lean`, so that the watch
stream's contract, `ClientV3.watchSpec`, can be stated where the client's watch is) -/

/-- **The content `c` is a `WatchRequest` modelled by `r`** (a create's raw key `""` for `"\x00"`). -/
opaque watchReqHolds (c : Proto.Content) (r : WireWatchReq) : Prop
/-- **The content `c` is a `WatchResponse` modelled by `m`.** -/
opaque watchRespHolds (c : Proto.Content) (m : WireWatchRespM) : Prop
/-- **The content `c` is an `mvccpb.Event` modelled by `e`.** -/
opaque eventHolds (c : Proto.Content) (e : EventM) : Prop

/-! ## 2a's slots -/

/-- (2a's `V3rpc.reqModels`) The content `c` of a request of method `m` models `rq`. -/
def reqModels (_m : GoString) (c : Proto.Content) (rq : Req) : Prop := reqHolds c rq

/-- (2a's `V3rpc.replyModels`) The content `c` of a reply of method `m` carries the success body
`b`: a KV reply through W0's Go-level model (the header's revision the body's), any other through
`bodyHolds`. -/
def replyModels (_m : GoString) (b : RespBody) (c : Proto.Content) : Prop :=
  match b with
  | .range rev a => ∃ m h, rangeRespHolds c m ∧ m.hdr = some h ∧ h.revision = W64 rev ∧ m.ofAns a
  | .put rev prev => ∃ m, putRespHolds c m ∧ m.hdr.revision = W64 rev ∧
      m.prevKv = prev.map KeyValueM.ofKV
  | .deleteRange rev n l => ∃ m, deleteRespHolds c m ∧ m.hdr.revision = W64 rev ∧
      m.deleted = W64 n ∧ m.prevKvs = l.map KeyValueM.ofKV
  | .txn rev ok rs => ∃ m, txnRespHolds c m ∧ m.hdr.revision = W64 rev ∧ m.ofResps ok rs
  | .compact => ∃ m, compactRespHolds c m
  | b => bodyHolds c b

/-- (2a's `V3rpc.chunkModels`) The content `c` of a `RangeStreamResponse` carries the chunk `m`. -/
def chunkModels (c : Proto.Content) (m : RangeRespM) : Prop := chunkHolds c m

/-! ## Merging streamed ranges (`proto.Merge`) -/

/-- A proto3 scalar merged: the source's if set (non-zero). -/
def mergeW (a b : w64) : w64 := if b = W64 0 then a else b

def mergeHeader (h h' : HeaderM) : HeaderM :=
  ⟨mergeW h.clusterId h'.clusterId, mergeW h.memberId h'.memberId, mergeW h.revision h'.revision,
   mergeW h.raftTerm h'.raftTerm, mergeW h.leaderId h'.leaderId⟩

/-- **`proto.Merge` of two `RangeResponse`s**: the key-values appended, the header merged field by
field (taken if the destination has none), `More` or-ed, `Count` the source's if set. -/
def mergeRange (m m' : RangeRespM) : RangeRespM :=
  { hdr := match m.hdr, m'.hdr with
      | h, none => h
      | none, some h' => some h'
      | some h, some h' => some (mergeHeader h h')
    kvs := m.kvs ++ m'.kvs
    more := m.more || m'.more
    count := mergeW m.count m'.count }

/-! ## A transaction reply's nesting (verify-round, A6 F6) -/

mutual
/-- The depth of a `ResponseOp` message holding `m`: a range, put or delete response nests two
levels below it (the response, its header or key-values); a nested transaction's response one
level more than its own operations' (or its header). -/
def respOpDepth : ResponseOpM → Nat
  | .empty => 1
  | .range _ => 3
  | .put _ => 3
  | .deleteRange _ => 3
  | .txn _ _ rs => 2 + max 1 (respOpsDepth rs)
def respOpsDepth : List ResponseOpM → Nat
  | [] => 0
  | r :: rs => max (respOpDepth r) (respOpsDepth rs)
end

/-- The depth of a `TxnResponse` holding `m` (its header, or its operations' responses). -/
def txnRespDepth (m : TxnRespM) : Nat := 1 + max 1 (respOpsDepth m.responses)

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def watch_holds_fun.spec : Prop :=
  (∀ c r r', watchReqHolds c r → watchReqHolds c r' → r = r') ∧
  (∀ c m m', watchRespHolds c m → watchRespHolds c m' → m = m') ∧
  (∀ c e e', eventHolds c e → eventHolds c e' → e = e')

/-- The watch messages are at most three levels deep (a response, its events, their key-values). -/
def watch_holds_depth.spec : Prop :=
  (∀ c r, watchReqHolds c r → Proto.depth c ≤ 2) ∧
  (∀ c m, watchRespHolds c m → Proto.depth c ≤ 3) ∧
  (∀ c e, eventHolds c e → Proto.depth c ≤ 2)

/-- **Each relation is functional in the content.** -/
def holds_fun.spec : Prop :=
  (∀ c rq rq', reqHolds c rq → reqHolds c rq' → rq = rq') ∧
  (∀ c b b', bodyHolds c b → bodyHolds c b' → b = b') ∧
  (∀ c m m', respHeaderHolds c m → respHeaderHolds c m' → m = m') ∧
  (∀ c m m', keyValueHolds c m → keyValueHolds c m' → m = m') ∧
  (∀ c m m', rangeRespHolds c m → rangeRespHolds c m' → m = m') ∧
  (∀ c m m', putRespHolds c m → putRespHolds c m' → m = m') ∧
  (∀ c m m', deleteRespHolds c m → deleteRespHolds c m' → m = m') ∧
  (∀ c m m', responseOpHolds c m → responseOpHolds c m' → m = m') ∧
  (∀ c m m', txnRespHolds c m → txnRespHolds c m' → m = m') ∧
  (∀ c m m', compactRespHolds c m → compactRespHolds c m' → m = m') ∧
  (∀ c m m', compareHolds c m → compareHolds c m' → m = m') ∧
  (∀ c m m', requestOpHolds c m → requestOpHolds c m' → m = m') ∧
  (∀ c m m', chunkHolds c m → chunkHolds c m' → m = m')

/-- **Nesting depth**: a non-transaction message is at most three levels deep (what `proto.Clone`
of a `Compare` and `proto.Merge` of `RangeResponse`s need). -/
def holds_depth.spec : Prop :=
  (∀ c rq, reqHolds c rq → (∀ t, rq ≠ .txn t) → Proto.depth c ≤ 3) ∧
  (∀ c b, bodyHolds c b → Proto.depth c ≤ 3) ∧
  (∀ c m, compareHolds c m → Proto.depth c ≤ 1) ∧
  (∀ c m, rangeRespHolds c m → Proto.depth c ≤ 2) ∧
  (∀ c m, chunkHolds c m → Proto.depth c ≤ 3)

/-- **The replies' nesting** (verify-round, A6 F6: `Grpc.unaryOut` needs each reply's depth below
`Proto.depthMax`): the flat replies are at most two levels deep, a transaction's as its model nests
(`txnRespDepth`: a reply to a transaction of `txnMsgDepth t` is at most one level deeper, the
innermost range's key-values; at `--max-txn-ops = 4999` that is `10000`, which decodes). -/
def holds_depth_resp.spec : Prop :=
  (∀ c m, putRespHolds c m → Proto.depth c ≤ 2) ∧
  (∀ c m, deleteRespHolds c m → Proto.depth c ≤ 2) ∧
  (∀ c m, compactRespHolds c m → Proto.depth c ≤ 2) ∧
  (∀ c m, respHeaderHolds c m → Proto.depth c ≤ 1) ∧
  (∀ c m, keyValueHolds c m → Proto.depth c ≤ 1) ∧
  (∀ c m, responseOpHolds c m → Proto.depth c ≤ respOpDepth m) ∧
  (∀ c m, txnRespHolds c m → Proto.depth c ≤ txnRespDepth m)

/-- **The wire view keeps the models** (verify-round, A6 F2: gRPC delivers `Proto.norm c` of a sent
content `c`, `Clone` copies it). A reply's and an event's models do not distinguish a `nil` field
from an empty one, so `norm` keeps them; a request's range ends do (W0's `endOf`: a non-`nil`
empty end is `"\x00"`), so a request keeps its model when its ends are `nil` or non-empty
(`endsOk`); a client whose request has a non-`nil` empty end (`clientv3.WithRange("")`) is answered
for the key alone, unlike W0's model of it (requested of client-core). -/
def holds_norm.spec : Prop :=
  (∀ c rq, reqHolds c rq → endsOk c → reqHolds (Proto.norm c) rq) ∧
  (∀ c m, compareHolds c m → endsOk c → compareHolds (Proto.norm c) m) ∧
  (∀ c m, requestOpHolds c m → endsOk c → requestOpHolds (Proto.norm c) m) ∧
  (∀ c r, watchReqHolds c r → endsOk c → watchReqHolds (Proto.norm c) r) ∧
  (∀ c b, bodyHolds c b → bodyHolds (Proto.norm c) b) ∧
  (∀ c m, respHeaderHolds c m → respHeaderHolds (Proto.norm c) m) ∧
  (∀ c m, keyValueHolds c m → keyValueHolds (Proto.norm c) m) ∧
  (∀ c m, rangeRespHolds c m → rangeRespHolds (Proto.norm c) m) ∧
  (∀ c m, putRespHolds c m → putRespHolds (Proto.norm c) m) ∧
  (∀ c m, deleteRespHolds c m → deleteRespHolds (Proto.norm c) m) ∧
  (∀ c m, responseOpHolds c m → responseOpHolds (Proto.norm c) m) ∧
  (∀ c m, txnRespHolds c m → txnRespHolds (Proto.norm c) m) ∧
  (∀ c m, compactRespHolds c m → compactRespHolds (Proto.norm c) m) ∧
  (∀ c m, chunkHolds c m → chunkHolds (Proto.norm c) m) ∧
  (∀ c m, watchRespHolds c m → watchRespHolds (Proto.norm c) m) ∧
  (∀ c e, eventHolds c e → eventHolds (Proto.norm c) e)

/-- **`proto.Merge` of two range responses** (2a's `Proto.merge`, at this type). -/
def rangeResp_merge.spec : Prop := ∀ c c' m m',
  rangeRespHolds c m → rangeRespHolds c' m' → rangeRespHolds (Proto.merge c c') (mergeRange m m')

/-! ### Relation laws (W0's predicates) -/

def rangeReqOwn_msgAt.spec : Prop := ∀ p dq r,
  rangeReqOwn (GF := GF) p dq r ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.RangeRequest.ty p dq c ∗ ⌜reqHolds c (.range r)⌝
def putReqOwn_msgAt.spec : Prop := ∀ p dq r,
  putReqOwn (GF := GF) p dq r ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.PutRequest.ty p dq c ∗ ⌜reqHolds c (.put r)⌝
def deleteReqOwn_msgAt.spec : Prop := ∀ p dq r,
  deleteReqOwn (GF := GF) p dq r ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.DeleteRangeRequest.ty p dq c ∗ ⌜reqHolds c (.deleteRange r)⌝
def txnReqOwn_msgAt.spec : Prop := ∀ p dq t,
  txnReqOwn (GF := GF) p dq t ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.TxnRequest.ty p dq c ∗ ⌜reqHolds c (.txn t)⌝
def compactReqOwn_msgAt.spec : Prop := ∀ p dq rev phys,
  compactReqOwn (GF := GF) p dq rev phys ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.CompactionRequest.ty p dq c ∗ ⌜reqHolds c (.compact rev phys)⌝
def compareOwn_msgAt.spec : Prop := ∀ p dq m,
  compareOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.Compare.ty p dq c ∗ ⌜compareHolds c m⌝
def requestOpOwn_msgAt.spec : Prop := ∀ p dq m,
  requestOpOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.RequestOp.ty p dq c ∗ ⌜requestOpHolds c m⌝
def respHeaderOwn_msgAt.spec : Prop := ∀ p dq m,
  respHeaderOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.ResponseHeader.ty p dq c ∗ ⌜respHeaderHolds c m⌝
def keyValueOwn_msgAt.spec : Prop := ∀ p dq m,
  keyValueOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt mvccpb.KeyValue.ty p dq c ∗ ⌜keyValueHolds c m⌝
def rangeRespOwn_msgAt.spec : Prop := ∀ p dq m,
  rangeRespOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.RangeResponse.ty p dq c ∗ ⌜rangeRespHolds c m⌝
def putRespOwn_msgAt.spec : Prop := ∀ p dq m,
  putRespOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.PutResponse.ty p dq c ∗ ⌜putRespHolds c m⌝
def deleteRespOwn_msgAt.spec : Prop := ∀ p dq m,
  deleteRespOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.DeleteRangeResponse.ty p dq c ∗ ⌜deleteRespHolds c m⌝
def responseOpOwn_msgAt.spec : Prop := ∀ p dq m,
  responseOpOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.ResponseOp.ty p dq c ∗ ⌜responseOpHolds c m⌝
def txnRespOwn_msgAt.spec : Prop := ∀ p dq m,
  txnRespOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.TxnResponse.ty p dq c ∗ ⌜txnRespHolds c m⌝
def compactRespOwn_msgAt.spec : Prop := ∀ p dq m,
  compactRespOwn (GF := GF) p dq m ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.CompactionResponse.ty p dq c ∗ ⌜compactRespHolds c m⌝

/-- **A `RangeStreamResponse` carrying a chunk** (verify-round, A6 F8: what
`headerFillingRangeStream.Send` reads, `key.go:84-89`): its `RangeResponse` is a (non-`nil`)
`RangeResponse` message holding the chunk, read and written through W0's `rangeRespOwn`. -/
def chunk_msgAt.spec : Prop := ∀ p dq m,
  (∃ c, Proto.msgAt (GF := GF) etcdserverpb.RangeStreamResponse.ty p dq c ∗ ⌜chunkHolds c m⌝) ⊣⊢
    ∃ rr : Loc, protoRest etcdserverpb.RangeStreamResponse p dq ∗
      p.[etcdserverpb.RangeStreamResponse, go!"RangeResponse"] ↦{dq} rr ∗ rangeRespOwn rr dq m

/-! ### Package initialization: the generated descriptors and enum maps -/

/-- **The KV service's descriptor** (`KV_ServiceDesc`, read-only after init): its unary methods and
its stream with their generated handlers, in the descriptor's order (`rpc_grpc.pb.go`; the
initializer is translated, the handlers' names are those it stores). Verify round (A6
completeness F1): every handler named (was: `RangeStream`'s an unknown `ss`); the untranslated
handlers' specs (`_KV_RangeStream_Handler.spec`, ...) are stated, their proofs wait for 7.4. -/
def kvDesc_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢
    Grpc.serviceDescAt (globalAddr etcdserverpb.KV_ServiceDesc) go!"etcdserverpb.KV"
      [(go!"Range", @! etcdserverpb._KV_Range_Handler), (go!"Put", @! etcdserverpb._KV_Put_Handler),
       (go!"DeleteRange", @! etcdserverpb._KV_DeleteRange_Handler),
       (go!"Txn", @! etcdserverpb._KV_Txn_Handler),
       (go!"Compact", @! etcdserverpb._KV_Compact_Handler)]
      [(go!"RangeStream", @! etcdserverpb._KV_RangeStream_Handler)]

/-- The Watch service's descriptor: one stream, `Watch`. -/
def watchDesc_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢
    Grpc.serviceDescAt (globalAddr etcdserverpb.Watch_ServiceDesc) go!"etcdserverpb.Watch" []
      [(go!"Watch", @! etcdserverpb._Watch_Watch_Handler)]

/-- The Lease service's descriptor. -/
def leaseDesc_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢
    Grpc.serviceDescAt (globalAddr etcdserverpb.Lease_ServiceDesc) go!"etcdserverpb.Lease"
      [(go!"LeaseGrant", @! etcdserverpb._Lease_LeaseGrant_Handler),
       (go!"LeaseRevoke", @! etcdserverpb._Lease_LeaseRevoke_Handler),
       (go!"LeaseTimeToLive", @! etcdserverpb._Lease_LeaseTimeToLive_Handler),
       (go!"LeaseLeases", @! etcdserverpb._Lease_LeaseLeases_Handler)]
      [(go!"LeaseKeepAlive", @! etcdserverpb._Lease_LeaseKeepAlive_Handler)]

/-- The Auth service's descriptor: all seventeen handlers, in the descriptor's order (verify round,
A6 completeness F1: was six named and the rest an unknown `ms'`; eleven are untranslated, their
specs stated, `_Auth_UserGet_Handler.spec`, ...). -/
def authDesc_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢
    Grpc.serviceDescAt (globalAddr etcdserverpb.Auth_ServiceDesc) go!"etcdserverpb.Auth"
      [(go!"AuthEnable", @! etcdserverpb._Auth_AuthEnable_Handler),
       (go!"AuthDisable", @! etcdserverpb._Auth_AuthDisable_Handler),
       (go!"AuthStatus", @! etcdserverpb._Auth_AuthStatus_Handler),
       (go!"Authenticate", @! etcdserverpb._Auth_Authenticate_Handler),
       (go!"UserAdd", @! etcdserverpb._Auth_UserAdd_Handler),
       (go!"UserGet", @! etcdserverpb._Auth_UserGet_Handler),
       (go!"UserList", @! etcdserverpb._Auth_UserList_Handler),
       (go!"UserDelete", @! etcdserverpb._Auth_UserDelete_Handler),
       (go!"UserChangePassword", @! etcdserverpb._Auth_UserChangePassword_Handler),
       (go!"UserGrantRole", @! etcdserverpb._Auth_UserGrantRole_Handler),
       (go!"UserRevokeRole", @! etcdserverpb._Auth_UserRevokeRole_Handler),
       (go!"RoleAdd", @! etcdserverpb._Auth_RoleAdd_Handler),
       (go!"RoleGet", @! etcdserverpb._Auth_RoleGet_Handler),
       (go!"RoleList", @! etcdserverpb._Auth_RoleList_Handler),
       (go!"RoleDelete", @! etcdserverpb._Auth_RoleDelete_Handler),
       (go!"RoleGrantPermission", @! etcdserverpb._Auth_RoleGrantPermission_Handler),
       (go!"RoleRevokePermission", @! etcdserverpb._Auth_RoleRevokePermission_Handler)] []

/-- The Cluster and Maintenance services' descriptors, every handler named, in the descriptors'
order (verify round, A6 completeness F1: were unknown lists; the handlers are untranslated, their
specs stated, `_Cluster_MemberAdd_Handler.spec`, ..., `_Maintenance_Snapshot_Handler.spec`). -/
def otherDescs_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢
    Grpc.serviceDescAt (globalAddr etcdserverpb.Cluster_ServiceDesc) go!"etcdserverpb.Cluster"
      [(go!"MemberAdd", @! etcdserverpb._Cluster_MemberAdd_Handler),
       (go!"MemberRemove", @! etcdserverpb._Cluster_MemberRemove_Handler),
       (go!"MemberUpdate", @! etcdserverpb._Cluster_MemberUpdate_Handler),
       (go!"MemberList", @! etcdserverpb._Cluster_MemberList_Handler),
       (go!"MemberPromote", @! etcdserverpb._Cluster_MemberPromote_Handler)] [] ∗
    Grpc.serviceDescAt (globalAddr etcdserverpb.Maintenance_ServiceDesc) go!"etcdserverpb.Maintenance"
      [(go!"Alarm", @! etcdserverpb._Maintenance_Alarm_Handler),
       (go!"Status", @! etcdserverpb._Maintenance_Status_Handler),
       (go!"Defragment", @! etcdserverpb._Maintenance_Defragment_Handler),
       (go!"Hash", @! etcdserverpb._Maintenance_Hash_Handler),
       (go!"HashKV", @! etcdserverpb._Maintenance_HashKV_Handler),
       (go!"MoveLeader", @! etcdserverpb._Maintenance_MoveLeader_Handler),
       (go!"Downgrade", @! etcdserverpb._Maintenance_Downgrade_Handler)]
      [(go!"Snapshot", @! etcdserverpb._Maintenance_Snapshot_Handler)]

/-- **The sort enums' name maps** (`RangeRequest_SortOrder_name`, `_SortTarget_name`, read-only
after init): their keys are exactly `0..2` and `0..4` (W0's `Op.IsSortOptionValid`). Needs the
two maps translated (`Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`: today names only). -/
def sortNames_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢
    (∃ (mp : GoMap) (m : GMap w32 GoString),
      typedPointsto (globalAddr go!"go.etcd.io/etcd/api/v3/etcdserverpb.RangeRequest_SortOrder_name")
        mp DFrac.discard ∗ ownMap mp DFrac.discard m ∗
      ⌜∀ k : w32, (m !! k).isSome ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝) ∗
    (∃ (mp : GoMap) (m : GMap w32 GoString),
      typedPointsto (globalAddr go!"go.etcd.io/etcd/api/v3/etcdserverpb.RangeRequest_SortTarget_name")
        mp DFrac.discard ∗ ownMap mp DFrac.discard m ∗
      ⌜∀ k : w32, (m !! k).isSome ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝)

/-! ### Decoded range ends (integration X; I5's `endsDecoded`/`opsDecoded`, 3h's to give)

A `RangeEnd` that is a non-`nil` empty slice is read by the auth checks as the key alone and by mvcc
as every key from it on (`nonissues/etcd-auth-empty-range-end-point-check.md`); a request decoded
by protobuf never has one (its content is canonical, `Proto.norm c = c`, and `endsOk_canon`). The
request path's checks take `endsDecoded` as a scope premise; grpc's decoder gives it, and so does
the apply's `Unmarshal`.

**verify-round (A6 F2).** `endsDecoded t p` was an opaque persistent fact keyed by the address,
read against the *current* field (`endsDecoded_range`): a holder could create it from a `nil` end,
rewrite the end to a non-`nil` empty slice and derive `False` (A6-provability F2's counterexample).
It is now **tied to a share of the message**: `∃ dq c, msgAt t p dq c ∗ ⌜endsOk c⌝`, a pure fact
about the content (Go-level since the same round, `Proto/Api.lean`) that the share pins: while it
is held nobody can write the fields, and the laws give it back. It is no longer persistent; it is
at `DFrac.discard` (`endsDecoded_ro`: the apply thread's read-only entries). The arity is unchanged,
so its users' statements (2c's `Range`, `RangeStream`, `Txn`) stand; their proofs hand it back to
nobody (the share is lost with it, which only the handler's `reqBack` notices: any share will do). -/

/-- A canonical content (a decoded message's) has its ends `nil` or non-empty: proto3 never encodes
an empty `bytes` field, and `norm` makes an unset one `nil`. -/
def endsOk_canon.spec : Prop := ∀ c, Proto.norm c = c → endsOk c

/-- A range request whose model's end is not `"\x00"` (W0's `endOf` maps a non-`nil` empty end
to `"\x00"`) has its end `nil` or non-empty: the health checks' requests (a `nil` end). -/
def endsOk_range_intro.spec : Prop := ∀ c (r : RangeReq),
  reqHolds c (.range r) → r.rangeEnd ≠ [W8 0] → endsOk c

/-- **The range ends of the request message `*t` at `p` are `nil` or non-empty**: a share of the
message whose content has `endsOk`. Exclusive (a share), persistent at `DFrac.discard`
(`endsDecoded_ro`). Read through the laws below, which give it back. -/
def endsDecoded (t : go.GoType) (p : Loc) : IProp GF :=
  iprop(∃ (dq : DFrac) (c : Proto.Content), Proto.msgAt t p dq c ∗ ⌜endsOk c⌝)

/-- A decoded (canonical) message's share is one (grpc's `decOk_call`, `srvRecv_recv`; `Unmarshal`). -/
def endsDecoded_of_canon.spec : Prop := ∀ t p dq c,
  Proto.msgAt (GF := GF) t p dq c ∗ ⌜Proto.norm c = c⌝ ⊢ endsDecoded t p

/-- At `DFrac.discard` it is persistent (the apply thread's entries, read-only: apply's provisional
`endsDecoded rt`, `reqMsgAt_endsDecoded`, is this at `TxnRequest`). -/
def endsDecoded_ro.spec : Prop := ∀ t p c,
  Proto.msgAt (GF := GF) t p DFrac.discard c ∗ ⌜endsOk c⌝ ⊢ □ endsDecoded t p

/-- **Every operation of the slice `sl` was decoded** (a share of the slice and of each operation). -/
def opsDecoded (sl : GoSlice) : IProp GF :=
  iprop(∃ (dq : DFrac) (ps : List Loc), sl ↦*{dq} ps ∗
    [∗list] op ∈ ps, endsDecoded etcdserverpb.RequestOp.ty op)

/-- **Every comparison of the slice `sl` was decoded.** -/
def cmpsDecoded (sl : GoSlice) : IProp GF :=
  iprop(∃ (dq : DFrac) (ps : List Loc), sl ↦*{dq} ps ∗
    [∗list] cp ∈ ps, endsDecoded etcdserverpb.Compare.ty cp)

/-- A decoded request's range end is `nil` or non-empty (the field read at any share, given back
with the fact). -/
def endsDecoded_range.spec : Prop := ∀ (p : Loc) (dq : DFrac) (es : GoSlice) (ebs : GoString),
  endsDecoded (GF := GF) etcdserverpb.RangeRequest.ty p ∗
    p.[etcdserverpb.RangeRequest, go!"RangeEnd"] ↦{dq} es ∗ es ↦*□ ebs ⊢
  endsDecoded etcdserverpb.RangeRequest.ty p ∗
    p.[etcdserverpb.RangeRequest, go!"RangeEnd"] ↦{dq} es ∗ ⌜es = slice.nil ∨ ebs ≠ []⌝
def endsDecoded_delete.spec : Prop := ∀ (p : Loc) (dq : DFrac) (es : GoSlice) (ebs : GoString),
  endsDecoded (GF := GF) etcdserverpb.DeleteRangeRequest.ty p ∗
    p.[etcdserverpb.DeleteRangeRequest, go!"RangeEnd"] ↦{dq} es ∗ es ↦*□ ebs ⊢
  endsDecoded etcdserverpb.DeleteRangeRequest.ty p ∗
    p.[etcdserverpb.DeleteRangeRequest, go!"RangeEnd"] ↦{dq} es ∗ ⌜es = slice.nil ∨ ebs ≠ []⌝
def endsDecoded_compare.spec : Prop := ∀ (p : Loc) (dq : DFrac) (es : GoSlice) (ebs : GoString),
  endsDecoded (GF := GF) etcdserverpb.Compare.ty p ∗
    p.[etcdserverpb.Compare, go!"RangeEnd"] ↦{dq} es ∗ es ↦*□ ebs ⊢
  endsDecoded etcdserverpb.Compare.ty p ∗
    p.[etcdserverpb.Compare, go!"RangeEnd"] ↦{dq} es ∗ ⌜es = slice.nil ∨ ebs ≠ []⌝

/-- **The split laws** (I5's request): a decoded transaction's branches and compares are decoded,
and a decoded operation's request (range, delete, nested transaction) is; the parts join back. -/
def endsDecoded_txn.spec : Prop := ∀ (p : Loc) (dq : DFrac) (cs ss fs : GoSlice),
  endsDecoded (GF := GF) etcdserverpb.TxnRequest.ty p ∗
    p.[etcdserverpb.TxnRequest, go!"Compare"] ↦{dq} cs ∗
    p.[etcdserverpb.TxnRequest, go!"Success"] ↦{dq} ss ∗
    p.[etcdserverpb.TxnRequest, go!"Failure"] ↦{dq} fs ⊢
  p.[etcdserverpb.TxnRequest, go!"Compare"] ↦{dq} cs ∗
    p.[etcdserverpb.TxnRequest, go!"Success"] ↦{dq} ss ∗
    p.[etcdserverpb.TxnRequest, go!"Failure"] ↦{dq} fs ∗
    opsDecoded ss ∗ opsDecoded fs ∗ cmpsDecoded cs ∗
    (opsDecoded ss -∗ opsDecoded fs -∗ cmpsDecoded cs -∗ endsDecoded etcdserverpb.TxnRequest.ty p)
def endsDecoded_op.spec : Prop := ∀ (p : Loc) (dq : DFrac) (iv : GoInterface) (w q : Loc),
  endsDecoded (GF := GF) etcdserverpb.RequestOp.ty p ∗ p.[etcdserverpb.RequestOp, go!"Request"] ↦{dq} iv ⊢
  p.[etcdserverpb.RequestOp, go!"Request"] ↦{dq} iv ∗
    ((⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w⌝ -∗
      w.[etcdserverpb.RequestOp_RequestRange, go!"RequestRange"] ↦{dq} q -∗
      w.[etcdserverpb.RequestOp_RequestRange, go!"RequestRange"] ↦{dq} q ∗
        endsDecoded etcdserverpb.RangeRequest.ty q ∗
        (endsDecoded etcdserverpb.RangeRequest.ty q -∗ endsDecoded etcdserverpb.RequestOp.ty p)) ∧
    (⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w⌝ -∗
      w.[etcdserverpb.RequestOp_RequestDeleteRange, go!"RequestDeleteRange"] ↦{dq} q -∗
      w.[etcdserverpb.RequestOp_RequestDeleteRange, go!"RequestDeleteRange"] ↦{dq} q ∗
        endsDecoded etcdserverpb.DeleteRangeRequest.ty q ∗
        (endsDecoded etcdserverpb.DeleteRangeRequest.ty q -∗ endsDecoded etcdserverpb.RequestOp.ty p)) ∧
    (⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w⌝ -∗
      w.[etcdserverpb.RequestOp_RequestTxn, go!"RequestTxn"] ↦{dq} q -∗
      w.[etcdserverpb.RequestOp_RequestTxn, go!"RequestTxn"] ↦{dq} q ∗
        endsDecoded etcdserverpb.TxnRequest.ty q ∗
        (endsDecoded etcdserverpb.TxnRequest.ty q -∗ endsDecoded etcdserverpb.RequestOp.ty p)) ∧
    endsDecoded etcdserverpb.RequestOp.ty p)

end laws

/-! ## The generated client stubs and server handlers (WP forms)

What a generated unary stub does (`kVClient.Put`, ...): build the call options
`append([]CallOption{grpc.StaticMethod()}, opts...)`, allocate the reply holder `new(T)`, and call
`c.cc.Invoke(ctx, method, in, out, cOpts...)`; return `(out, nil)` or `(nil, err)`. What a generated
unary handler does (`_KV_Range_Handler`, ...): allocate the request holder, decode into it (grpc's
`dec`), then call the service's method directly (no interceptor) or through the interceptor with a
`*UnaryServerInfo` and a closure calling the method. A fresh `new(T)` of a message type holds some
content (part of `msgAt`'s realization): the stubs' reply holders and the handlers' request holders
are given to grpc as such. -/

section shapes
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- A stub's connection field: the `*kVClient` (or another stub) `c` holds `cc` (read-only). -/
def stubAt (stubT : Type) (c : Loc) (cc : GoInterface) : IProp GF :=
  iprop(c.[stubT, go!"cc"] ↦□ cc)

/-- **What a unary stub's caller must establish** (WP form): with a fresh reply holder `out` of type
`*repT` (holding some content) and the call options (grpc's `StaticMethod()` option, then the
caller's), the connection's `Invoke` of method `m` on the request `in` and `out`, whose result the
stub returns. -/
def unaryStubWP (cc : GoInterface) (m : val) (reqT repT : go.GoType) (ctx : GoInterface) (q : Loc)
    (os : List GoInterface) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∀ (out : Loc) (c0 : Proto.Content) (cOpts : GoSlice) (sm : GoInterface),
    Proto.msgAt repT out (DFrac.own 1) c0 -∗ Grpc.callOptOk sm -∗ cOpts ↦* (sm :: os) -∗
    WP (App (App (App (App (App (Val (cc @!! google_golang_org.grpc.ClientConnInterface.ty @!! go!"Invoke"))
        (Val #ctx)) (Val m)) (Val #(Proto.msgVal reqT q))) (Val #(Proto.msgVal repT out)))
        (Val #cOpts))
      {{ v, ∃ err : GoInterface, ⌜v = #err⌝ ∗
          Ψ (PairV #(if decide (err = GoInterface.nil) then out else null) #err) }})

/-- **A unary handler's body after decoding** (WP form): the service's method `meth` of `srv`
(after the type assertion to the service interface `svcT`) on the decoded request `q`, directly
(`ic` the nil function) or through the interceptor `ic` with a fresh `*UnaryServerInfo` (the
service value and the method's full name `full`) and a continuation that calls the method on a
request of type `*reqT`. The method's `(*repT, error)` is returned as `(any, error)`. -/
def handlerBodyWP (srv : GoInterfaceOk) (meth : GoString) (reqT repT : go.GoType) (full : GoString)
    (ctx : GoInterface) (q : Loc) (ic : GoFunc) (Ψ : val → IProp GF) : IProp GF :=
  let f : val := #(methods srv.ty meth srv.v)
  let ret (Ψ' : val → IProp GF) : val → IProp GF := fun v =>
    iprop(∃ (resp : Loc) (err : GoInterface), ⌜v = PairV #resp #err⌝ ∗
      Ψ' (PairV #(Proto.msgVal repT resp) #err))
  if ic = func.nil then
    iprop(WP (App (App (Val f) (Val #ctx)) (Val #q)) {{ ret Ψ }})
  else
    iprop(∀ (info : Loc) (h : val),
      info ↦ (google_golang_org.grpc.UnaryServerInfo.mk (GoInterface.ok srv) full) -∗
      (□ ∀ (ctx' : GoInterface) (q' : Loc) (Ψ' : val → IProp GF),
        WP (App (App (Val f) (Val #ctx')) (Val #q')) {{ ret Ψ' }} -∗
        WP (App (App (Val h) (Val #ctx')) (Val #(Proto.msgVal reqT q'))) {{ Ψ' }}) -∗
      WP (App (App (App (App (Val #ic) (Val #ctx)) (Val #(Proto.msgVal reqT q))) (Val #info))
        (Val h)) {{ Ψ }})

/-- The interface type `RegisterKVServer` (and the other registrations) asserts the service value
against (`interface{ testEmbeddedByValue() }`: a service embedding `Unimplemented*Server` by
pointer); etcd's service values do not have the method. -/
def embedTestTy : go.GoType :=
  go.GoType.InterfaceType [go.InterfaceElem.MethodElem
    go!"go.etcd.io/etcd/api/v3/etcdserverpb.testEmbeddedByValue" (go.signature.Signature [] false [])]

/-- **What a streaming stub's caller must establish** (WP form): with the call options, the
connection's `NewStream` of the service's stream descriptor `sd` and method `m`; on success the
stub wraps the stream in a fresh `*grpc.GenericClientStream[Req, Res]` (returned as the stream
interface), on an error it returns a `nil` stream. -/
def streamStubWP {Req Res : Type} [TypedPointsto (GF := GF) (google_golang_org.grpc.GenericClientStream Req Res)]
    (cc : GoInterface) (sd : Loc) (m : val) (reqT repT : go.GoType) (ctx : GoInterface)
    (os : List GoInterface) (Ψ : val → IProp GF) : IProp GF :=
  iprop(∀ (cOpts : GoSlice) (sm : GoInterface),
    Grpc.callOptOk sm -∗ cOpts ↦* (sm :: os) -∗
    WP (App (App (App (App (Val (cc @!! google_golang_org.grpc.ClientConnInterface.ty @!! go!"NewStream"))
        (Val #ctx)) (Val #sd)) (Val m)) (Val #cOpts))
      {{ v, ∃ (st err : GoInterface), ⌜v = PairV #st #err⌝ ∗
          ((⌜err ≠ GoInterface.nil⌝ -∗ Ψ (PairV #GoInterface.nil #err)) ∧
           (⌜err = GoInterface.nil⌝ -∗ ∀ x : Loc,
              x ↦ (google_golang_org.grpc.GenericClientStream.mk st : google_golang_org.grpc.GenericClientStream Req Res) -∗
              Ψ (PairV #(interface.mkOk (go.GoType.PointerType
                (google_golang_org.grpc.GenericClientStream.ty reqT repT)) #x) #GoInterface.nil))) }})

end shapes

section initlaws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The streaming services' stream descriptors are readable** (the stubs pass
`&Watch_ServiceDesc.Streams[0]`, `&Lease_ServiceDesc.Streams[0]`, and (verify-round, the new
`kVClient.RangeStream`, `maintenanceClient.Snapshot` stubs) `&KV_ServiceDesc.Streams[0]`,
`&Maintenance_ServiceDesc.Streams[0]` to `NewStream`). -/
def descStreams_init.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ⊢
    (∃ (sl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
      (globalAddr etcdserverpb.Watch_ServiceDesc).[google_golang_org.grpc.ServiceDesc, go!"Streams"] ↦□ sl ∗
      sl ↦*□ sds ∗ ⌜1 ≤ sds.length⌝) ∗
    (∃ (sl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
      (globalAddr etcdserverpb.Lease_ServiceDesc).[google_golang_org.grpc.ServiceDesc, go!"Streams"] ↦□ sl ∗
      sl ↦*□ sds ∗ ⌜1 ≤ sds.length⌝) ∗
    (∃ (sl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
      (globalAddr etcdserverpb.KV_ServiceDesc).[google_golang_org.grpc.ServiceDesc, go!"Streams"] ↦□ sl ∗
      sl ↦*□ sds ∗ ⌜1 ≤ sds.length⌝) ∗
    (∃ (sl : GoSlice) (sds : List google_golang_org.grpc.StreamDesc),
      (globalAddr etcdserverpb.Maintenance_ServiceDesc).[google_golang_org.grpc.ServiceDesc, go!"Streams"] ↦□ sl ∗
      sl ↦*□ sds ∗ ⌜1 ≤ sds.length⌝)

end initlaws

/-! ## The raft request (`InternalRaftRequest`): moved down from 2c (round 1, F4)

The payload of every write's raft entry: 2c builds it (`raftRequest`), marshals it and proposes the
bytes; 2d's apply decodes them. The model `IrrBody` was 2c's (`ApiReq.lean`); it is the message's
content and lives with the message (2c keeps the semantics: `IrrBody.fires`, `irrStep`). -/

/-- **An internal request's model** (2c's `IrrBody`, moved). -/
inductive IrrBody where
  /-- a client request (KV writes, compactions, lease grants and revocations, auth, alarm list
  and disarm) -/
  | req (rq : Req)
  /-- an alarm raised (`AlarmRequest_ACTIVATE`) -/
  | alarmActivate (al : Alarm)
  /-- a member's attributes published (`ClusterMemberAttrSet`) -/
  | publish (id : Nat) (name : GoString) (urls : List GoString)
  /-- a token assigned to user `name` (`InternalAuthenticateRequest`: `Name`, `SimpleToken`; Go does
  not propose the password, `v3_server.go:872`) -/
  | authToken (name : GoString)
  /-- no observable effect: a lease checkpoint, the cluster version, the downgrade info -/
  | noop

/-- The request revokes a lease (its `LeaseRevoke` field set: `isPriorityRequest`). -/
def IrrBody.isRevoke : IrrBody → Bool
  | .req (.leaseRevoke _) => true
  | _ => false

-- The protobuf nesting depth of a `RequestOp` (2c's, moved).
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

/-- The protobuf nesting depth of a `TxnRequest`'s messages (2c's, moved). -/
def txnMsgDepth (t : TxnReq) : Nat :=
  1 + max (if t.compare = [] then 0 else 1) (max (opsMsgDepth t.success) (opsMsgDepth t.failure))

/-- **An internal request every member's apply can decode** (2c's, moved): a transaction at most
`9999` messages deep below the `InternalRaftRequest`. -/
def IrrBody.depthOk : IrrBody → Prop
  | .req (.txn t) => txnMsgDepth t + 1 ≤ 10000
  | _ => True

/-- `RequestHeader`: the proposal's id and the proposer's user and auth revision. -/
structure IrrHeader where
  id : w64
  username : GoString
  authRevision : w64

/-- **The content `c` is an `InternalRaftRequest` asking `ir`** (exactly `ir`'s field set; the
`Header` not considered). -/
opaque irrHolds (c : Proto.Content) (ir : IrrBody) : Prop
/-- The content's `Header` (`none`: unset) and `ID` (`0`). -/
opaque irrHeaderHolds (c : Proto.Content) (h : Option IrrHeader) : Prop
/-- **The content `c` is an `AlarmRequest` asking `ir`** (`GET`: `.req .alarmList`;
`DEACTIVATE`: `.req (.alarmDisarm al)`; `ACTIVATE`: `.alarmActivate al`). -/
opaque alarmReqHolds (c : Proto.Content) (ir : IrrBody) : Prop
/-- Every `string` field of the request is valid UTF-8 (user, role, member names, passwords,
URLs): what `proto.Marshal` checks (proto3). -/
opaque IrrBody.utf8Ok : IrrBody → Prop

section irr
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **The client request a writer lends into an `InternalRaftRequest`** (integration X, for 2c's
writers: `&pb.InternalRaftRequest{Put: r}`): the requests a client proposes through a field of their
own (not `Range`, `Authenticate`, the member and lease-read requests: those are not proposed this
way). -/
def irrCarries : Req → Bool
  | .put _ => true
  | .deleteRange _ => true
  | .txn _ => true
  | .compact _ _ => true
  | .leaseGrant _ _ => true
  | .leaseRevoke _ => true
  | .authEnable => true
  | .authDisable => true
  | .authStatus => true
  | .userAdd _ _ _ => true
  | .userDelete _ => true
  | .userGet _ => true
  | .userChangePassword _ _ => true
  | .userGrantRole _ _ => true
  | .userRevokeRole _ _ => true
  | .userList => true
  | .roleList => true
  | .roleAdd _ => true
  | .roleDelete _ => true
  | .roleGet _ => true
  | .roleGrantPermission _ _ => true
  | .roleRevokePermission _ _ _ => true
  | _ => false

/-- **The message type and content relation of the inner request of `ir`**: a carried client
request's (`reqType`, `reqHolds`), an alarm's (`AlarmRequest`, `alarmReqHolds`); `none` for the
server's own (`publish`, `authToken`, `noop`: built owned). -/
def irrInner : IrrBody → Option (go.GoType × (Proto.Content → Prop))
  | .req .alarmList => some (etcdserverpb.AlarmRequest.ty, fun c => alarmReqHolds c (.req .alarmList))
  | .req (.alarmDisarm al) =>
      some (etcdserverpb.AlarmRequest.ty, fun c => alarmReqHolds c (.req (.alarmDisarm al)))
  | .req rq => if irrCarries rq then some (reqType rq, fun c => reqHolds c rq) else none
  | .alarmActivate al =>
      some (etcdserverpb.AlarmRequest.ty, fun c => alarmReqHolds c (.alarmActivate al))
  | _ => none

/-- **The struct a writer builds around the inner request at `q`** (`&pb.InternalRaftRequest{F: q}`,
the field `F` of `ir`'s kind; every other field zero). -/
def irrLit : IrrBody → Loc → etcdserverpb.InternalRaftRequest
  | .req (.put _), q => { zero_val etcdserverpb.InternalRaftRequest with Put' := q }
  | .req (.deleteRange _), q => { zero_val etcdserverpb.InternalRaftRequest with DeleteRange' := q }
  | .req (.txn _), q => { zero_val etcdserverpb.InternalRaftRequest with Txn' := q }
  | .req (.compact _ _), q => { zero_val etcdserverpb.InternalRaftRequest with Compaction' := q }
  | .req (.leaseGrant _ _), q => { zero_val etcdserverpb.InternalRaftRequest with LeaseGrant' := q }
  | .req (.leaseRevoke _), q => { zero_val etcdserverpb.InternalRaftRequest with LeaseRevoke' := q }
  | .req (.authEnable), q => { zero_val etcdserverpb.InternalRaftRequest with AuthEnable' := q }
  | .req (.authDisable), q => { zero_val etcdserverpb.InternalRaftRequest with AuthDisable' := q }
  | .req (.authStatus), q => { zero_val etcdserverpb.InternalRaftRequest with AuthStatus' := q }
  | .req (.userAdd _ _ _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthUserAdd' := q }
  | .req (.userDelete _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthUserDelete' := q }
  | .req (.userGet _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthUserGet' := q }
  | .req (.userChangePassword _ _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthUserChangePassword' := q }
  | .req (.userGrantRole _ _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthUserGrantRole' := q }
  | .req (.userRevokeRole _ _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthUserRevokeRole' := q }
  | .req (.userList), q => { zero_val etcdserverpb.InternalRaftRequest with AuthUserList' := q }
  | .req (.roleList), q => { zero_val etcdserverpb.InternalRaftRequest with AuthRoleList' := q }
  | .req (.roleAdd _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthRoleAdd' := q }
  | .req (.roleDelete _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthRoleDelete' := q }
  | .req (.roleGet _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthRoleGet' := q }
  | .req (.roleGrantPermission _ _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthRoleGrantPermission' := q }
  | .req (.roleRevokePermission _ _ _), q => { zero_val etcdserverpb.InternalRaftRequest with AuthRoleRevokePermission' := q }
  | .req (.alarmList), q => { zero_val etcdserverpb.InternalRaftRequest with Alarm' := q }
  | .req (.alarmDisarm _), q => { zero_val etcdserverpb.InternalRaftRequest with Alarm' := q }
  | .alarmActivate _, q => { zero_val etcdserverpb.InternalRaftRequest with Alarm' := q }
  | _, _ => zero_val etcdserverpb.InternalRaftRequest

/-- **An `*InternalRaftRequest` asking `ir`, with header `h`**: the outer struct owned, the inner
request message (`irrInner`) at the fraction `dq` (a writer wraps the request its caller lent it,
`irrOwn_wrap`, and takes it back, `irrOwn_unwrap`; integration X, I4's `irrOwn p dq ir` made 3h's);
at `dq = 1` an owned message (`irrOwnH_msgAt`). -/
opaque irrOwnH [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (ir : IrrBody) (h : Option IrrHeader) : IProp GF := iprop(True)

/-- 2c's `irrOwn` (header and `ID` unset). -/
def irrOwn (p : Loc) (dq : DFrac) (ir : IrrBody) : IProp GF := irrOwnH p dq ir none

/-- **`p`'s inner request is the message at `q`** (persistent; given by `irrOwn_wrap`). -/
opaque irrInnerAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p q : Loc) : IProp GF := iprop(True)

/-- **An `*AlarmRequest` asking `ir`** (2c's `alarmReqOwn`). -/
opaque alarmReqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (ir : IrrBody) : IProp GF := iprop(True)

/-- **`r` is `nil` (`b = false`) or a read-only `*InternalRaftRequest` whose `LeaseRevoke` is set
exactly when `b`** (2e's `irrIsRevoke`). Persistent. -/
def irrIsRevoke (r : Loc) (b : Bool) : IProp GF :=
  iprop(⌜r = null ∧ b = false⌝ ∨
    ∃ lr : Loc, r.[etcdserverpb.InternalRaftRequest, go!"LeaseRevoke"] ↦□ lr ∗ ⌜b = decide (lr ≠ null)⌝)

/-- A `*RequestHeader`'s fields (owned). -/
def reqHeaderAt (hp : Loc) (h : IrrHeader) : IProp GF :=
  iprop(protoRest etcdserverpb.RequestHeader hp (DFrac.own 1) ∗
    hp.[etcdserverpb.RequestHeader, go!"ID"] ↦ h.id ∗
    hp.[etcdserverpb.RequestHeader, go!"Username"] ↦ h.username ∗
    hp.[etcdserverpb.RequestHeader, go!"AuthRevision"] ↦ h.authRevision)

def irrOwnH_msgAt.spec : Prop := ∀ p ir h,
  irrOwnH (GF := GF) p (DFrac.own 1) ir h ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.InternalRaftRequest.ty p (DFrac.own 1) c ∗
      ⌜irrHolds c ir ∧ irrHeaderHolds c h⌝

/-- **Reading the whole message** (`Marshal`) at a lent fraction: a fraction of it holds a content
asking `ir`. -/
def irrOwnH_read.spec : Prop := ∀ p dq ir h,
  irrOwnH (GF := GF) p dq ir h ⊢
    ∃ (dq' : DFrac) (c : Proto.Content), Proto.msgAt etcdserverpb.InternalRaftRequest.ty p dq' c ∗
      ⌜irrHolds c ir ∧ irrHeaderHolds c h⌝ ∗
      (Proto.msgAt etcdserverpb.InternalRaftRequest.ty p dq' c -∗ irrOwnH p dq ir h)

/-- **Wrapping a lent request** (`&pb.InternalRaftRequest{F: q}`, integration X). -/
def irrOwn_wrap.spec : Prop := ∀ (p q : Loc) (dq : DFrac) (ir : IrrBody) (t : go.GoType)
    (H : Proto.Content → Prop) (c : Proto.Content),
  irrInner ir = some (t, H) →
  p ↦ irrLit ir q ∗ Proto.msgAt t q dq c ∗ ⌜H c⌝ ⊢ |==> irrOwn (GF := GF) p dq ir ∗ irrInnerAt p q

/-- **Taking the lent request back** (the outer struct dropped, whatever its header). -/
def irrOwn_unwrap.spec : Prop := ∀ (p q : Loc) (dq : DFrac) (ir : IrrBody) (h : Option IrrHeader)
    (t : go.GoType) (H : Proto.Content → Prop),
  irrInner ir = some (t, H) →
  irrOwnH (GF := GF) p dq ir h ∗ irrInnerAt p q ⊢ ∃ c, Proto.msgAt t q dq c ∗ ⌜H c⌝

def irrInnerAt_persistent.spec : Prop := ∀ p q, Persistent (irrInnerAt (GF := GF) p q)

def alarmReqOwn_msgAt.spec : Prop := ∀ p dq ir,
  alarmReqOwn (GF := GF) p dq ir ⊣⊢
    ∃ c, Proto.msgAt etcdserverpb.AlarmRequest.ty p dq c ∗ ⌜alarmReqHolds c ir⌝

/-- **Setting the header** (`processInternalRaftRequestOnce`: `r.Header = &pb.RequestHeader{...}`,
then `r.Header.Username`/`AuthRevision` written in place). -/
def irrOwn_setHeader.spec : Prop := ∀ (p : Loc) (dq : DFrac) (ir : IrrBody),
  irrOwnH (GF := GF) p dq ir none ⊢
    p.[etcdserverpb.InternalRaftRequest, go!"Header"] ↦ (null : Loc) ∗
    ∀ (hp : Loc) (h : IrrHeader), p.[etcdserverpb.InternalRaftRequest, go!"Header"] ↦ hp -∗
      reqHeaderAt hp h -∗ irrOwnH p dq ir (some h)

/-- **Reading the header back** (`r.Header.ID` after marshaling). -/
def irrOwnH_header.spec : Prop := ∀ (p : Loc) (dq : DFrac) (ir : IrrBody) (h : IrrHeader),
  irrOwnH (GF := GF) p dq ir (some h) ⊢
    ∃ hp : Loc, p.[etcdserverpb.InternalRaftRequest, go!"Header"] ↦ hp ∗ reqHeaderAt hp h ∗
      (p.[etcdserverpb.InternalRaftRequest, go!"Header"] ↦ hp -∗ reqHeaderAt hp h -∗
        irrOwnH p dq ir (some h))

/-- **What `proto.Marshal` needs of a raft request**: the depth (`depthOk`), and `marshalOk` exactly
for valid UTF-8 strings. (The encoded size is the server's bound: `--max-request-bytes` is checked
after marshaling, so `fits` comes from the request having fit gRPC: 2a's `msgsFit`, a premise of
2c's.) -/
def irr_content.spec : Prop := ∀ (c : Proto.Content) (ir : IrrBody),
  irrHolds c ir → (ir.depthOk → Proto.depth c < Proto.depthMax) ∧ (Proto.marshalOk c ↔ ir.utf8Ok)

def irr_holds_fun.spec : Prop :=
  (∀ c ir ir', irrHolds c ir → irrHolds c ir' → ir = ir') ∧
  (∀ c h h', irrHeaderHolds c h → irrHeaderHolds c h' → h = h') ∧
  (∀ c ir ir', alarmReqHolds c ir → alarmReqHolds c ir' → ir = ir')

/-- **A read-only raft request answers `isPriorityRequest`** (2e's `irrIsRevoke`; the apply's decoded
request, persisted). -/
def irrIsRevoke_intro.spec : Prop := ∀ (p : Loc) (c : Proto.Content) (ir : IrrBody),
  Proto.msgAt (GF := GF) etcdserverpb.InternalRaftRequest.ty p DFrac.discard c ∗ ⌜irrHolds c ir⌝ ⊢
    irrIsRevoke p ir.isRevoke

/-! ## Merge destinations (round 1, F1)

`proto.Merge` writes its destination in place: it merges into set submessages and appends to
repeated fields, into their spare capacity. So a message may be merged into only if its holder owns
all of that: **no raftpb predicate and no W0 predicate gives it** (their submessages or slices are
shared read-only, or held without capacity: a `MsgApp`'s entries, a snapshot's conf state, a
`RangeResponse`'s `Kvs`). The one destination etcd uses is the client's streamed-range accumulator
(`GetStreamToGetResponse`: `&pb.RangeResponse{}`, then `Merge` per chunk): `rangeRespDst`. -/

-- (integration I3) 3h's provisional `mergeDstOk t p c` is 2a's `Proto.mergeDst t p c` (which holds
-- the message's `msgAt` too): `rangeRespDst_msgAt` is stated over it.

/-- **A `RangeResponse` merge destination** holding `m`: owned, its `Kvs` slice with its capacity,
its header and key-values owned. -/
opaque rangeRespDst [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (m : RangeRespM) : IProp GF := iprop(True)

/-- A fresh `&pb.RangeResponse{}` is an (empty) destination. -/
def rangeRespDst_fresh.spec : Prop := ∀ (p : Loc),
  typedPointsto p (zero_val etcdserverpb.RangeResponse) (DFrac.own 1) ⊢
    rangeRespDst (GF := GF) p ⟨none, [], false, W64 0⟩

/-- A destination is 2a's merge destination (`Proto.mergeDst`: what `Merge` takes and returns) of its content. -/
def rangeRespDst_msgAt.spec : Prop := ∀ (p : Loc) (m : RangeRespM),
  rangeRespDst (GF := GF) p m ⊣⊢
    ∃ c, Proto.mergeDst etcdserverpb.RangeResponse.ty p c ∗ ⌜rangeRespHolds c m⌝

/-- A destination is, forgetting the capacity, an owned reply (the client returns it). -/
def rangeRespDst_own.spec : Prop := ∀ (p : Loc) (m : RangeRespM),
  rangeRespDst (GF := GF) p m ⊢ rangeRespOwn p (DFrac.own 1) m

/-- **The lease replies' header field**, at any content (round 1, second tier 1: the `GetHeader`
getters' bodies read it; an assumption of `msgAt`'s realization at these types, stated). -/
def leaseResp_header.spec : Prop :=
  (∀ (p : Loc) (dq : DFrac) (c : Proto.Content),
    Proto.msgAt (GF := GF) etcdserverpb.LeaseGrantResponse.ty p dq c ⊢
      ∃ (h : Loc) (ho : Option HeaderM), p.[etcdserverpb.LeaseGrantResponse, go!"Header"] ↦{dq} h ∗
        optOwn respHeaderOwn h dq ho ∗
        (p.[etcdserverpb.LeaseGrantResponse, go!"Header"] ↦{dq} h -∗ optOwn respHeaderOwn h dq ho -∗
          Proto.msgAt etcdserverpb.LeaseGrantResponse.ty p dq c)) ∧
  (∀ (p : Loc) (dq : DFrac) (c : Proto.Content),
    Proto.msgAt (GF := GF) etcdserverpb.LeaseKeepAliveResponse.ty p dq c ⊢
      ∃ (h : Loc) (ho : Option HeaderM), p.[etcdserverpb.LeaseKeepAliveResponse, go!"Header"] ↦{dq} h ∗
        optOwn respHeaderOwn h dq ho ∗
        (p.[etcdserverpb.LeaseKeepAliveResponse, go!"Header"] ↦{dq} h -∗ optOwn respHeaderOwn h dq ho -∗
          Proto.msgAt etcdserverpb.LeaseKeepAliveResponse.ty p dq c)) ∧
  (∀ (p : Loc) (dq : DFrac) (c : Proto.Content),
    Proto.msgAt (GF := GF) etcdserverpb.LeaseTimeToLiveResponse.ty p dq c ⊢
      ∃ (h : Loc) (ho : Option HeaderM), p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Header"] ↦{dq} h ∗
        optOwn respHeaderOwn h dq ho ∗
        (p.[etcdserverpb.LeaseTimeToLiveResponse, go!"Header"] ↦{dq} h -∗ optOwn respHeaderOwn h dq ho -∗
          Proto.msgAt etcdserverpb.LeaseTimeToLiveResponse.ty p dq c)) ∧
  (∀ (p : Loc) (dq : DFrac) (c : Proto.Content),
    Proto.msgAt (GF := GF) etcdserverpb.LeaseLeasesResponse.ty p dq c ⊢
      ∃ (h : Loc) (ho : Option HeaderM), p.[etcdserverpb.LeaseLeasesResponse, go!"Header"] ↦{dq} h ∗
        optOwn respHeaderOwn h dq ho ∗
        (p.[etcdserverpb.LeaseLeasesResponse, go!"Header"] ↦{dq} h -∗ optOwn respHeaderOwn h dq ho -∗
          Proto.msgAt etcdserverpb.LeaseLeasesResponse.ty p dq c))

end irr

end EtcdServerPb
end EtcdGrove
end Perennial
