/-
# The v3 API's messages as Go values (batch W0, the anchor)

The KV messages a client and a member exchange (`etcdserverpb`'s requests and responses, `mvccpb`'s
`KeyValue`), as heap resources over models: what a client's spec hands to the gRPC call it makes,
and what a reply gives back. Shared by the client (`client/v3`), the gRPC boundary
(`notes/specs-only/req/google_golang_org_grpc.md`) and the server batches that build the replies
(2a, 2c, 3b); the generated getters of these messages (`ResponseOp.GetResponseRange`, ...) and the
protobuf plumbing under them are batch 3h's (`req/go_etcd_io_etcd_api_v3_etcdserverpb.md`), which
also realizes the predicates below from its own message vocabulary.

**Ownership.** Each message predicate `xOwn p dq m` owns the message struct at `p` with the
fraction `dq` (full ownership, `DFrac.own 1`, from a reply; any fraction, `DFrac.discard` once a
client persists it) and the messages it points to, at the same `dq`; the contents of every byte
slice it points to are read-only (`↦*□`: a request is built from a client's read-only bytes, a reply
is never written byte-wise by the clients). The unfold law of each (`<msg>Own_unfold`) is the
message's struct field by field, so that a client reads (and, at `own 1`, writes) its fields as
Go does; `protoRest t p dq` is the protobuf bookkeeping (`state`, `sizeCache`, `unknownFields`),
opaque, which no client touches (its intro law for a freshly allocated message is `protoRest_zero`;
`protoRest_persist` makes it read-only, so that a message a client built can be shared).

**Models.** Requests are `Model.lean`'s (`RangeReq`, `PutReq`, ...: their `int64` fields as `Int`,
read through `W64`); replies are modelled at the Go level (`HeaderM`, `KeyValueM`, ... with `w64`
fields), and `RespM.ofBody` relates a reply to `Model.lean`'s answer.

The predicates are opaque: their only meaning is their unfold laws, which are obligations of their
realization (3h).

**The wire view** (second pass, grpc-v3rpc's `Proto.norm`): a message crosses gRPC, `proto.Clone`
or a `Marshal`/`Unmarshal` round trip as `Proto.norm c` of its content `c` (every proto3-unset field
at its zero Go value). W0 defines no relation over `Proto.Content`: 3h realizes each predicate here
through its own `*Holds` relation, which survives `norm` (3h's `holds_norm`): the reply and event
relations always, the request relations (`rangeReqOwn`, `deleteReqOwn`, `compareOwn`,
`requestOpOwn`, `txnReqOwn`) only under `endsOk c` (no non-`nil` empty range end, which `endOf`
reads as `[0]` and the wire as `[]`). The client never builds such an end (`ClientV3.OpM.emptyEnd`,
`Cmp.WithRange`'s `e ≠ []`), so the request a member decodes has the model the client sent. The
request predicates carry it (re-review NF1/NF2): `rangeReqOwn_unfold`, `deleteReqOwn_unfold` and
`compareOwn_unfold` (hence `requestOpOwn`, `txnReqOwn`) state `es = slice.nil ∨ ebs ≠ []` of the
range end, so 3h realizes them as `∃ c, msgAt ∗ ⌜…Holds c m ∧ endsOk c⌝` and grpc's `unaryArgs_msgAt`
gets `endsOk`; a clone (`norm c`) keeps the model.

**Watch messages** (batch 1b's models, moved here at integration so that the client, the gRPC watch
server (2b) and the messages' realization (3h) share them without the client's vocabulary):
`WatchReq` (a watch as the member reads it), `EventM`, `WireWatchReq`, `WireWatchRespM`,
`HeaderM.zero`; `eventOwn`, `watchReqOwn`, `wireWatchRespOwn` (the latter two unfolded by 2b's
`watchReqOwn_unfold`, `wireWatchRespOwn_unfold`). What a watch's responses mean (`watchStep`,
`wireStep`) stays the client's (`client/v3/ApiWatch.lean`).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.Model
public import GeneratedProof.go_etcd_io.etcd.api.v3.etcdserverpb
public import GeneratedProof.go_etcd_io.etcd.api.v3.mvccpb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdWire

open Iris Iris.BI EtcdModel
open go_etcd_io.etcd.api.v3

/-! ## Reply models (Go level) -/

/-- `etcdserverpb.ResponseHeader`. -/
structure HeaderM where
  clusterId : w64
  memberId : w64
  revision : w64
  raftTerm : w64
  leaderId : w64

/-- `mvccpb.KeyValue`. -/
structure KeyValueM where
  key : GoString
  createRevision : w64
  modRevision : w64
  version : w64
  value : GoString
  lease : w64

def KeyValueM.ofKV (kv : KV) : KeyValueM :=
  { key := kv.key, createRevision := W64 kv.createRev, modRevision := W64 kv.modRev,
    version := W64 kv.version, value := kv.value, lease := W64 kv.lease }

/-- `etcdserverpb.RangeResponse` (`clientv3.GetResponse`). Its header may be `nil`: a streamed range's
chunks but the last carry none (`EtcdServer.RangeStream`); a unary reply always has one. -/
structure RangeRespM where
  hdr : Option HeaderM
  kvs : List KeyValueM
  more : Bool
  count : w64

/-- `etcdserverpb.PutResponse` (`clientv3.PutResponse`). -/
structure PutRespM where
  hdr : HeaderM
  prevKv : Option KeyValueM

/-- `etcdserverpb.DeleteRangeResponse` (`clientv3.DeleteResponse`). -/
structure DeleteRespM where
  hdr : HeaderM
  deleted : w64
  prevKvs : List KeyValueM

/-- `etcdserverpb.ResponseOp` (and, in `txn`, a nested `TxnResponse`). -/
inductive ResponseOpM where
  | empty
  | range (m : RangeRespM)
  | put (m : PutRespM)
  | deleteRange (m : DeleteRespM)
  | txn (hdr : HeaderM) (succeeded : Bool) (responses : List ResponseOpM)

/-- `etcdserverpb.TxnResponse` (`clientv3.TxnResponse`). -/
structure TxnRespM where
  hdr : HeaderM
  succeeded : Bool
  responses : List ResponseOpM

/-- `etcdserverpb.CompactionResponse` (`clientv3.CompactResponse`). -/
structure CompactRespM where
  hdr : HeaderM

/-! ## Watch messages (moved here from `client/v3/ApiWatch.lean`, batch 1b) -/

/-- **A watch request**: what it delivers. `range` as the member reads it (an empty key is
`"\x00"`, `v3rpc/watch.go`); the filters drop puts (`NOPUT`) or deletes (`NODELETE`). -/
structure WatchReq where
  range : KeyRange
  prevKV : Bool
  filterPut : Bool
  filterDelete : Bool
  progressNotify : Bool
  createdNotify : Bool
  fragment : Bool

/-- **An `mvccpb.Event`**: `Type` (`DELETE` iff `del`), `Kv`, `PrevKv` (`none`: `nil`). -/
structure EventM where
  del : Bool
  kv : KeyValueM
  prevKv : Option KeyValueM

/-- **A `pb.WatchRequest`**: a create (the watch, its start revision as sent: the client resumes
from its position), a cancel of a watch id, a progress request. -/
inductive WireWatchReq where
  | create (w : WatchReq) (start : Int)
  | cancel (id : Int)
  | progress

/-- The creates among the requests, in order. -/
def WireWatchReq.creates (ss : List WireWatchReq) : List (WatchReq × Int) :=
  ss.filterMap fun
    | .create w s => some (w, s)
    | _ => none

/-- **A `pb.WatchResponse`** (`hdr` `none`: a `nil` header). -/
structure WireWatchRespM where
  hdr : Option HeaderM
  watchId : Int
  created : Bool
  canceled : Bool
  compactRev : w64
  cancelReason : GoString
  fragment : Bool
  events : List EventM

/-- The header as the client reads it (`ensureWatchHeader`: a `nil` header is a zero one). -/
def HeaderM.zero : HeaderM :=
  { clusterId := W64 0, memberId := W64 0, revision := W64 0, raftTerm := W64 0, leaderId := W64 0 }

/-! ## Replies against the model's answers -/

def RangeRespM.ofAns (m : RangeRespM) (a : RangeAns) : Prop :=
  m.kvs = a.kvs.map KeyValueM.ofKV ∧ m.more = a.more ∧ m.count = W64 a.count

/-- A transaction's operation reply against the model's (a nested range's header revision is
modelled; the other nested headers are not). -/
inductive ResponseOpM.ofResp : ResponseOpM → OpResp → Prop
  | empty : ResponseOpM.ofResp .empty .empty
  | range (m : RangeRespM) (rev : Nat) (a : RangeAns) : m.hdr.map (·.revision) = some (W64 rev) →
      m.ofAns a → ResponseOpM.ofResp (.range m) (.range rev a)
  | put (m : PutRespM) (prev : Option KV) : m.prevKv = prev.map KeyValueM.ofKV →
      ResponseOpM.ofResp (.put m) (.put prev)
  | deleteRange (m : DeleteRespM) (n : Nat) (l : List KV) :
      m.deleted = W64 n → m.prevKvs = l.map KeyValueM.ofKV →
      ResponseOpM.ofResp (.deleteRange m) (.deleteRange n l)
  | txn (hdr : HeaderM) (ok : Bool) (ms : List ResponseOpM) (rs : List OpResp) :
      List.Forall₂ ResponseOpM.ofResp ms rs → ResponseOpM.ofResp (.txn hdr ok ms) (.txn ok rs)

def TxnRespM.ofResps (m : TxnRespM) (ok : Bool) (rs : List OpResp) : Prop :=
  m.succeeded = ok ∧ List.Forall₂ ResponseOpM.ofResp m.responses rs

/-! ## Ownership -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The protobuf bookkeeping fields of the message of type `t` at `p` (`state`, `sizeCache`,
`unknownFields`): opaque. -/
opaque protoRest [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Type) (p : Loc) (dq : DFrac) : IProp GF := iprop(True)

opaque respHeaderOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : HeaderM) : IProp GF := iprop(True)
opaque keyValueOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : KeyValueM) : IProp GF := iprop(True)
opaque rangeRespOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : RangeRespM) : IProp GF := iprop(True)
opaque putRespOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : PutRespM) : IProp GF := iprop(True)
opaque deleteRespOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : DeleteRespM) : IProp GF := iprop(True)
opaque responseOpOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : ResponseOpM) : IProp GF := iprop(True)
opaque txnRespOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : TxnRespM) : IProp GF := iprop(True)
opaque compactRespOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : CompactRespM) : IProp GF := iprop(True)

opaque rangeReqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (r : RangeReq) : IProp GF := iprop(True)
opaque putReqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (r : PutReq) : IProp GF := iprop(True)
opaque deleteReqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (r : DeleteReq) : IProp GF := iprop(True)
opaque compareOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (c : EtcdModel.Compare) : IProp GF := iprop(True)
opaque requestOpOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (op : RequestOp) : IProp GF := iprop(True)
opaque txnReqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (t : TxnReq) : IProp GF := iprop(True)
opaque compactReqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (rev : Int) (physical : Bool) : IProp GF := iprop(True)

/-- **A range end as mvcc reads the slice** (`treeIndex`, `index.go`): a `nil` end names one key
(`[]`), a non-`nil` empty end every key from the key on (`"\x00"`, as `KeyRange.mem` reads it), any
other end itself. (Protobuf decodes an absent end as `nil`; `clientv3.WithRange("")` and the
in-process adapter pass a non-`nil` empty one.) -/
def endOf (es : GoSlice) (bs : GoString) : GoString :=
  if es = slice.nil then [] else if bs = [] then [0#8] else bs

/-- A slice of message pointers, each owning its model. -/
def msgsOwn {M : Type} (own : Loc → DFrac → M → IProp GF) (sl : GoSlice) (dq : DFrac)
    (ms : List M) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*{dq} ps ∗ [∗list] p; m ∈ ps; ms, own p dq m)

/-- An optional message pointer: `nil`, or one owning its model. -/
def optOwn {M : Type} (own : Loc → DFrac → M → IProp GF) (p : Loc) (dq : DFrac) :
    Option M → IProp GF
  | none => iprop(⌜p = null⌝)
  | some m => own p dq m

/-- A freshly allocated message's bookkeeping fields (zero) are its `protoRest` (for each message
type `t` above, whose bookkeeping fields have these names). -/
def protoRest_zero.spec : Prop := ∀ (t : Type) (p : Loc),
  p.[t, go!"state"] ↦ (zero_val google_golang_org.protobuf.internal.impl.MessageState) ∗
    p.[t, go!"sizeCache"] ↦ (W32 0) ∗ p.[t, go!"unknownFields"] ↦ slice.nil ⊢
  protoRest (GF := GF) t p (DFrac.own 1)

def respHeaderOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : HeaderM),
  respHeaderOwn (GF := GF) p dq m ⊣⊢
    protoRest etcdserverpb.ResponseHeader p dq ∗
    p.[etcdserverpb.ResponseHeader, go!"ClusterId"] ↦{dq} m.clusterId ∗
    p.[etcdserverpb.ResponseHeader, go!"MemberId"] ↦{dq} m.memberId ∗
    p.[etcdserverpb.ResponseHeader, go!"Revision"] ↦{dq} m.revision ∗
    p.[etcdserverpb.ResponseHeader, go!"RaftTerm"] ↦{dq} m.raftTerm ∗
    p.[etcdserverpb.ResponseHeader, go!"LeaderId"] ↦{dq} m.leaderId

def keyValueOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : KeyValueM),
  keyValueOwn (GF := GF) p dq m ⊣⊢
    ∃ (ks vs : GoSlice), protoRest mvccpb.KeyValue p dq ∗
    p.[mvccpb.KeyValue, go!"Key"] ↦{dq} ks ∗ ks ↦*□ m.key ∗
    p.[mvccpb.KeyValue, go!"CreateRevision"] ↦{dq} m.createRevision ∗
    p.[mvccpb.KeyValue, go!"ModRevision"] ↦{dq} m.modRevision ∗
    p.[mvccpb.KeyValue, go!"Version"] ↦{dq} m.version ∗
    p.[mvccpb.KeyValue, go!"Value"] ↦{dq} vs ∗ vs ↦*□ m.value ∗
    p.[mvccpb.KeyValue, go!"Lease"] ↦{dq} m.lease

def rangeRespOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : RangeRespM),
  rangeRespOwn (GF := GF) p dq m ⊣⊢
    ∃ (h : Loc) (kvs : GoSlice), protoRest etcdserverpb.RangeResponse p dq ∗
    p.[etcdserverpb.RangeResponse, go!"Header"] ↦{dq} h ∗ optOwn respHeaderOwn h dq m.hdr ∗
    p.[etcdserverpb.RangeResponse, go!"Kvs"] ↦{dq} kvs ∗ msgsOwn keyValueOwn kvs dq m.kvs ∗
    p.[etcdserverpb.RangeResponse, go!"More"] ↦{dq} m.more ∗
    p.[etcdserverpb.RangeResponse, go!"Count"] ↦{dq} m.count

def putRespOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : PutRespM),
  putRespOwn (GF := GF) p dq m ⊣⊢
    ∃ (h pk : Loc), protoRest etcdserverpb.PutResponse p dq ∗
    p.[etcdserverpb.PutResponse, go!"Header"] ↦{dq} h ∗ respHeaderOwn h dq m.hdr ∗
    p.[etcdserverpb.PutResponse, go!"PrevKv"] ↦{dq} pk ∗ optOwn keyValueOwn pk dq m.prevKv

def deleteRespOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : DeleteRespM),
  deleteRespOwn (GF := GF) p dq m ⊣⊢
    ∃ (h : Loc) (pks : GoSlice), protoRest etcdserverpb.DeleteRangeResponse p dq ∗
    p.[etcdserverpb.DeleteRangeResponse, go!"Header"] ↦{dq} h ∗ respHeaderOwn h dq m.hdr ∗
    p.[etcdserverpb.DeleteRangeResponse, go!"Deleted"] ↦{dq} m.deleted ∗
    p.[etcdserverpb.DeleteRangeResponse, go!"PrevKvs"] ↦{dq} pks ∗
    msgsOwn keyValueOwn pks dq m.prevKvs

/-- The `Response` oneof of a `ResponseOp` holding `m` (a wrapper struct per case). -/
def responseOneof (iv : GoInterface) (dq : DFrac) : ResponseOpM → IProp GF
  | .empty => iprop(⌜iv = GoInterface.nil⌝)
  | .range m => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w⌝ ∗
      w.[etcdserverpb.ResponseOp_ResponseRange, go!"ResponseRange"] ↦{dq} q ∗ rangeRespOwn q dq m)
  | .put m => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w⌝ ∗
      w.[etcdserverpb.ResponseOp_ResponsePut, go!"ResponsePut"] ↦{dq} q ∗ putRespOwn q dq m)
  | .deleteRange m => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w⌝ ∗
      w.[etcdserverpb.ResponseOp_ResponseDeleteRange, go!"ResponseDeleteRange"] ↦{dq} q ∗
      deleteRespOwn q dq m)
  | .txn hdr ok rs => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w⌝ ∗
      w.[etcdserverpb.ResponseOp_ResponseTxn, go!"ResponseTxn"] ↦{dq} q ∗
      txnRespOwn q dq { hdr := hdr, succeeded := ok, responses := rs })

def responseOpOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : ResponseOpM),
  responseOpOwn (GF := GF) p dq m ⊣⊢
    ∃ iv : GoInterface, protoRest etcdserverpb.ResponseOp p dq ∗
    p.[etcdserverpb.ResponseOp, go!"Response"] ↦{dq} iv ∗ responseOneof iv dq m

def txnRespOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : TxnRespM),
  txnRespOwn (GF := GF) p dq m ⊣⊢
    ∃ (h : Loc) (rs : GoSlice), protoRest etcdserverpb.TxnResponse p dq ∗
    p.[etcdserverpb.TxnResponse, go!"Header"] ↦{dq} h ∗ respHeaderOwn h dq m.hdr ∗
    p.[etcdserverpb.TxnResponse, go!"Succeeded"] ↦{dq} m.succeeded ∗
    p.[etcdserverpb.TxnResponse, go!"Responses"] ↦{dq} rs ∗ msgsOwn responseOpOwn rs dq m.responses

def compactRespOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : CompactRespM),
  compactRespOwn (GF := GF) p dq m ⊣⊢
    ∃ h : Loc, protoRest etcdserverpb.CompactionResponse p dq ∗
    p.[etcdserverpb.CompactionResponse, go!"Header"] ↦{dq} h ∗ respHeaderOwn h dq m.hdr

/-- A message owned at some fraction is at a non-nil pointer (the replies and the messages nested
in them). -/
def msgOwn_ne_null.spec : Prop :=
  (∀ p dq m, rangeRespOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, putRespOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, deleteRespOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, txnRespOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, compactRespOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, respHeaderOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, keyValueOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝) ∧
  (∀ p dq m, responseOpOwn (GF := GF) p dq m ⊢ ⌜p ≠ null⌝)

/-- A reply persisted: every message predicate is fractional in `dq` and may be made read-only.
Stated for the five replies a client gets (the nested messages follow by their unfold laws). -/
def replyPersist.spec : Prop :=
  (∀ p m, rangeRespOwn (GF := GF) p (DFrac.own 1) m ⊢ |==> rangeRespOwn p DFrac.discard m) ∧
  (∀ p m, putRespOwn (GF := GF) p (DFrac.own 1) m ⊢ |==> putRespOwn p DFrac.discard m) ∧
  (∀ p m, deleteRespOwn (GF := GF) p (DFrac.own 1) m ⊢ |==> deleteRespOwn p DFrac.discard m) ∧
  (∀ p m, txnRespOwn (GF := GF) p (DFrac.own 1) m ⊢ |==> txnRespOwn p DFrac.discard m) ∧
  (∀ p m, compactRespOwn (GF := GF) p (DFrac.own 1) m ⊢ |==> compactRespOwn p DFrac.discard m)

/-- **Read-only messages are persistent** (integration I1, 1g's need: the cache shares events among
its watchers and store and returns read-only replies): every message predicate at `DFrac.discard`,
and the protobuf bookkeeping under it. Realized by 3h through `Proto.msgAt`'s persistence at a
discarded fraction. -/
def msgOwn_discard_persistent.spec : Prop :=
  (∀ (t : Type) p, Persistent (protoRest (GF := GF) t p DFrac.discard)) ∧
  (∀ p m, Persistent (respHeaderOwn (GF := GF) p DFrac.discard m)) ∧
  (∀ p m, Persistent (keyValueOwn (GF := GF) p DFrac.discard m)) ∧
  (∀ p m, Persistent (rangeRespOwn (GF := GF) p DFrac.discard m)) ∧
  (∀ p m, Persistent (putRespOwn (GF := GF) p DFrac.discard m)) ∧
  (∀ p m, Persistent (deleteRespOwn (GF := GF) p DFrac.discard m)) ∧
  (∀ p m, Persistent (responseOpOwn (GF := GF) p DFrac.discard m)) ∧
  (∀ p m, Persistent (txnRespOwn (GF := GF) p DFrac.discard m)) ∧
  (∀ p m, Persistent (compactRespOwn (GF := GF) p DFrac.discard m))

/-- **A message's bookkeeping persisted** (verify round, A1-provability F6): `protoRest` is
fractional in `dq` and may be made read-only. With the unfold laws (each field's points-to persisted
by Go's own `↦` laws) it persists any message, a request a client built (`Cmp`'s `Compare`,
`txn.Commit`'s `RequestOp`s and `TxnRequest`, held at one `discard` fraction) as well as a reply.
Realized by 3h through `Proto.msgAt`, as `msgOwn_discard_persistent`. -/
def protoRest_persist.spec : Prop := ∀ (t : Type) (p : Loc),
  protoRest (GF := GF) t p (DFrac.own 1) ⊢ |==> protoRest t p DFrac.discard

/-! ### Requests -/

def rangeReqOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (r : RangeReq),
  rangeReqOwn (GF := GF) p dq r ⊣⊢
    ∃ (ks es : GoSlice) (ebs : GoString), protoRest etcdserverpb.RangeRequest p dq ∗
    p.[etcdserverpb.RangeRequest, go!"Key"] ↦{dq} ks ∗ ks ↦*□ r.key ∗
    p.[etcdserverpb.RangeRequest, go!"RangeEnd"] ↦{dq} es ∗ es ↦*□ ebs ∗
    ⌜r.rangeEnd = endOf es ebs ∧ (es = slice.nil ∨ ebs ≠ [])⌝ ∗
    p.[etcdserverpb.RangeRequest, go!"Limit"] ↦{dq} (W64 r.limit) ∗
    p.[etcdserverpb.RangeRequest, go!"Revision"] ↦{dq} (W64 r.revision) ∗
    p.[etcdserverpb.RangeRequest, go!"SortOrder"] ↦{dq} (W32 r.sortOrder) ∗
    p.[etcdserverpb.RangeRequest, go!"SortTarget"] ↦{dq} (W32 r.sortTarget) ∗
    p.[etcdserverpb.RangeRequest, go!"Serializable"] ↦{dq} r.serializable ∗
    p.[etcdserverpb.RangeRequest, go!"KeysOnly"] ↦{dq} r.keysOnly ∗
    p.[etcdserverpb.RangeRequest, go!"CountOnly"] ↦{dq} r.countOnly ∗
    p.[etcdserverpb.RangeRequest, go!"MinModRevision"] ↦{dq} (W64 r.minModRevision) ∗
    p.[etcdserverpb.RangeRequest, go!"MaxModRevision"] ↦{dq} (W64 r.maxModRevision) ∗
    p.[etcdserverpb.RangeRequest, go!"MinCreateRevision"] ↦{dq} (W64 r.minCreateRevision) ∗
    p.[etcdserverpb.RangeRequest, go!"MaxCreateRevision"] ↦{dq} (W64 r.maxCreateRevision) ∗
    ⌜(-2 ^ 63 ≤ r.limit ∧ r.limit < 2 ^ 63) ∧ (-2 ^ 63 ≤ r.revision ∧ r.revision < 2 ^ 63) ∧
      (-2 ^ 31 ≤ r.sortOrder ∧ r.sortOrder < 2 ^ 31) ∧
      (-2 ^ 31 ≤ r.sortTarget ∧ r.sortTarget < 2 ^ 31) ∧
      (-2 ^ 63 ≤ r.minModRevision ∧ r.minModRevision < 2 ^ 63) ∧
      (-2 ^ 63 ≤ r.maxModRevision ∧ r.maxModRevision < 2 ^ 63) ∧
      (-2 ^ 63 ≤ r.minCreateRevision ∧ r.minCreateRevision < 2 ^ 63) ∧
      (-2 ^ 63 ≤ r.maxCreateRevision ∧ r.maxCreateRevision < 2 ^ 63)⌝

def putReqOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (r : PutReq),
  putReqOwn (GF := GF) p dq r ⊣⊢
    ∃ (ks vs : GoSlice), protoRest etcdserverpb.PutRequest p dq ∗
    p.[etcdserverpb.PutRequest, go!"Key"] ↦{dq} ks ∗ ks ↦*□ r.key ∗
    p.[etcdserverpb.PutRequest, go!"Value"] ↦{dq} vs ∗ vs ↦*□ r.value ∗
    p.[etcdserverpb.PutRequest, go!"Lease"] ↦{dq} (W64 r.lease) ∗
    p.[etcdserverpb.PutRequest, go!"PrevKv"] ↦{dq} r.prevKv ∗
    p.[etcdserverpb.PutRequest, go!"IgnoreValue"] ↦{dq} r.ignoreValue ∗
    p.[etcdserverpb.PutRequest, go!"IgnoreLease"] ↦{dq} r.ignoreLease ∗
    ⌜-2 ^ 63 ≤ r.lease ∧ r.lease < 2 ^ 63⌝

def deleteReqOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (r : DeleteReq),
  deleteReqOwn (GF := GF) p dq r ⊣⊢
    ∃ (ks es : GoSlice) (ebs : GoString), protoRest etcdserverpb.DeleteRangeRequest p dq ∗
    p.[etcdserverpb.DeleteRangeRequest, go!"Key"] ↦{dq} ks ∗ ks ↦*□ r.key ∗
    p.[etcdserverpb.DeleteRangeRequest, go!"RangeEnd"] ↦{dq} es ∗ es ↦*□ ebs ∗
    ⌜r.rangeEnd = endOf es ebs ∧ (es = slice.nil ∨ ebs ≠ [])⌝ ∗
    p.[etcdserverpb.DeleteRangeRequest, go!"PrevKv"] ↦{dq} r.prevKv

/-- The `TargetUnion` oneof of a `Compare` holding `v`. -/
def cmpOneof (iv : GoInterface) (dq : DFrac) : CmpVal → IProp GF
  | .none => iprop(⌜iv = GoInterface.nil⌝)
  | .version n => iprop(∃ w : Loc,
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_Version.ty) #w ∧
        -2 ^ 63 ≤ n ∧ n < 2 ^ 63⌝ ∗
      w.[etcdserverpb.Compare_Version, go!"Version"] ↦{dq} (W64 n))
  | .createRevision n => iprop(∃ w : Loc,
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_CreateRevision.ty) #w ∧
        -2 ^ 63 ≤ n ∧ n < 2 ^ 63⌝ ∗
      w.[etcdserverpb.Compare_CreateRevision, go!"CreateRevision"] ↦{dq} (W64 n))
  | .modRevision n => iprop(∃ w : Loc,
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_ModRevision.ty) #w ∧
        -2 ^ 63 ≤ n ∧ n < 2 ^ 63⌝ ∗
      w.[etcdserverpb.Compare_ModRevision, go!"ModRevision"] ↦{dq} (W64 n))
  | .value v => iprop(∃ (w : Loc) (vs : GoSlice),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_Value.ty) #w⌝ ∗
      w.[etcdserverpb.Compare_Value, go!"Value"] ↦{dq} vs ∗ vs ↦*□ v)
  | .lease n => iprop(∃ w : Loc,
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.Compare_Lease.ty) #w ∧
        -2 ^ 63 ≤ n ∧ n < 2 ^ 63⌝ ∗
      w.[etcdserverpb.Compare_Lease, go!"Lease"] ↦{dq} (W64 n))

def compareOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (c : EtcdModel.Compare),
  compareOwn (GF := GF) p dq c ⊣⊢
    ∃ (ks es : GoSlice) (ebs : GoString) (iv : GoInterface), protoRest etcdserverpb.Compare p dq ∗
    p.[etcdserverpb.Compare, go!"Result"] ↦{dq} (W32 c.result) ∗
    p.[etcdserverpb.Compare, go!"Target"] ↦{dq} (W32 c.target) ∗
    p.[etcdserverpb.Compare, go!"Key"] ↦{dq} ks ∗ ks ↦*□ c.key ∗
    p.[etcdserverpb.Compare, go!"RangeEnd"] ↦{dq} es ∗ es ↦*□ ebs ∗
    ⌜c.rangeEnd = endOf es ebs ∧ (es = slice.nil ∨ ebs ≠ [])⌝ ∗
    p.[etcdserverpb.Compare, go!"TargetUnion"] ↦{dq} iv ∗ cmpOneof iv dq c.targetUnion ∗
    ⌜(-2 ^ 31 ≤ c.result ∧ c.result < 2 ^ 31) ∧ (-2 ^ 31 ≤ c.target ∧ c.target < 2 ^ 31)⌝

/-- The `Request` oneof of a `RequestOp` holding `op`. -/
def requestOneof (iv : GoInterface) (dq : DFrac) : RequestOp → IProp GF
  | .empty => iprop(⌜iv = GoInterface.nil⌝)
  | .range r => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w⌝ ∗
      w.[etcdserverpb.RequestOp_RequestRange, go!"RequestRange"] ↦{dq} q ∗ rangeReqOwn q dq r)
  | .put r => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w⌝ ∗
      w.[etcdserverpb.RequestOp_RequestPut, go!"RequestPut"] ↦{dq} q ∗ putReqOwn q dq r)
  | .deleteRange r => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w⌝ ∗
      w.[etcdserverpb.RequestOp_RequestDeleteRange, go!"RequestDeleteRange"] ↦{dq} q ∗
      deleteReqOwn q dq r)
  | .txn cmps succ fail => iprop(∃ (w q : Loc),
      ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w⌝ ∗
      w.[etcdserverpb.RequestOp_RequestTxn, go!"RequestTxn"] ↦{dq} q ∗
      txnReqOwn q dq { compare := cmps, success := succ, failure := fail })

def requestOpOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (op : RequestOp),
  requestOpOwn (GF := GF) p dq op ⊣⊢
    ∃ iv : GoInterface, protoRest etcdserverpb.RequestOp p dq ∗
    p.[etcdserverpb.RequestOp, go!"Request"] ↦{dq} iv ∗ requestOneof iv dq op

def txnReqOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (t : TxnReq),
  txnReqOwn (GF := GF) p dq t ⊣⊢
    ∃ (cs ss fs : GoSlice), protoRest etcdserverpb.TxnRequest p dq ∗
    p.[etcdserverpb.TxnRequest, go!"Compare"] ↦{dq} cs ∗ msgsOwn compareOwn cs dq t.compare ∗
    p.[etcdserverpb.TxnRequest, go!"Success"] ↦{dq} ss ∗ msgsOwn requestOpOwn ss dq t.success ∗
    p.[etcdserverpb.TxnRequest, go!"Failure"] ↦{dq} fs ∗ msgsOwn requestOpOwn fs dq t.failure

def compactReqOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (rev : Int) (phys : Bool),
  compactReqOwn (GF := GF) p dq rev phys ⊣⊢
    protoRest etcdserverpb.CompactionRequest p dq ∗
    p.[etcdserverpb.CompactionRequest, go!"Revision"] ↦{dq} (W64 rev) ∗
    p.[etcdserverpb.CompactionRequest, go!"Physical"] ↦{dq} phys ∗
    ⌜-2 ^ 63 ≤ rev ∧ rev < 2 ^ 63⌝

/-! ### Watch messages (batch 1b's; realized by 3h, unfolded by 2b's `watchReqOwn_unfold`,
`wireWatchRespOwn_unfold` and the law below) -/

/-- **An `mvccpb.Event` message** at `p`, at the fraction `dq`. -/
opaque eventOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (e : EventM) : IProp GF := iprop(True)

/-- **Slot (2a, 3h)**: a `pb.WatchRequest` message at `p` modelled by `r`. A create's key is
`w.range.key`, or `""` when that is `"\x00"` (`toPB` sends the watch's own key, which the member
normalizes). -/
opaque watchReqOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (r : WireWatchReq) : IProp GF := iprop(True)

/-- **Slot (2a, 3h)**: a `pb.WatchResponse` message at `p` modelled by `m`. -/
opaque wireWatchRespOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (dq : DFrac) (m : WireWatchRespM) : IProp GF := iprop(True)

/-- **What `eventOwn` means**: the `Event` struct's fields (`Type` `0` a put, `1` a delete). -/
def eventOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (e : EventM),
  eventOwn (GF := GF) p dq e ⊣⊢
    ∃ (kv pk : Loc), protoRest go_etcd_io.etcd.api.v3.mvccpb.Event p dq ∗
    p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Type"] ↦{dq} (if e.del then W32 1 else W32 0) ∗
    p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"Kv"] ↦{dq} kv ∗ keyValueOwn kv dq e.kv ∗
    p.[go_etcd_io.etcd.api.v3.mvccpb.Event, go!"PrevKv"] ↦{dq} pk ∗ optOwn keyValueOwn pk dq e.prevKv

/-- An event message made read-only. -/
def eventOwn_persist.spec : Prop := ∀ (p : Loc) (dq : DFrac) (e : EventM),
  eventOwn (GF := GF) p dq e ⊢ |==> eventOwn p DFrac.discard e

/-- A read-only event message is persistent (with `msgOwn_discard_persistent`). -/
def eventOwn_discard_persistent.spec : Prop :=
  ∀ (p : Loc) (e : EventM), Persistent (eventOwn (GF := GF) p DFrac.discard e)

end own

end EtcdWire
end EtcdGrove
end Perennial
