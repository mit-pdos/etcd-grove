/-
**The client meets the server** (unit C1, 2026-10-14): the vocabulary of the client's KV path
over gRPC (`client/v3/kv.go`, `retry.go`, the generated stub `api/etcdserverpb/rpc_grpc.pb.go`)
and of its trust boundary, grpc's `ClientConn.Invoke` (`Spec/google_golang_org/grpc/
ClientConn__Invoke.lean`, generic since 2026-10-14). Lean-first (no Rocq counterpart); the design
is in `notes/decisions.md`, "The client meets the server (unit C1)" and "A generic gRPC
specification".

**The connection** (`isEtcdConn conn addr`, unit P3a; it was grpc's opaque `isGrpcConn conn
addr`): the client's connection `conn` reaches the gRPC server at `addr` (grpc's `grpcConn`,
`google_golang_org/grpc/InvGrpc.lean`), whose methods are registered with their specs
(`isGrpcRpcs addr name Spec`), with one unary interceptor that meets the retry interceptor's
contract (`etcdInterceptorOk`: what `Client.unaryClientInterceptor` returns,
`Client__unaryClientInterceptor.lean`) and no default call options: what `clientv3.New`'s
`dialSetupOpts` dials with, given no `Config.DialOptions` that add interceptors or call options
(an assumption about the unverified constructor and its configuration). The client's
calls are specified for any spec of the KV service's `Put` and `Range` (predicate transformers
over the messages' models, `GrpcSpec pbPutRequest pbPutResponse`, ...), and for any caller's
postcondition `Φ`; etcd's server's specs and handler proofs are in `client/v3/Results.lean`.

**Messages** (`ProtoMsg` instances: `pbPutRequest`, `pbRangeRequest`, `pbPutResponse`,
`pbRangeResponse`; `pbDeleteRangeRequest`, `pbDeleteRangeResponse` for the server's side): a request's model is the server's model of it (`putReqOp`, `rangeReqOp`:
`OpFull`), the sender's message the owned struct with its slices' contents, the decoded copy the
server's own predicate (`txn.putRequestIs`, `txn.rangeRequestIs`); a response's model is every
field the wire carries (`PutRespM`, `RangeRespM`: its header (`hdrFull`, the five fields), a put's
previous key-value (`txn.kvIs`, the six fields), a range's key-values (`txn.kvsIs`), `More`,
`Count`), held read-only (`putRespMsg`, `rangeRespMsg`) by the server's response and by the
client's decoded reply alike (a slice's contents, not whether it is `nil`).

**Call options** (`callOptOk`, `callOptsOk`): what the client passes in a call's `opts`: grpc's own
option values that hold only scalars (`StaticMethodCallOption`, `FailFastCallOption`,
`MaxSendMsgSizeCallOption`, `MaxRecvMsgSizeCallOption`: the stub's and `client.go`'s
`defaultCallOpts`), or a `retryOption` whose closure writes only the interceptor's own `options`'
`retryPolicy` (`retryApplyOk`: `withRepeatablePolicy`'s). None writes the caller's memory, which
`Invoke`'s frame needs (grpc's `Header`/`Trailer`/`Peer` options would).

**Context errors** (`ctxErrClient ci cd`): the context's `Err()` returns client errors
(`clientErr`, nil included), and keeps returning one once it has: Go's documented contract of
`Context.Err` (nil, then `Canceled` or `DeadlineExceeded` for good) and the method sets of those
errors (leaf errors, not `EtcdError`s), which the model does not have; a premise of
`ContextError` (whose result `kv.Put` passes to `errors.As` on a second `ContextError`).

**The objects**: `kvStubAt kc conn` (the generated `*kVClient` on `conn`), `retryKVAt rkv conn`
(a `*retryKVClient` over one), `kvObjAt api addr` (a `*kv` over one, with its call options),
`clientKVAt cl addr` (what `NewKV` reads of a `*Client`: its connection and call options, fixed
since `clientv3.New`, an assumption about the unverified constructor). The call options' slice is
full (`len = cap`, as `client.go` builds it): `retryKVClient.Range` appends to it, which, with
spare capacity, would write the slice's shared backing array from concurrent calls.

**The wire models** (`putWireOf o`, `rangeWireOf o`): the server's model of the request
`kv.Do` sends for the `Op` `o` (`txn.putOpOf`, `txn.rangeOpOf` of its fields; a range end is what
the wire carries, its contents: the server reads an empty one as `nil`, as the absent field it is).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxnOwn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests
public import Proof.go_etcd_io.etcd.client.v3.ClientErr
public import Perennial.Proof.context
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil errCellOk errCellOk_nil)

/-! ## Messages -/

section model
variable [ext : FfiSyntax]

/-- A `*pb.PutResponse` as the wire carries it: its header, its previous key-value. -/
structure PutRespM where
  hdr : HdrM
  prev : Option EtcdKv

/-- A `*pb.RangeResponse` as the wire carries it. -/
structure RangeRespM where
  hdr : HdrM
  kvs : List EtcdKv
  more : Bool
  count : w64

/-- A `*pb.DeleteRangeResponse` as the wire carries it: its header, `Deleted`, `PrevKvs`. -/
structure DelRespM where
  hdr : HdrM
  deleted : w64
  prevs : List EtcdKv

/-- **A `*pb.ResponseOp` as the wire carries it** (a transaction's operation's response, nested
transactions included; unit V2): its oneof's kind and the inner response's fields, the inner
header by its revision only (the server sets nothing else there: `txn.responseOpIs`). -/
inductive OpRespM where
  | range (rev : w64) (kvs : List EtcdKv) (more : Bool) (count : w64)
  | put (rev : w64) (prev : Option EtcdKv)
  | delete (rev : w64) (deleted : w64) (prevKvs : List EtcdKv)
  | txn (rev : w64) (succeeded : Bool) (resps : List OpRespM)

/-- A `*pb.TxnResponse` as the wire carries it: its header, `Succeeded`, its `Responses`. -/
structure TxnRespM where
  hdr : HdrM
  succeeded : Bool
  resps : List OpRespM

/-- **The server's model of the delete request `req`** (whose `Key` holds `k`, `RangeEnd` `e`):
the copy the gRPC server decodes (`txn.deleteRangeRequestIs`) denotes it, its range end the
contents `e` (as `rangeReqOp`'s). -/
def deleteReqOp (req : etcdserverpb.DeleteRangeRequest) (k e : GoString) : OpFull :=
  txn.deleteOpOf k e req.PrevKv'

/-- **The server's model of the put request `kv.Do` sends for the `Op` `o`** (`txn.putOpOf` of
the request's fields). -/
def putWireOf (o : OpFull) : OpFull :=
  txn.putOpOf o.key o.val o.leaseID o.base.prevKV o.ignoreValue o.ignoreLease

/-- The `int32` enumeration value of the sort order a range request carries for the `Op` `o`
(`pb.RangeRequest_SortOrder(op.sort.Order)`, the low 32 bits; `0` without a sort option). -/
def sortOrderWire (o : OpFull) : w32 := if o.base.sortSet then W32 (sint.Z o.sortOrder) else W32 0

/-- The sort target's (as `sortOrderWire`). -/
def sortTargetWire (o : OpFull) : w32 := if o.base.sortSet then W32 (sint.Z o.sortTarget) else W32 0

/-- **The server's model of the range request `kv.Do` sends for the `Op` `o`** (`txn.rangeOpOf`
of the request's fields; the sort's order and target `0` without a sort option, their `int32`
values with one: the vertical slice's unit V2). -/
def rangeWireOf (o : OpFull) : OpFull :=
  txn.rangeOpOf o.key o.base.rangeEnd o.base.rev o.base.limit (sortOrderWire o) (sortTargetWire o)
    o.base.serializable o.keysOnly o.base.countOnly o.base.minModRev o.base.maxModRev
    o.base.minCreateRev o.base.maxCreateRev

/-- **The server's model of the delete request `kv.Do` sends for the `Op` `o`**
(`txn.deleteOpOf` of the request's fields: the key, the range end's contents, `PrevKv`; unit
V2). -/
def deleteWireOf (o : OpFull) : OpFull := txn.deleteOpOf o.key o.base.rangeEnd o.base.prevKV

/-- **`IsSortOptionValid`**: no sort option, or the order's and target's `int32` values are
among `RangeRequest_SortOrder_name`'s (`0` to `2`) and `RangeRequest_SortTarget_name`'s (`0` to
`4`) keys. -/
def sortValid (o : OpFull) : Bool :=
  or (not o.base.sortSet)
    (and (decide (0 ≤ sint.Z (sortOrderWire o) ∧ sint.Z (sortOrderWire o) ≤ 2))
      (decide (0 ≤ sint.Z (sortTargetWire o) ∧ sint.Z (sortTargetWire o) ≤ 4)))

/-- **The server's model of a transaction operation the client sends** (unit V2): a get's and a
delete's request as the wire carries them (`rangeWireOf`, `deleteWireOf`), a put as it is
(`txnOpOf`'s puts are the server's `putTxnOp`), a nested transaction's operations likewise. -/
def opWire : TxnOp → TxnOp
  | .get o => .get (rangeWireOf o)
  | .delete o => .delete (deleteWireOf o)
  | .txn cs ts es => .txn cs (ts.attach.map fun ⟨t, _⟩ => opWire t) (es.attach.map fun ⟨t, _⟩ => opWire t)
  | op => op

/-- **The server's model of a transaction the client sends** (unit V2): its comparisons (their
range ends' contents, as the wire carries them: the server reads an absent one as `[]`), its
operations' wire models (`opWire`). -/
def txnWireOf (t : TxnModel) : TxnModel :=
  { cmps := t.cmps, thenOps := t.thenOps.map opWire, elseOps := t.elseOps.map opWire }

/-- **The server's model of the put request `req`** (whose `Key` holds `k`, `Value` `v`): the copy
the gRPC server decodes (`txn.putRequestIs`) denotes it. -/
def putReqOp (req : etcdserverpb.PutRequest) (k v : GoString) : OpFull :=
  txn.putOpOf k v req.Lease' req.PrevKv' req.IgnoreValue' req.IgnoreLease'

/-- **The server's model of the range request `req`** (whose `Key` holds `k`, `RangeEnd` `e`):
the copy the gRPC server decodes (`txn.rangeRequestIs`) denotes it, its range end the contents
`e` (an empty `RangeEnd` is not on the wire: the server's copy has `nil`, which
`txn.rangeEndOf` reads as `[]`). -/
def rangeReqOp (req : etcdserverpb.RangeRequest) (k e : GoString) : OpFull :=
  txn.rangeOpOf k e req.Revision' req.Limit' req.SortOrder' req.SortTarget' req.Serializable'
    req.KeysOnly' req.CountOnly' req.MinModRevision' req.MaxModRevision' req.MinCreateRevision'
    req.MaxCreateRevision'

/-- **The wire model of a plain operation `o`** (`Op.toRequestOp`'s request, as the server reads
it; unit V2): a get's (`rangeWireOf`), a put's (`putTxnOp` of `putWireOf`), a delete's
(`deleteWireOf`). -/
def leafWire (o : OpFull) : TxnOp :=
  if o.t = W64 1 then .get (rangeWireOf o)
  else if o.t = W64 2 then txn.putTxnOp (putWireOf o)
  else .delete (deleteWireOf o)

/-- A plain operation's wire model is the wire model (`opWire`) of its transaction operation
(`txnOpOf`). -/
theorem leafWire_txnOpOf (o : OpFull) (op : TxnOp) (h : txnOpOf o = some op) :
    leafWire o = opWire op := by
  unfold txnOpOf at h
  unfold leafWire
  by_cases h1 : o.t = W64 1
  · rw [if_pos h1] at h ⊢
    by_cases hr : o.base.rev = W64 0
    · rw [if_pos hr, Option.some.injEq] at h; subst h; simp [opWire]
    · rw [if_neg hr] at h; cases h
  · rw [if_neg h1] at h ⊢
    by_cases h2 : o.t = W64 2
    · rw [if_pos h2] at h ⊢
      simp only [txn.putTxnOp, putWireOf, txn.putOpOf, op_simps]
      by_cases hv : o.ignoreValue = true <;> by_cases hl : o.ignoreLease = true <;>
        (try simp only [Bool.not_eq_true] at hv) <;> (try simp only [Bool.not_eq_true] at hl) <;>
        simp only [hv, hl, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, true_and, false_and,
          and_false, and_true, Option.some.injEq] at h ⊢
      · by_cases hz : o.val = [] ∧ o.leaseID = W64 0
        · simp [hz] at h; subst h; simp [opWire]
        · simp only [hz, ↓reduceIte] at h; cases h
      · by_cases hz : o.val = []
        · simp [hz] at h; subst h; simp [opWire]
        · simp only [hz, ↓reduceIte] at h; cases h
      · by_cases hz : o.leaseID = W64 0
        · simp [hz] at h; subst h; simp [opWire]
        · simp only [hz, ↓reduceIte] at h; cases h
      · subst h; simp [opWire]
    · rw [if_neg h2] at h ⊢
      by_cases h3 : o.t = W64 3
      · rw [if_pos h3, Option.some.injEq] at h; subst h; simp [opWire]
      · rw [if_neg h3] at h; cases h

end model

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

instance (priority := high) clientC1_typeRepr_u :
    TypeRepr go_etcd_io.etcd.client.v3.Client.underlying go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

/-- **The `*pb.PutResponse` `l` holds the message `m`** (read-only; see the file header). -/
def putRespMsg (l : Loc) (m : PutRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ h pk : Loc,
    structFieldRef etcdserverpb.PutResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.PutResponse go!"PrevKv" l ↦□ pk ∗
    match m.prev with
    | none => iprop(⌜pk = null⌝)
    | some v => iprop(⌜pk ≠ null⌝ ∗ txn.kvIs pk v))

instance putRespMsg_persistent (l : Loc) (m : PutRespM) :
    Persistent (putRespMsg (GF := GF) l m) := by
  unfold putRespMsg; cases m.prev <;> infer_instance

/-- **The `*pb.RangeResponse` `l` holds the message `m`** (read-only). -/
def rangeRespMsg (l : Loc) (m : RangeRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.RangeResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" l ↦□ sl ∗ sl ↦*□ ps ∗ txn.kvsIs ps m.kvs ∗
    structFieldRef etcdserverpb.RangeResponse go!"More" l ↦□ m.more ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" l ↦□ m.count)

instance rangeRespMsg_persistent (l : Loc) (m : RangeRespM) :
    Persistent (rangeRespMsg (GF := GF) l m) := by
  unfold rangeRespMsg; infer_instance

/-- **The `*pb.DeleteRangeResponse` `l` holds the message `m`** (read-only). -/
def delRespMsg (l : Loc) (m : DelRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" l ↦□ m.deleted ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"PrevKvs" l ↦□ sl ∗ sl ↦*□ ps ∗
    txn.kvsIs ps m.prevs)

instance delRespMsg_persistent (l : Loc) (m : DelRespM) :
    Persistent (delRespMsg (GF := GF) l m) := by
  unfold delRespMsg; infer_instance

mutual
/-- **The `*pb.ResponseOp` `p` holds the message `m`** (read-only; unit V2): its `Response`
oneof's wrapper of `m`'s kind, the inner response not nil, with its header's revision and its
fields (`txn.rangeResponseIs`, `txn.putResponseIs`, ...; a nested transaction's responses
recursively). -/
def opRespMsg (p : Loc) : OpRespM → IProp GF
  | .range rev kvs more count => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ r ∗
      txn.rangeResponseIs r rev kvs more count)
  | .put rev prev => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ r ∗
      txn.putResponseIs r rev prev)
  | .delete rev n prevs => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty)
          #w : GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w ↦□ r ∗
      ⌜r ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" r ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
      structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" r ↦□ n ∗
      structFieldRef etcdserverpb.DeleteRangeResponse go!"PrevKvs" r ↦□ sl ∗ sl ↦*□ ps ∗
      txn.kvsIs ps prevs)
  | .txn rev ok resps => iprop(⌜p ≠ null⌝ ∗ ∃ (w r h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ r ∗ ⌜r ≠ null⌝ ∗
      structFieldRef etcdserverpb.TxnResponse go!"Header" r ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" r ↦□ ok ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" r ↦□ sl ∗ sl ↦*□ ps ∗
      opRespsMsg ps resps)

/-- The `*pb.ResponseOp`s `ps` hold, in order, the messages `ms`. -/
def opRespsMsg : List Loc → List OpRespM → IProp GF
  | [], [] => iprop(True)
  | p :: ps, m :: ms => iprop(opRespMsg p m ∗ opRespsMsg ps ms)
  | _, _ => iprop(False)
end

mutual
theorem opRespMsg_persistent' (p : Loc) : ∀ m : OpRespM, Persistent (opRespMsg (GF := GF) p m)
  | .range .. => by unfold opRespMsg; infer_instance
  | .put .. => by unfold opRespMsg; infer_instance
  | .delete .. => by unfold opRespMsg; infer_instance
  | .txn _ _ resps => by
    haveI : ∀ ps, Persistent (opRespsMsg (GF := GF) ps resps) := fun ps => opRespsMsg_persistent' ps resps
    unfold opRespMsg; infer_instance

theorem opRespsMsg_persistent' : ∀ (ps : List Loc) (ms : List OpRespM),
    Persistent (opRespsMsg (GF := GF) ps ms)
  | [], [] => by unfold opRespsMsg; infer_instance
  | p :: ps, m :: ms => by
    haveI := opRespMsg_persistent' p m
    haveI := opRespsMsg_persistent' ps ms
    unfold opRespsMsg; infer_instance
  | [], _ :: _ => by unfold opRespsMsg; infer_instance
  | _ :: _, [] => by unfold opRespsMsg; infer_instance
end

instance opRespMsg_persistent (p : Loc) (m : OpRespM) : Persistent (opRespMsg (GF := GF) p m) :=
  opRespMsg_persistent' p m

instance opRespsMsg_persistent (ps : List Loc) (ms : List OpRespM) :
    Persistent (opRespsMsg (GF := GF) ps ms) := opRespsMsg_persistent' ps ms

/-- **The `*pb.TxnResponse` `l` holds the message `m`** (read-only; unit V2). -/
def txnRespMsg (l : Loc) (m : TxnRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" l ↦□ m.succeeded ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" l ↦□ sl ∗ sl ↦*□ ps ∗
    opRespsMsg ps m.resps)

instance txnRespMsg_persistent (l : Loc) (m : TxnRespM) :
    Persistent (txnRespMsg (GF := GF) l m) := by
  unfold txnRespMsg; infer_instance

/-! ## A transaction request in the client's memory (unit V2) -/

/-- **The `*pb.RangeRequest` `r` of the client's memory holds the get whose wire model is `o`**
(read-only fields; the range end by its contents, as the wire carries it: `txn.rangeOpOf` of
the contents, not of `txn.rangeEndOf`, which reads an empty non-`nil` slice as `[0]`). -/
def rangeReqAt (r : Loc) (o : OpFull) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (k e : GoString) (rev limit : w64)
      (order target : w32) (ser ko co : Bool) (minM maxM minC maxC : w64),
    structFieldRef etcdserverpb.RangeRequest go!"Key" r ↦□ ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.RangeRequest go!"RangeEnd" r ↦□ esl ∗ esl ↦*□ e ∗
    structFieldRef etcdserverpb.RangeRequest go!"Limit" r ↦□ limit ∗
    structFieldRef etcdserverpb.RangeRequest go!"Revision" r ↦□ rev ∗
    structFieldRef etcdserverpb.RangeRequest go!"SortOrder" r ↦□ order ∗
    structFieldRef etcdserverpb.RangeRequest go!"SortTarget" r ↦□ target ∗
    structFieldRef etcdserverpb.RangeRequest go!"Serializable" r ↦□ ser ∗
    structFieldRef etcdserverpb.RangeRequest go!"KeysOnly" r ↦□ ko ∗
    structFieldRef etcdserverpb.RangeRequest go!"CountOnly" r ↦□ co ∗
    structFieldRef etcdserverpb.RangeRequest go!"MinModRevision" r ↦□ minM ∗
    structFieldRef etcdserverpb.RangeRequest go!"MaxModRevision" r ↦□ maxM ∗
    structFieldRef etcdserverpb.RangeRequest go!"MinCreateRevision" r ↦□ minC ∗
    structFieldRef etcdserverpb.RangeRequest go!"MaxCreateRevision" r ↦□ maxC ∗
    ⌜o = txn.rangeOpOf k e rev limit order target ser ko co minM maxM minC maxC⌝)

/-- **The `*pb.PutRequest` `p` of the client's memory holds the put `o`** (read-only fields). -/
def putReqAt (p : Loc) (o : OpFull) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ (ksl vsl : GoSlice) (k v : GoString) (lease : w64) (pk iv il : Bool),
    structFieldRef etcdserverpb.PutRequest go!"Key" p ↦□ ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.PutRequest go!"Value" p ↦□ vsl ∗ vsl ↦*□ v ∗
    structFieldRef etcdserverpb.PutRequest go!"Lease" p ↦□ lease ∗
    structFieldRef etcdserverpb.PutRequest go!"PrevKv" p ↦□ pk ∗
    structFieldRef etcdserverpb.PutRequest go!"IgnoreValue" p ↦□ iv ∗
    structFieldRef etcdserverpb.PutRequest go!"IgnoreLease" p ↦□ il ∗
    ⌜o = txn.putOpOf k v lease pk iv il⌝)

/-- **The `*pb.DeleteRangeRequest` `d` of the client's memory holds the delete whose wire model
is `o`** (read-only fields; the range end by its contents). -/
def deleteReqAt (d : Loc) (o : OpFull) : IProp GF :=
  iprop(⌜d ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (k e : GoString) (pk : Bool),
    structFieldRef etcdserverpb.DeleteRangeRequest go!"Key" d ↦□ ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" d ↦□ esl ∗ esl ↦*□ e ∗
    structFieldRef etcdserverpb.DeleteRangeRequest go!"PrevKv" d ↦□ pk ∗
    ⌜o = txn.deleteOpOf k e pk⌝)

/-- **The `*pb.RequestOp` `p` of the client's memory holds the operation `op`** (its wire
model; read-only): a get, a put or a delete (`Op.toRequestOp`'s); a nested transaction is not
covered (`False`: the builder's operations are plain). -/
def reqOpAt (p : Loc) (op : TxnOp) : IProp GF :=
  match op with
  | .get o => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
      rangeReqAt r o)
  | .delete o => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
      deleteReqAt r o)
  | .txn _ _ _ => iprop(False)
  | _ => iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc) (o : OpFull),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
      putReqAt r o ∗ ⌜op = txn.putTxnOp o⌝)

/-- The `*pb.RequestOp`s `ps` hold, in order, the operations `ops`. -/
def reqOpsAt (ps : List Loc) (ops : List TxnOp) : IProp GF :=
  iprop(⌜ps.length = ops.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (op : TxnOp), ⌜ps[i]? = some p⌝ -∗ ⌜ops[i]? = some op⌝ -∗
      reqOpAt p op)

/-- The `*pb.Compare`s `ps` hold, in order, the comparisons `ms` (not nil, read-only). -/
def comparesAt (ps : List Loc) (ms : List CmpModel) : IProp GF :=
  iprop(⌜ps.length = ms.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (m : CmpModel), ⌜ps[i]? = some p⌝ -∗ ⌜ms[i]? = some m⌝ -∗
      ⌜p ≠ null⌝ ∗ compareAt p m)

/-- **The `pb.TxnRequest` value `req` of the client's memory holds the transaction `t`** (its
wire model, `txnWireOf` of the builder's; its slices read-only). -/
def txnReqAt (req : etcdserverpb.TxnRequest) (t : TxnModel) : IProp GF :=
  iprop(∃ cps sps fps : List Loc,
    req.Compare' ↦*□ cps ∗ comparesAt cps t.cmps ∗
    req.Success' ↦*□ sps ∗ reqOpsAt sps t.thenOps ∗
    req.Failure' ↦*□ fps ∗ reqOpsAt fps t.elseOps)

instance rangeReqAt_persistent (r : Loc) (o : OpFull) : Persistent (rangeReqAt (GF := GF) r o) := by
  unfold rangeReqAt; infer_instance
instance putReqAt_persistent (r : Loc) (o : OpFull) : Persistent (putReqAt (GF := GF) r o) := by
  unfold putReqAt; infer_instance
instance deleteReqAt_persistent (r : Loc) (o : OpFull) :
    Persistent (deleteReqAt (GF := GF) r o) := by
  unfold deleteReqAt; infer_instance
instance reqOpAt_persistent (p : Loc) (op : TxnOp) : Persistent (reqOpAt (GF := GF) p op) := by
  unfold reqOpAt; split <;> infer_instance
instance reqOpsAt_persistent (ps : List Loc) (ops : List TxnOp) :
    Persistent (reqOpsAt (GF := GF) ps ops) := by
  unfold reqOpsAt; infer_instance
instance comparesAt_persistent (ps : List Loc) (ms : List CmpModel) :
    Persistent (comparesAt (GF := GF) ps ms) := by
  unfold comparesAt; infer_instance
instance txnReqAt_persistent (req : etcdserverpb.TxnRequest) (t : TxnModel) :
    Persistent (txnReqAt (GF := GF) req t) := by
  unfold txnReqAt; infer_instance

/-- A put's `*pb.RequestOp` (`reqOpAt` of the server's put `txn.putTxnOp o`). -/
theorem reqOpAt_put (p w r : Loc) (o : OpFull) :
    ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗ putReqAt r o ⊢
    reqOpAt (GF := GF) p (txn.putTxnOp o) := by
  iintro ⟨%Hp, #Hq, #Hw, #Hr⟩
  have key : ∀ op : TxnOp, (∀ a, op ≠ .get a) → (∀ a, op ≠ .delete a) →
      (∀ a b c, op ≠ .txn a b c) → op = txn.putTxnOp o →
      reqOpAt (GF := GF) p op = iprop(⌜p ≠ null⌝ ∗ ∃ (w r : Loc) (o' : OpFull),
        structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
          (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w :
            GoInterface) ∗
        structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
        putReqAt r o' ∗ ⌜op = txn.putTxnOp o'⌝) := by
    intro op h1 h2 h3 _
    unfold reqOpAt
    cases op with
    | get a => exact absurd rfl (h1 a)
    | delete a => exact absurd rfl (h2 a)
    | txn a b c => exact absurd rfl (h3 a b c)
    | _ => rfl
  rw [key (txn.putTxnOp o) (by intro a; unfold txn.putTxnOp; split <;> (try split) <;> simp)
    (by intro a; unfold txn.putTxnOp; split <;> (try split) <;> simp)
    (by intro a b c; unfold txn.putTxnOp; split <;> (try split) <;> simp) rfl]
  isplitl []
  · ipureintro; exact Hp
  iexists w, r, o
  iframe #
  ipureintro; rfl

/-- The deletes of a transaction's operations, at every depth (`v3rpc.delCount`'s, over the
transaction model). -/
def delCountT : List TxnOp → Nat
  | [] => 0
  | .delete _ :: us => delCountT us + 1
  | .txn _ ts es :: us => delCountT ts + delCountT es + delCountT us
  | _ :: us => delCountT us

/-- **What the decoding gives of a transaction request's deletes** (`r`, the server's copy;
persistent): each top-level delete's `RangeEnd` is `nil` or not empty (protobuf decodes an empty
`bytes` field as `nil`), and the deletes are fewer than `2 ^ 63` in each branch (each is at least
a byte of the message): `v3rpc.txnReqWire`, over the transaction model; nested transactions are
not covered (the builder's operations are plain). -/
def txnWireOk (r : Loc) (t : TxnModel) : IProp GF :=
  iprop(⌜delCountT t.thenOps < 2 ^ 63 ∧ delCountT t.elseOps < 2 ^ 63⌝ ∗
    □ ∀ (sl : GoSlice) (ps : List Loc) (i : Nat) (p w d : Loc) (esl : GoSlice),
      (structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ sl ∨
        structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ sl) -∗ sl ↦*□ ps -∗
      ⌜ps[i]? = some p⌝ -∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ d -∗
      structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" d ↦□ esl -∗
      ⌜esl = slice.nil ∨ esl.len ≠ W64 0⌝)

instance txnWireOk_persistent (r : Loc) (t : TxnModel) : Persistent (txnWireOk (GF := GF) r t) := by
  unfold txnWireOk; infer_instance

/-! ## `etcdserverpb`'s sort enumerations (unit V2) -/

/-- **The protobuf enumerations' name maps** `Op.IsSortOptionValid` looks the sort order and
target up in (`etcdserverpb.RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`:
generated `map[int32]string` literals): fixed maps whose keys are the enumerations' values, `0` to
`2` and `0` to `4`; and the error `kv.Do` returns for another sort option,
`rpctypes.ErrInvalidSortOption` (`Error(ErrGRPCInvalidSortOption)`, an `EtcdError`), a client
error that grpc's `status` accepts (`statusErrOk`). Facts of `etcdserverpb`'s and `rpctypes`' initialization, stated here as a premise of the
client's gets (the maps as the server's `v3rpc.sortNameMaps`); to be folded into the packages'
facts (`cache/v3/Base.lean`). -/
def sortNamesOk : IProp GF :=
  iprop((∃ e : GoInterface,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrInvalidSortOption ↦□ e ∗
      ⌜e ≠ GoInterface.nil ∧ clientErr e⌝ ∗ statusErrOk e ∗ errCellOk e) ∗
    (∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortOrder_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝) ∗
    (∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortTarget_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝))

instance sortNamesOk_persistent : Persistent (sortNamesOk (GF := GF)) := by
  unfold sortNamesOk; infer_instance

/-- `sortNamesOk` if the get has a sort option (`b`, its `sortSet`): a get without one never reads
the enumerations (`Op.IsSortOptionValid` returns at once). -/
def sortNamesIf (b : Bool) : IProp GF := if b then sortNamesOk else iprop(True)

instance sortNamesIf_persistent (b : Bool) : Persistent (sortNamesIf (GF := GF) b) := by
  unfold sortNamesIf; split <;> infer_instance

theorem sortNamesIf_false : ⊢ sortNamesIf (GF := GF) false := by
  unfold sortNamesIf; iintro; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

/-- **The error of a KV call** (persistent; D37): a client error (`clientErr`: a leaf, as
`errors.Is` and `errors.As` see it) that grpc's `status` accepts (`statusErrOk`) and that is no
caller's own `errors.New` value (`errCellOk`: an `*errorString` among the client's errors holds one
of `clientErrMsgs`; `errCellOk_ne`). What the client's KV results (`client_put_any`, ...) say of a
returned error; what a program needs to tell its own sentinel errors apart from the client's
(Kubernetes' storage test: `errors.Is(err, errDeleteRejected)` is `false` for the store's etcd
errors). -/
def kvErr (err : GoInterface) : IProp GF :=
  iprop(⌜clientErr err⌝ ∗ statusErrOk err ∗ errCellOk err)

instance kvErr_persistent (err : GoInterface) : Persistent (kvErr (GF := GF) err) := by
  unfold kvErr; infer_instance

/-- **A KV call's error is no caller's `errors.New(msg)` value** of a message not among the
client's (`clientErrMsgs`): the caller's error at `y` (whose cell holds `msg`, as Perennial's
`errors.New` leaves it, `errStrCell y msg`) differs from it; with `clientErr` (a leaf), so does
`errors.Is` (D37). -/
theorem kvErr_ne (err : GoInterface) (y : Loc) (msg : GoString)
    (hmsg : msg ∉ go_etcd_io.etcd.cache.v3.clientErrMsgs) :
    kvErr (GF := GF) err ⊢ y.[_root_.Perennial.errors.errorString, go!"s"] ↦□ msg -∗
      ⌜err ≠ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #y⌝ := by
  unfold kvErr
  iintro ⟨-, -, #Hcl⟩ #Hy
  iapply (go_etcd_io.etcd.cache.v3.errCellOk_ne err y msg hmsg) $$ Hcl Hy

/-- **What a unary `Put` call returns** to the client (every layer's postcondition: the stub's,
the retry client's, `kv.Do`'s at its `put` field): `nil` and a response holding a message `m`
(`putRespMsg`) with the run's knowledge `Q m`; or a client error that grpc's `status` accepts
(`statusErrOk`, unit P3a: `ContextError` passes it to `rpctypes.Error`) and no response. -/
def putCallOut (Q : PutRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err ∗ errCellOk err))

/-- **What a unary `Range` call returns** to the client (as `putCallOut`). -/
def rangeCallOut (Q : RangeRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err ∗ errCellOk err))

/-- **What a unary `DeleteRange` call returns** (as `putCallOut`; the vertical slice's unit V2). -/
def deleteCallOut (Q : DelRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : DelRespM, delRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err ∗ errCellOk err))

/-- **What a unary `Txn` call returns** (as `putCallOut`; the vertical slice's unit V2). -/
def txnCallOut (Q : TxnRespM → IProp GF) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : TxnRespM, txnRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err ∗ errCellOk err))

/-! ## The KV service's messages -/

/-- **A `*pb.PutRequest`** on the wire (see the file header). -/
def pbPutRequest : ProtoMsg GF where
  ty := etcdserverpb.PutRequest.ty
  M := OpFull
  send inp o := iprop(∃ (req : etcdserverpb.PutRequest) (k v : GoString), inp ↦ req ∗
    req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗ ⌜o = putReqOp req k v⌝)
  recv r o := txn.putRequestIs r o
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.PutRequest))
  own l := iprop(∃ v : etcdserverpb.PutRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.RangeRequest`** on the wire (see the file header). -/
def pbRangeRequest : ProtoMsg GF where
  ty := etcdserverpb.RangeRequest.ty
  M := OpFull
  send inp o := iprop(∃ (req : etcdserverpb.RangeRequest) (k e : GoString), inp ↦ req ∗
    req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗ ⌜o = rangeReqOp req k e⌝)
  recv r o := txn.rangeRequestIs r o
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.RangeRequest))
  own l := iprop(∃ v : etcdserverpb.RangeRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.PutResponse`** on the wire (see the file header). -/
def pbPutResponse : ProtoMsg GF where
  ty := etcdserverpb.PutResponse.ty
  M := PutRespM
  send := putRespMsg
  recv := putRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.PutResponse))
  own l := iprop(∃ v : etcdserverpb.PutResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.RangeResponse`** on the wire (see the file header). -/
def pbRangeResponse : ProtoMsg GF where
  ty := etcdserverpb.RangeResponse.ty
  M := RangeRespM
  send := rangeRespMsg
  recv := rangeRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.RangeResponse))
  own l := iprop(∃ v : etcdserverpb.RangeResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.DeleteRangeRequest`** on the wire (see the file header; the server's side only: the
client's `kv.Do` does not send one in this development). -/
def pbDeleteRangeRequest : ProtoMsg GF where
  ty := etcdserverpb.DeleteRangeRequest.ty
  M := OpFull
  send inp o := iprop(∃ (req : etcdserverpb.DeleteRangeRequest) (k e : GoString), inp ↦ req ∗
    req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗ ⌜o = deleteReqOp req k e⌝)
  recv r o := txn.deleteRangeRequestIs r o
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.DeleteRangeRequest))
  own l := iprop(∃ v : etcdserverpb.DeleteRangeRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.DeleteRangeResponse`** on the wire. -/
def pbDeleteRangeResponse : ProtoMsg GF where
  ty := etcdserverpb.DeleteRangeResponse.ty
  M := DelRespM
  send := delRespMsg
  recv := delRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.DeleteRangeResponse))
  own l := iprop(∃ v : etcdserverpb.DeleteRangeResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.TxnRequest`** on the wire (the vertical slice's unit V2; a trusted wire model, as
`pbPutRequest`'s): a request's model is the transaction model `t` the server reads; the sender's
message is the owned struct whose slices hold, read-only, the comparisons and the operations' wire
requests of `t` (`txnReqAt`: what the client's `txn.Commit` builds); the decoded copy denotes the
same transaction (`txn.txnRequestIs`: the txn package's model of the server's request) and is as
protobuf decodes it (`txnWireOk`: each top-level delete's `RangeEnd` `nil` or not empty, an empty
`bytes` field being decoded as `nil`; fewer than `2 ^ 63` deletes per branch, each at least a byte
of the message). -/
def pbTxnRequest : ProtoMsg GF where
  ty := etcdserverpb.TxnRequest.ty
  M := TxnModel
  send inp t := iprop(∃ req : etcdserverpb.TxnRequest, inp ↦ req ∗ txnReqAt req t)
  recv r t := iprop(txn.txnRequestIs r t ∗ txnWireOk r t)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.TxnRequest))
  own l := iprop(∃ v : etcdserverpb.TxnRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.TxnResponse`** on the wire (the vertical slice's unit V2; as `pbPutResponse`):
`txnRespMsg`, every field the wire carries (the header, `Succeeded`, the responses, nested). -/
def pbTxnResponse : ProtoMsg GF where
  ty := etcdserverpb.TxnResponse.ty
  M := TxnRespM
  send := txnRespMsg
  recv := txnRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.TxnResponse))
  own l := iprop(∃ v : etcdserverpb.TxnResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-! ## Call options -/

/-- **A `retryOption`'s closure** `f` writes only the interceptor's `options`' `retryPolicy`
(`withRepeatablePolicy`'s). -/
def retryApplyOk (f : GoFunc) : IProp GF :=
  iprop(∀ (o : Loc) (p : go_etcd_io.etcd.client.v3.retryPolicy),
    {{ structFieldRef go_etcd_io.etcd.client.v3.options go!"retryPolicy" o ↦ p }}
      (App (Val #f) (Val #o))
    {{ RET #(); ∃ p' : go_etcd_io.etcd.client.v3.retryPolicy,
        structFieldRef go_etcd_io.etcd.client.v3.options go!"retryPolicy" o ↦ p' }})

instance retryApplyOk_persistent (f : GoFunc) : Persistent (retryApplyOk (GF := GF) f) := by
  unfold retryApplyOk; infer_instance

/-- **A call option the client passes** (persistent; see the file header). -/
def callOptOk (v : GoInterface) : IProp GF :=
  iprop(⌜∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ grpcScalarOptTys⌝ ∨
    ∃ ro : go_etcd_io.etcd.client.v3.retryOption,
      ⌜v = interface.mkOk go_etcd_io.etcd.client.v3.retryOption.ty #ro⌝ ∗
      retryApplyOk ro.applyFunc')

instance callOptOk_persistent (v : GoInterface) : Persistent (callOptOk (GF := GF) v) := by
  unfold callOptOk; infer_instance

/-- Every call option of `vs` is one the client passes. -/
def callOptsOk (vs : List GoInterface) : IProp GF := iprop([∗list] v ∈ vs, callOptOk v)

instance callOptsOk_persistent (vs : List GoInterface) : Persistent (callOptsOk (GF := GF) vs) := by
  unfold callOptsOk; infer_instance

theorem callOptsOk_app (vs ws : List GoInterface) :
    callOptsOk (GF := GF) vs ∗ callOptsOk ws ⊢ callOptsOk (vs ++ ws) := by
  unfold callOptsOk
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_append.2
  isplitl [H1]
  · iexact H1
  · iexact H2

theorem callOptsOk_singleton (v : GoInterface) : callOptOk (GF := GF) v ⊢ callOptsOk [v] := by
  unfold callOptsOk
  iintro H
  iapply BigSepL.bigSepL_singleton.2
  iexact H

/-! ## The connection -/

/-- **The client's retry interceptor's contract** (persistent; unit P3a: what
`Client.unaryClientInterceptor` returns, `Client__unaryClientInterceptor.lean`): called on a
connection to `addr` (`grpcConn`, any interceptors) with an invoker making one attempt
(`grpcInvokerOk`), for a method registered at `addr` with `Spec`, the request `inp`
(`Req.send`, given back), a zero reply `out` (`Rep.blank`), the client's call options
(`callOptsOk`) and the caller's `□ ▷ Spec m Φ` (persistent: the request may be delivered several
times, the attempts), it returns
* `nil`: an attempt succeeded, the last one (the loop returns at the first `nil`), and `out` holds
  its reply's copy of a response (`Rep.recv out m'`) with its run's `Φ m'`; other attempts may
  have run the handler: an attempt that failed with a gRPC `Canceled` or `DeadlineExceeded` while
  `ctx` is not done is retried whatever the method (`issues/etcd-client-retry-put-ctx-error.md`);
* an error: a client error (`clientErr`) that grpc's `status` accepts (`statusErrOk`); nothing
  about whether, or how often, the handler ran, nor about `out`. -/
def etcdInterceptorOk (ic : GoFunc) : IProp GF :=
  iprop(□ ∀ (conn : Loc) (addr : List GoString) (ics : List GoFunc) (dopts : List GoInterface)
      (inv : GoFunc) (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep)
      (m : Req.M) (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (inp out : Loc) (opts : GoSlice)
      (vs : List GoInterface),
    {{ grpcConn conn addr ics dopts ∗ grpcInvokerOk conn addr inv ∗ isGrpcRpcs addr method Spec ∗
        □ ▷ Spec m Φ ∗ ctxOk ctx cd ∗ Req.send inp m ∗ Rep.blank out ∗
        opts ↦*□ vs ∗ callOptsOk vs }}
      (interceptorCall ic #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn inv #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err ∗ errCellOk err)) }})

instance etcdInterceptorOk_persistent (ic : GoFunc) : Persistent (etcdInterceptorOk (GF := GF) ic) := by
  unfold etcdInterceptorOk; infer_instance

/-- **Call options holding only scalars** (D29): no retry option among them (the client's own
call options, `defaultCallOpts` and the message-size options; a write's). -/
def scalarOpts (vs : List GoInterface) : Prop :=
  ∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ grpcScalarOptTys

/-- **The attempt modes of the retry interceptor's contract**: any number of attempts (a
persistent precondition), or a write that is never retried (D29: a refusal-free connection and
no retry option, so the call's policy is the default `nonRepeatable`, which the interceptor
retries only after a refusal). -/
inductive AttemptMode where
  | any
  | write
  deriving DecidableEq

/-- The request's precondition in a mode. -/
def modePre (md : AttemptMode) (method : GoString) (addr : List GoString) (vs : List GoInterface)
    (P : IProp GF) : IProp GF :=
  match md with
  | .any => iprop(□ ▷ P)
  | .write => iprop(▷ P ∗ ⌜kvMethod method ∧ (∀ a ∈ addr, noRefusalAt a) ∧ scalarOpts vs⌝)

/-- The retry interceptor's contract in a mode (D29): `etcdInterceptorOk` (`.any`),
`etcdInterceptorOkW` (`.write`). -/
def etcdInterceptorOkM (md : AttemptMode) (ic : GoFunc) : IProp GF :=
  iprop(□ ∀ (conn : Loc) (addr : List GoString) (ics : List GoFunc) (dopts : List GoInterface)
      (inv : GoFunc) (method : GoString) (Req Rep : ProtoMsg GF) (Spec : GrpcSpec Req Rep)
      (m : Req.M) (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (inp out : Loc) (opts : GoSlice)
      (vs : List GoInterface),
    {{ grpcConn conn addr ics dopts ∗ grpcInvokerOk conn addr inv ∗ isGrpcRpcs addr method Spec ∗
        modePre md method addr vs (Spec m Φ) ∗ ctxOk ctx cd ∗
        Req.send inp m ∗ Rep.blank out ∗ opts ↦*□ vs ∗ callOptsOk vs }}
      (interceptorCall ic #(GoInterface.ok ctx) #method
        #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)
        #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface) #conn inv #opts)
    {{ (err : GoInterface), RET #err; Req.send inp m ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err ∗ errCellOk err)) }})

instance etcdInterceptorOkM_persistent (md : AttemptMode) (ic : GoFunc) :
    Persistent (etcdInterceptorOkM (GF := GF) md ic) := by
  unfold etcdInterceptorOkM; infer_instance

/-- **The retry interceptor's contract for a write on a refusal-free connection** (persistent;
2026-10-21, D29): as `etcdInterceptorOk`, for the caller's ordinary `▷ Spec m Φ`, whatever the
retry bound, when every address of the connection is refusal-free (`noRefusalAt`) and the call
options hold only scalars (`scalarOpts`): the call's policy is the default `nonRepeatable`, and
the interceptor sends it again only after a refusal, which such a connection never returns. -/
def etcdInterceptorOkW (ic : GoFunc) : IProp GF := etcdInterceptorOkM .write ic

instance etcdInterceptorOkW_persistent (ic : GoFunc) :
    Persistent (etcdInterceptorOkW (GF := GF) ic) := by
  unfold etcdInterceptorOkW; infer_instance

/-- The two modes of the contract (D29). -/
theorem etcdInterceptorOkM_split (ic : GoFunc) :
    (□ ∀ md : AttemptMode, etcdInterceptorOkM (GF := GF) md ic) ⊢
      etcdInterceptorOk ic ∗ etcdInterceptorOkW ic := by
  iintro #H
  isplitl []
  · ihave #H0 := H $$ %AttemptMode.any
    unfold etcdInterceptorOkM etcdInterceptorOk
    iintro !> %conn %addr %ics %dopts %inv %method %Req %Rep %Spec %m %Φ %ctx %cd %inp %out %opts
      %vs %Ψ !> ⟨#Hgc, #Hinv, #Hrpc, #Hpre, #Hctx, Hsend, Hblank, #Hopts, #Hok⟩ HΨ
    iapply H0 $$ [Hsend Hblank] HΨ
    unfold modePre
    iframe #
    iframe
  · ihave #H2 := H $$ %AttemptMode.write
    unfold etcdInterceptorOkW
    iexact H2

/-- **An etcd client's connection `conn` to the server at `addr`** (persistent; unit P3a; see the
file header): grpc's connection with one unary interceptor, the client's retry interceptor
(`etcdInterceptorOk`), and no default call options. -/
def isEtcdConn (conn : Loc) (addr : List GoString) : IProp GF :=
  iprop(∃ ic : GoFunc, grpcConn conn addr [ic] [] ∗ etcdInterceptorOk ic ∗
    -- (2026-10-21, D29) a write on a refusal-free connection: ordinary, whatever the bound
    etcdInterceptorOkW ic)

instance isEtcdConn_persistent (conn : Loc) (addr : List GoString) :
    Persistent (isEtcdConn (GF := GF) conn addr) := by
  unfold isEtcdConn; infer_instance

/-- **A request's precondition on a connection, with the call options `vs`** (D29): persistent
(any number of attempts), or ordinary on a refusal-free connection with scalar call options (a
write, never retried). -/
def reqPre (conn : Loc) (method : GoString) (addr : List GoString) (vs : List GoInterface)
    (P : IProp GF) : IProp GF :=
  iprop(□ ▷ P ∨ (⌜kvMethod method ∧ (∀ a ∈ addr, noRefusalAt a) ∧ scalarOpts vs⌝ ∗ ▷ P))

theorem reqPre_box (conn : Loc) (method : GoString) (addr : List GoString) (vs : List GoInterface)
    (P : IProp GF) : (□ ▷ P : IProp GF) ⊢ reqPre conn method addr vs P := by
  unfold reqPre; iintro #H; ileft; iexact H

/-- Scalar options added to a call's options keep its precondition (the stubs' `StaticMethod`). -/
theorem reqPre_scalar_app (conn : Loc) (method : GoString) (addr : List GoString)
    (ws vs : List GoInterface) (P : IProp GF) (h : scalarOpts ws) :
    reqPre (GF := GF) conn method addr vs P ⊢ reqPre conn method addr (ws ++ vs) P := by
  unfold reqPre
  iintro (#H | ⟨%Hw, H⟩)
  · ileft; iexact H
  · iright; iframe H
    ipureintro
    refine ⟨Hw.1, Hw.2.1, fun v hv => ?_⟩
    rcases List.mem_append.1 hv with hv | hv
    · exact h v hv
    · exact Hw.2.2 v hv

/-! ## Context errors -/

/-- **The context `ci` (descriptor `cd`)'s `Err()` returns client errors** (persistent; see the
file header): `isContext`'s triple of `Err()` (`"#HErr"`: a non-nil error makes the context done,
`ContextClosed`, after which `Err()` is non-nil: Go's "successive calls to Err return the same
error"), with `clientErr` of the error returned, which grpc's `status` accepts (`statusErrOk`,
unit P3a: `kv.Put` passes `ContextError`'s result, possibly the context's error, to a second
`ContextError`, which passes it to `rpctypes.Error`; `context.Canceled` is an `errors.New` error,
`DeadlineExceeded` a `deadlineExceededError`, neither with a `GRPCStatus` or `Is` method). -/
def ctxErrClient (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(□ ∀ (cl : Broadcast) (Φ : val → IProp GF),
    (match cl with
     | .Done => context.ContextClosed cd.Done_gn
     | _ => iprop(True)) -∗
    ▷ (∀ err : GoInterface,
        (match cl with
         | .Done => iprop(⌜err ≠ interface.nil⌝)
         | _ => if err = interface.nil then iprop(True)
                else context.ContextClosed cd.Done_gn) -∗
        ⌜clientErr err⌝ -∗ statusErrOk err -∗ errCellOk err -∗ Φ #err) -∗
    WP (App (Val #(methods ci.ty go!"Err" ci.v)) (Val #())) {{ Φ }})

instance ctxErrClient_persistent (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    Persistent (ctxErrClient ci cd) := by
  unfold ctxErrClient; infer_instance

namespace client

/-- **Every context's `Err()` returns client errors** (a premise, persistent; `InvServerKV.lean`'s
header; moved here from there on 2026-10-18, for the lessor): `ctxErrClient` for every
`isContext`. -/
def ctxErrClientAll : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    context.isContext ctx cs -∗ ctxErrClient ctx cs)

instance ctxErrClientAll_persistent : Persistent (ctxErrClientAll (GF := GF)) := by
  unfold ctxErrClientAll; infer_instance

end client

/-! ## The objects -/

/-- **The generated stub `kc`** (`*etcdserverpb.kVClient`) on the connection `conn`. -/
def kvStubAt (kc conn : Loc) : IProp GF :=
  iprop(structFieldRef etcdserverpb.kVClient go!"cc" kc ↦□
    (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn :
      GoInterface))

instance kvStubAt_persistent (kc conn : Loc) : Persistent (kvStubAt (GF := GF) kc conn) := by
  unfold kvStubAt; infer_instance

/-- **The `*retryKVClient` `rkv`** over a stub on `conn`. -/
def retryKVAt (rkv conn : Loc) : IProp GF :=
  iprop(∃ kc : Loc, structFieldRef go_etcd_io.etcd.client.v3.retryKVClient go!"kc" rkv ↦□
      (interface.mkOk (go.GoType.PointerType etcdserverpb.kVClient.ty) #kc : GoInterface) ∗
    kvStubAt kc conn)

instance retryKVAt_persistent (rkv conn : Loc) : Persistent (retryKVAt (GF := GF) rkv conn) := by
  unfold retryKVAt; infer_instance

/-- **The call options' slice `sl`** (read-only, full: `len = cap`), each one the client passes. -/
def callOptsAt (sl : GoSlice) : IProp GF :=
  iprop(∃ vs : List GoInterface, sl ↦*□ vs ∗ ⌜sl.len = sl.cap⌝ ∗ callOptsOk vs ∗
    -- (2026-10-21, D29) scalars only: the client passes no retry option of its own
    ⌜scalarOpts vs⌝)

instance callOptsAt_persistent (sl : GoSlice) : Persistent (callOptsAt (GF := GF) sl) := by
  unfold callOptsAt; infer_instance

/-- **The `*kv` `api`** (what `NewKV` returns) over a `*retryKVClient` on a connection to the
server at `addr`. -/
def kvObjAt (api : Loc) (addr : List GoString) : IProp GF :=
  iprop(∃ (rkv conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"remote" api ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv :
        GoInterface) ∗
    retryKVAt rkv conn ∗ isEtcdConn conn addr ∗
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"callOpts" api ↦□ sl ∗ callOptsAt sl)

instance kvObjAt_persistent (api : Loc) (addr : List GoString) : Persistent (kvObjAt (GF := GF) api addr) := by
  unfold kvObjAt; infer_instance

/-- **A request's precondition on a `*kv`** (D29): persistent, or ordinary over a refusal-free
connection (a write: the `*kv` passes its client's call options, scalars, `callOptsAt`). -/
def kvReqPre (api : Loc) (addr : List GoString) (P : IProp GF) : IProp GF :=
  iprop(□ ▷ P ∨ (⌜∀ a ∈ addr, noRefusalAt a⌝ ∗ ▷ P))

theorem kvReqPre_box (api : Loc) (addr : List GoString) (P : IProp GF) :
    (□ ▷ P : IProp GF) ⊢ kvReqPre api addr P := by
  unfold kvReqPre; iintro #H; ileft; iexact H

/-- A `*kv`'s precondition is its connection's, with scalar call options. -/
theorem kvReqPre_conn (api rkv conn : Loc) (method : GoString) (hm : kvMethod method)
    (addr : List GoString) (vs : List GoInterface) (P : IProp GF) (hvs : scalarOpts vs) :
    structFieldRef go_etcd_io.etcd.client.v3.kv go!"remote" api ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv :
        GoInterface) ∗ retryKVAt rkv conn ∗ kvReqPre api addr P ⊢ reqPre conn method addr vs P := by
  iintro ⟨-, -, H⟩
  unfold kvReqPre reqPre
  icases H with (#H | ⟨%Hnr, H⟩)
  · ileft; iexact H
  · iright
    iframe H
    ipureintro; exact ⟨hm, Hnr, hvs⟩

/-- **What `NewKV` reads of the `*Client` `cl`**: its connection (to the server at `addr`) and call
options, fixed since `clientv3.New` (an assumption about the unverified constructor). -/
def clientKVAt (cl : Loc) (addr : List GoString) : IProp GF :=
  iprop(⌜cl ≠ null⌝ ∗ ∃ (conn : Loc) (sl : GoSlice),
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn ∗ isEtcdConn conn addr ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" cl ↦□ sl ∗ callOptsAt sl)

instance clientKVAt_persistent (cl : Loc) (addr : List GoString) :
    Persistent (clientKVAt (GF := GF) cl addr) := by
  unfold clientKVAt; infer_instance

end defs

end EtcdGrove
end Perennial
