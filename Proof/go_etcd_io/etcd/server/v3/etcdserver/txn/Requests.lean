/-
The server's requests and responses (`etcdserverpb`, names-only types with their fields) as
pure values: what a `*pb.RangeRequest`, `*pb.PutRequest`, `*pb.DeleteRangeRequest`,
`*pb.Compare` and `*pb.TxnRequest` denote in the client's transaction model
(`cache/v3/InvEtcdTxn.lean`: `TxnModel`, `TxnOp`, `CmpModel`, `OpFull`), and what the
responses hold. All the predicates are persistent: the server reads its requests and builds
its responses, and hands them on read-only. Lean-first; see `notes/decisions.md`, "The
server's txn: the two models meet, the sole writer as tokens".

**`OpFull` reused** for the three requests: a range request is a get's `OpFull` (`rangeOpOf`:
operation type `1`, the key, the range end, the revision, the limit, the sort, serializable,
keys-only, count-only and the four revision filters, exactly the fields `Op.toRangeRequest`
sends), a put request a put's (`putOpOf`: type `2`, key, value, lease, `PrevKv`,
`IgnoreValue`, `IgnoreLease`), a delete request a delete's (`deleteOpOf`: type `3`, key, range
end, `PrevKv`); the fields a request does not have are `OpFull.newOp`'s. So a server-side
statement is in the client's own terms (`rangeIn`, `rangeSel`, `kvFilterOk`, `rangeKvsOk`,
`effSortOrder`, `inRange`), and the model's `runTxn` applies as it is. *Rejected:* a record of
the request's fields (a second vocabulary, and a translation to `OpFull` in every statement).

**The range end** (`rangeEndOf`): the client model's `inRange key rangeEnd` reads `[]` as the
key alone and `[0]` as every key from `key` on. The server (`mkGteRange`) turns `[0]` into the
empty non-nil slice, and mvcc reads `end == nil` as the key alone and a non-nil empty `end` as
no upper bound (`treeIndex.Range`/`unsafeVisit`'s `len(end) > 0`; mvcc's `rangeAnswers` with
`endNil` and `inRange k [] _`). A request's `RangeEnd` thus denotes: `[]` if the slice is
`nil`, `[0]` if it is empty but not `nil` (no upper bound, as mvcc reads it), its contents
otherwise; on a request decoded from the wire (protobuf-go decodes an empty proto3 `bytes`
field as `nil`) the denotation is the client's. A comparison's range end is read the same way
(`applyCompare` also calls `mkGteRange`).

**Sort** (`rangeOpOf`): `sortSet` iff the order or the target is not zero (the client sends both
zero when it sets no sort); `OpFull.effSortOrder` then is the server's: no order and a target
other than the key is ascending, ascending by key is the default. Enumeration values outside
the protobuf's (a target above `VALUE`: the server panics; an order above `DESCEND`: it does not
sort) are the specs' business.

**Puts in a transaction** (`putTxnOp`): the server's put, total: `IgnoreValue` keeps the key's
value whatever `Value` is, `IgnoreLease` keeps its lease whatever `Lease` is (`put`); the
client's `txnOpOf` is partial because the client rejects the other combinations, which the
server does not see.

**Transactions** (`txnRequestIs rt t`): the comparisons (`comparesIs`, each a `compareIs`: the
client's `compareAt` with the server's range end) and the two branches' `RequestOp`s, each
(`requestOpIs`) not nil and holding in its `Request` oneof the wrapper of its operation's kind
with a non-nil request: a range (`TxnOp.get`), a put (`putTxnOp`), a delete, or a nested
transaction (`TxnOp.txn`, recursively). An empty oneof (`Request == nil`) denotes nothing:
`executeTxn` dereferences the response `newTxnResp` left `nil` for it (the gRPC layer rejects
such requests). A range in a transaction is a `TxnOp.get` whatever its `Revision`: the model's
get reads the transaction's state; a range at another revision is the specs' premise.

**Responses** (`rangeResponseIs`, `putResponseIs`, `deleteRangeResponseIs`, `txnResponseIs`):
the header (not nil) and its revision, and the fields the server sets, read-only; the key-values
as `kvIs` (the server's own copy of the cache's `kvValAt`, without the cache's assumptions).
`txnResponseIs resp rev ok ops rs` mirrors `TxnOpResult`: the `Responses` are, in order, the
responses of the chosen branch's operations `ops` with results `rs` (`responseOpIs`): a range's
key-values are its selection sorted and limited (`rangeKvsOk`), with its count; a put's and a
delete's headers and previous key-values are any (`PrevKv` is outside `TxnOpResult`); a delete
has its count; a nested transaction its own outcome and results, with a header of revision `0`
(only the outer response's revision is set). A range answered header-only
(`skipRangeExecution`) is not described here.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Base
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Proof.go_etcd_io.raft.v3.ProjSimps

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-! ## The requests, purely -/

/-- What a request's range end `RangeEnd` (the slice `sl` with contents `e`) denotes in the
client model's `inRange`: the key alone (`[]`) if `sl` is `nil`; every key from the key on
(`[0]`) if it is empty and not `nil` (as mvcc reads it, after `mkGteRange`); `[key, e)`
otherwise (`[0]` itself included: `mkGteRange` makes it the empty non-nil slice). -/
def rangeEndOf (sl : GoSlice) (e : GoString) : GoString :=
  if sl = slice.nil then [] else if e = [] then [W8 0] else e

/-- The get a `*pb.RangeRequest` with these fields denotes (`re`: its `rangeEndOf`). -/
def rangeOpOf (key re : GoString) (rev limit : w64) (order target : w32)
    (serializable keysOnly countOnly : Bool) (minMod maxMod minCreate maxCreate : w64) : OpFull :=
  { OpFull.newOp with
    base := { OpModel.zero with
      countOnly := countOnly, sortSet := decide (order ≠ W32 0 ∨ target ≠ W32 0), limit := limit,
      minModRev := minMod, maxModRev := maxMod, minCreateRev := minCreate,
      maxCreateRev := maxCreate, rangeEnd := re, rev := rev, serializable := serializable },
    t := W64 1, key := key, keysOnly := keysOnly, rangeEndSet := decide (re ≠ []),
    sortTarget := W64 (sint.Z target), sortOrder := W64 (sint.Z order) }

/-- The put a `*pb.PutRequest` with these fields denotes. -/
def putOpOf (key value : GoString) (lease : w64) (prevKv ignoreValue ignoreLease : Bool) :
    OpFull :=
  { OpFull.newOp with
    base := { OpModel.zero with prevKV := prevKv },
    t := W64 2, key := key, val := value, leaseID := lease, ignoreValue := ignoreValue,
    ignoreLease := ignoreLease }

/-- The delete a `*pb.DeleteRangeRequest` with these fields denotes (`re`: its `rangeEndOf`). -/
def deleteOpOf (key re : GoString) (prevKv : Bool) : OpFull :=
  { OpFull.newOp with
    base := { OpModel.zero with prevKV := prevKv, rangeEnd := re },
    t := W64 3, key := key, rangeEndSet := decide (re ≠ []) }

proj_simps Perennial.EtcdGrove.txn.rangeOpOf Perennial.EtcdGrove.txn.putOpOf
  Perennial.EtcdGrove.txn.deleteOpOf

/-- **The server's put** (`put`, total): `IgnoreValue` keeps the key's value, `IgnoreLease` its
lease, whatever the request's value and lease are. -/
def putTxnOp (o : OpFull) : TxnOp :=
  if o.ignoreValue then .putIgnVal o.key (if o.ignoreLease then none else some o.leaseID)
  else if o.ignoreLease then .putKeep o.key o.val
  else .put o.key o.val o.leaseID

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The requests in the heap -/

/-- The `*pb.RangeRequest` `r` (not nil) denotes the get `o`: its fields, read-only. -/
def rangeRequestIs (r : Loc) (o : OpFull) : IProp GF :=
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
    ⌜o = rangeOpOf k (rangeEndOf esl e) rev limit order target ser ko co minM maxM minC maxC⌝)

instance rangeRequestIs_persistent (r : Loc) (o : OpFull) :
    Persistent (rangeRequestIs (GF := GF) r o) := by
  unfold rangeRequestIs; infer_instance

/-- The `*pb.PutRequest` `p` (not nil) denotes the put `o`: its fields, read-only. Its size
cache (`sizeCache`, which `proto.Size` stores atomically) is in an invariant
(`putSizeCacheInv`), so that `proto.Size(p)` keeps the request persistent. -/
def putRequestIs (p : Loc) (o : OpFull) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ (ksl vsl : GoSlice) (k v : GoString) (lease : w64) (pk iv il : Bool),
    structFieldRef etcdserverpb.PutRequest go!"Key" p ↦□ ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.PutRequest go!"Value" p ↦□ vsl ∗ vsl ↦*□ v ∗
    structFieldRef etcdserverpb.PutRequest go!"Lease" p ↦□ lease ∗
    structFieldRef etcdserverpb.PutRequest go!"PrevKv" p ↦□ pk ∗
    structFieldRef etcdserverpb.PutRequest go!"IgnoreValue" p ↦□ iv ∗
    structFieldRef etcdserverpb.PutRequest go!"IgnoreLease" p ↦□ il ∗
    inv (nroot .@ "txn.putSizeCache")
      (∃ sc : w32, structFieldRef etcdserverpb.PutRequest go!"sizeCache" p ↦ sc) ∗
    ⌜o = putOpOf k v lease pk iv il⌝)

instance putRequestIs_persistent (p : Loc) (o : OpFull) :
    Persistent (putRequestIs (GF := GF) p o) := by
  unfold putRequestIs; infer_instance

/-- The `*pb.DeleteRangeRequest` `d` (not nil) denotes the delete `o`: its fields,
read-only. -/
def deleteRangeRequestIs (d : Loc) (o : OpFull) : IProp GF :=
  iprop(⌜d ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (k e : GoString) (pk : Bool),
    structFieldRef etcdserverpb.DeleteRangeRequest go!"Key" d ↦□ ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" d ↦□ esl ∗ esl ↦*□ e ∗
    structFieldRef etcdserverpb.DeleteRangeRequest go!"PrevKv" d ↦□ pk ∗
    ⌜o = deleteOpOf k (rangeEndOf esl e) pk⌝)

instance deleteRangeRequestIs_persistent (d : Loc) (o : OpFull) :
    Persistent (deleteRangeRequestIs (GF := GF) d o) := by
  unfold deleteRangeRequestIs; infer_instance

/-- The `*pb.Compare` `c` (not nil) denotes the comparison `cm`: the client's `compareAt`
(the target, the operator, the key, the operand), with the range end as the server reads it
(`rangeEndOf`). Comparisons with a target or an operator outside the protobuf's enumeration, or
an operand of another target's type, denote nothing. -/
def compareIs (c : Loc) (cm : CmpModel) : IProp GF :=
  iprop(⌜c ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (e : GoString) (u : GoInterface),
    structFieldRef etcdserverpb.Compare go!"Result" c ↦□ cm.op.code ∗
    structFieldRef etcdserverpb.Compare go!"Target" c ↦□ cm.target.code ∗
    structFieldRef etcdserverpb.Compare go!"Key" c ↦□ ksl ∗ ksl ↦*□ cm.key ∗
    structFieldRef etcdserverpb.Compare go!"RangeEnd" c ↦□ esl ∗ esl ↦*□ e ∗
    ⌜cm.rangeEnd = rangeEndOf esl e⌝ ∗
    structFieldRef etcdserverpb.Compare go!"TargetUnion" c ↦□ u ∗ compareUnionAt u cm)

instance compareIs_persistent (c : Loc) (cm : CmpModel) :
    Persistent (compareIs (GF := GF) c cm) := by
  unfold compareIs; infer_instance

/-- The `*pb.Compare`s `ps` denote, in order, the comparisons `cms`. -/
def comparesIs (ps : List Loc) (cms : List CmpModel) : IProp GF :=
  iprop(⌜ps.length = cms.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (cm : CmpModel), ⌜ps[i]? = some p⌝ -∗ ⌜cms[i]? = some cm⌝ -∗
      compareIs p cm)

instance comparesIs_persistent (ps : List Loc) (cms : List CmpModel) :
    Persistent (comparesIs (GF := GF) ps cms) := by
  unfold comparesIs; infer_instance

mutual
/-- **The `*pb.RequestOp` `p` denotes the operation `op`** (read-only): not nil, its `Request`
oneof the wrapper of the operation's kind, holding a non-nil request that denotes it; a nested
transaction recursively (`txnFieldsIs`). -/
def requestOpIs (p : Loc) : TxnOp → IProp GF
  | .txn cs ts es => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r ∗ ⌜r ≠ null⌝ ∗
      ∃ (csl ssl fsl : GoSlice) (cps sps fps : List Loc),
        structFieldRef etcdserverpb.TxnRequest go!"Compare" r ↦□ csl ∗ csl ↦*□ cps ∗
        comparesIs cps cs ∗
        structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ ssl ∗ ssl ↦*□ sps ∗
        requestOpsIs sps ts ∗
        structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ fsl ∗ fsl ↦*□ fps ∗
        requestOpsIs fps es))
  | op => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (u : GoInterface) (w r : Loc) (o : OpFull),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□ u ∗
      ((⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w ∧
          op = .get o⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
        rangeRequestIs r o) ∨
       (⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w ∧
          op = putTxnOp o⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
        putRequestIs r o) ∨
       (⌜u = interface.mkOk
            (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w ∧
          op = .delete o⌝ ∗
        structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
        deleteRangeRequestIs r o))))

/-- The `*pb.RequestOp`s `ps` denote, in order, the operations `ops`. -/
def requestOpsIs : List Loc → List TxnOp → IProp GF
  | [], [] => iprop(True)
  | p :: ps, op :: ops => iprop(requestOpIs p op ∗ requestOpsIs ps ops)
  | _, _ => iprop(False)

end

/-- The fields of the `*pb.TxnRequest` `r` (read-only): its comparisons denote `cs`, its
`Success` and `Failure` operations `ts` and `es`. -/
def txnFieldsIs (r : Loc) (cs : List CmpModel) (ts es : List TxnOp) : IProp GF :=
  iprop(∃ (csl ssl fsl : GoSlice) (cps sps fps : List Loc),
    structFieldRef etcdserverpb.TxnRequest go!"Compare" r ↦□ csl ∗ csl ↦*□ cps ∗
    comparesIs cps cs ∗
    structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ ssl ∗ ssl ↦*□ sps ∗
    requestOpsIs sps ts ∗
    structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ fsl ∗ fsl ↦*□ fps ∗
    requestOpsIs fps es)
instance requestOpIs_persistent (p : Loc) (op : TxnOp) :
    Persistent (requestOpIs (GF := GF) p op) := by
  cases op <;> unfold requestOpIs <;> infer_instance

instance requestOpsIs_persistent (ps : List Loc) (ops : List TxnOp) :
    Persistent (requestOpsIs (GF := GF) ps ops) := by
  induction ops generalizing ps with
  | nil => cases ps <;> unfold requestOpsIs <;> infer_instance
  | cons op ops ih => cases ps <;> unfold requestOpsIs <;> infer_instance

instance txnFieldsIs_persistent (r : Loc) (cs : List CmpModel) (ts es : List TxnOp) :
    Persistent (txnFieldsIs (GF := GF) r cs ts es) := by
  unfold txnFieldsIs; infer_instance

/-- **The `*pb.TxnRequest` `rt` denotes the transaction `t`** (read-only; not nil). -/
def txnRequestIs (rt : Loc) (t : TxnModel) : IProp GF :=
  iprop(⌜rt ≠ null⌝ ∗ txnFieldsIs rt t.cmps t.thenOps t.elseOps)

instance txnRequestIs_persistent (rt : Loc) (t : TxnModel) :
    Persistent (txnRequestIs (GF := GF) rt t) := by
  unfold txnRequestIs; infer_instance

/-! ## The responses -/

/-- The `*mvccpb.KeyValue` `l` holds `v` (its fields, read-only; as the cache's `kvValAt`). -/
def kvIs (l : Loc) (v : EtcdKv) : IProp GF :=
  iprop(∃ keySl valSl : GoSlice,
    structFieldRef mvccpb.KeyValue go!"Key" l ↦□ keySl ∗ keySl ↦*□ v.key ∗
    structFieldRef mvccpb.KeyValue go!"CreateRevision" l ↦□ v.createRev ∗
    structFieldRef mvccpb.KeyValue go!"ModRevision" l ↦□ v.modRev ∗
    structFieldRef mvccpb.KeyValue go!"Version" l ↦□ v.version ∗
    structFieldRef mvccpb.KeyValue go!"Value" l ↦□ valSl ∗ valSl ↦*□ v.value ∗
    structFieldRef mvccpb.KeyValue go!"Lease" l ↦□ v.lease)

instance kvIs_persistent (l : Loc) (v : EtcdKv) : Persistent (kvIs (GF := GF) l v) := by
  unfold kvIs; infer_instance

/-- The `*mvccpb.KeyValue`s `ps` hold, in order, the key-values `kvs` (read-only). -/
def kvsIs (ps : List Loc) (kvs : List EtcdKv) : IProp GF :=
  iprop(⌜ps.length = kvs.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (v : EtcdKv), ⌜ps[i]? = some p⌝ -∗ ⌜kvs[i]? = some v⌝ -∗ kvIs p v)

instance kvsIs_persistent (ps : List Loc) (kvs : List EtcdKv) :
    Persistent (kvsIs (GF := GF) ps kvs) := by
  unfold kvsIs; infer_instance

/-- **The `*pb.RangeResponse` `resp`** (not nil, read-only): header revision `rev`, the
key-values `kvs`, `More`, `Count`. -/
def rangeResponseIs (resp : Loc) (rev : w64) (kvs : List EtcdKv) (more : Bool) (count : w64) :
    IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ h ∗ ⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" resp ↦□ sl ∗ sl ↦*□ ps ∗ kvsIs ps kvs ∗
    structFieldRef etcdserverpb.RangeResponse go!"More" resp ↦□ more ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" resp ↦□ count)

instance rangeResponseIs_persistent (resp : Loc) (rev : w64) (kvs : List EtcdKv) (more : Bool)
    (count : w64) : Persistent (rangeResponseIs (GF := GF) resp rev kvs more count) := by
  unfold rangeResponseIs; infer_instance

/-- **The `*pb.PutResponse` `resp`** (not nil, read-only): header revision `rev`, and the
previous key-value `prev` (`PrevKv`: nil for `none`). -/
def putResponseIs (resp : Loc) (rev : w64) (prev : Option EtcdKv) : IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ ∃ (h pk : Loc),
    structFieldRef etcdserverpb.PutResponse go!"Header" resp ↦□ h ∗ ⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.PutResponse go!"PrevKv" resp ↦□ pk ∗
    match prev with
    | none => iprop(⌜pk = null⌝)
    | some v => iprop(⌜pk ≠ null⌝ ∗ kvIs pk v))

instance putResponseIs_persistent (resp : Loc) (rev : w64) (prev : Option EtcdKv) :
    Persistent (putResponseIs (GF := GF) resp rev prev) := by
  unfold putResponseIs; cases prev <;> infer_instance

/-- **The `*pb.DeleteRangeResponse` `resp`** (not nil, read-only): header revision `rev`,
`Deleted` the number `n`, the previous key-values `prevs` (`PrevKvs`). -/
def deleteRangeResponseIs (resp : Loc) (rev : w64) (n : Nat) (prevs : List EtcdKv) :
    IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp ↦□ h ∗ ⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" resp ↦□ W64 (n : Int) ∗
    structFieldRef etcdserverpb.DeleteRangeResponse go!"PrevKvs" resp ↦□ sl ∗ sl ↦*□ ps ∗
    kvsIs ps prevs)

instance deleteRangeResponseIs_persistent (resp : Loc) (rev : w64) (n : Nat)
    (prevs : List EtcdKv) : Persistent (deleteRangeResponseIs (GF := GF) resp rev n prevs) := by
  unfold deleteRangeResponseIs; infer_instance

mutual
/-- **The `*pb.ResponseOp` `p` is the response of the operation `op` with result `res`**
(read-only): not nil, its `Response` oneof the wrapper of the operation's kind, holding a
non-nil response: a range's key-values are its selection sorted and limited as requested
(`rangeKvsOk`), its count the result's; a put's response any (`PrevKv` is outside the model);
a delete's count the result's; a nested transaction's outcome and results the result's,
recursively (its fields as `txnRespFieldsIs`'s), with header revision `0`. -/
def responseOpIs (p : Loc) : TxnOp → TxnOpResult → IProp GF
  | .txn _ ts es, .txn ok rs => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ r ∗
      ⌜r ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.TxnResponse go!"Header" r ↦□ h ∗ ⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ (W64 0 : w64) ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" r ↦□ ok ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" r ↦□ sl ∗ sl ↦*□ ps ∗
      match ok with
      | true => responseOpsIs ps ts rs
      | false => responseOpsIs ps es rs))
  | op, res => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (u : GoInterface) (w r : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□ u ∗
      match op, res with
      | .get o, .range sel n => iprop(
          ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty)
            #w⌝ ∗
          structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ r ∗
          ∃ (rev : w64) (kvs : List EtcdKv) (more : Bool),
            rangeResponseIs r rev kvs more (W64 (n : Int)) ∗ ⌜rangeKvsOk o sel kvs⌝)
      | .put _ _ _, .put | .putKeep _ _, .put | .putIgnVal _ _, .put => iprop(
          ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty)
            #w⌝ ∗
          structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ r ∗
          ∃ (rev : w64) (prev : Option EtcdKv), putResponseIs r rev prev)
      | .delete _, .delete n => iprop(
          ⌜u = interface.mkOk
            (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w⌝ ∗
          structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w
            ↦□ r ∗
          ∃ (rev : w64) (prevs : List EtcdKv), deleteRangeResponseIs r rev n prevs)
      | _, _ => iprop(False)))

/-- The `*pb.ResponseOp`s `ps` are, in order, the responses of `ops` with results `rs`. -/
def responseOpsIs : List Loc → List TxnOp → List TxnOpResult → IProp GF
  | [], [], [] => iprop(True)
  | p :: ps, op :: ops, res :: rs => iprop(responseOpIs p op res ∗ responseOpsIs ps ops rs)
  | _, _, _ => iprop(False)

end

/-- The fields of the `*pb.TxnResponse` `resp` (read-only): header revision `rev`,
`Succeeded` is `ok`, and its `Responses` are those of the chosen branch's `ops` with results
`rs`. -/
def txnRespFieldsIs (resp : Loc) (rev : w64) (ok : Bool) (ops : List TxnOp)
    (rs : List TxnOpResult) : IProp GF :=
  iprop(∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ h ∗ ⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rev ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦□ ok ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
    responseOpsIs ps ops rs)
instance responseOpIs_persistent (p : Loc) (op : TxnOp) (res : TxnOpResult) :
    Persistent (responseOpIs (GF := GF) p op res) := by
  cases op <;> cases res <;> unfold responseOpIs <;> infer_instance

instance responseOpsIs_persistent (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult) :
    Persistent (responseOpsIs (GF := GF) ps ops rs) := by
  induction ops generalizing ps rs with
  | nil => cases ps <;> cases rs <;> unfold responseOpsIs <;> infer_instance
  | cons op ops ih => cases ps <;> cases rs <;> unfold responseOpsIs <;> infer_instance

instance txnRespFieldsIs_persistent (resp : Loc) (rev : w64) (ok : Bool) (ops : List TxnOp)
    (rs : List TxnOpResult) : Persistent (txnRespFieldsIs (GF := GF) resp rev ok ops rs) := by
  unfold txnRespFieldsIs; infer_instance

/-- **The `*pb.TxnResponse` `resp`** of the transaction `t` (not nil, read-only): header
revision `rev`, `Succeeded` is `ok`, and its responses are those of the branch `ok` chooses
with results `rs` (`TxnOpResult`, as `runTxn`'s). -/
def txnResponseIs (resp : Loc) (rev : w64) (t : TxnModel) (ok : Bool) (rs : List TxnOpResult) :
    IProp GF :=
  iprop(⌜resp ≠ null⌝ ∗ txnRespFieldsIs resp rev ok (t.branch ok) rs)

instance txnResponseIs_persistent (resp : Loc) (rev : w64) (t : TxnModel) (ok : Bool)
    (rs : List TxnOpResult) : Persistent (txnResponseIs (GF := GF) resp rev t ok rs) := by
  unfold txnResponseIs; infer_instance

end defs

end txn
end EtcdGrove
end Perennial
