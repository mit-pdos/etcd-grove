/-
The etcd model, continued: nested transactions and owned responses (Lean-first, no Rocq
counterpart), for `client/v3/leasing`. See `decisions.md`, "Leasing: nested transactions, owned
responses, `isLeasingKV`".

**Nested operations** (`OpT`): an `Op` value is either a plain operation (`OpT.leaf o`, its
`OpFull` model `o`, not a transaction) or a nested transaction (`OpT.txn o cmps thn els`:
`OpTxn(cmps, thenOps, elseOps)`, whose `Op` has the type `tTxn` and the three lists). `opTAtC c v
t` says that the `Op` value `v` is the tree `t` (its lists read-only; with `c = true`, also the
spare capacity of every nested `thenOps` slice, owned: `gatherOps` appends `elseOps` into it).
`OpT.txnOp` is the `TxnOp` a tree stands for (`TxnOp.txn` for a nested transaction, `txnOpOf` for
a leaf), `OpT.leaves` the plain operations in order (`gatherOps`), `OpT.chosen` those of the
branches a transaction's results chose (`gatherResponseOps`).

**Nested responses** (`txnOpRespN`, read-only): a nested transaction's `*pb.ResponseOp` wraps a
`*pb.TxnResponse` with its `Succeeded` and its chosen branch's responses, recursively; a plain
operation's is `txnOpRespAt`'s.

**Owned responses** (`txnCommitResultO`): what the client's `Commit()` returns is an error
(`clientErr`: a leaf of an error tree, as `errors.As` needs) or a fresh message
(protobuf decodes it from the gRPC reply), which the caller owns: the transaction's `Succeeded`,
and the top-level operations' responses (a range response's header, key-values, `More` and
`Count`; a put's, delete's or nested transaction's header) are owned; the rest is read-only. The
leasing KV writes these fields (`resp.Succeeded = ...`, `getResp.Header = resp.Header`) and caches
a range response. The response header carries all five fields (`hdrFull`, read-only).

**The builder with nested operations** (`isEtcdTxnKVO`): as `isEtcdTxnKV`, but `Then`/`Else` take
operation trees (`opsTAt`, with `OpT.txnOps`) and `Commit` returns `txnCommitResultO`.

**`Do`** (`isEtcdDoKV`): `kv.Do(ctx, op)` of a get answers as `kv.Get` does (`kvGetResult`), in
the `OpResponse`'s `get` field.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Perennial.Proof.errors
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Headers and key-values -/

section model
variable [ext : FfiSyntax]

/-- A `*pb.ResponseHeader`'s fields (what `copyHeader` copies). -/
structure HdrM where
  clusterId : w64
  memberId : w64
  revision : w64
  raftTerm : w64
  leaderId : w64
  deriving DecidableEq

/-- A `*mvccpb.KeyValue` of a response the caller owns: its location, its `Key` and `Value` slices
(whose contents are read-only) and its contents. -/
structure CachedKv where
  p : Loc
  keySl : GoSlice
  valSl : GoSlice
  kv : EtcdKv

end model

section clientErr
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- **An error etcd's client returns** (a gRPC status error, an `rpctypes.EtcdError`, a context
error): a leaf of an error tree, without `Unwrap` or `As` methods (`errors.isLeafError`), whose
value, if its dynamic type is `rpctypes.EtcdError`, is an `EtcdError` (Go's typing, which the model
lacks: `errors.AsTypeTyped`); and `rpctypes.EtcdError` implements `error` (its method set has
`Error() string`, `func (e EtcdError) Error() string`: `errors.AsTarget`, a method-set fact, which
the model also lacks, since method sets are uninterpreted). What `errors.As(err, &serverErr)`
needs (`leasingKV.acquire`, `errors.wp_As`: Go's `As` panics for a target whose element type is
neither an interface nor implements `error`). -/
def clientErr (err : GoInterface) : Prop :=
  errors.AsTarget v3rpc.rpctypes.EtcdError.ty ∧
  ∀ ii, err = GoInterface.ok ii → errors.isLeafError ii ∧
    errors.AsTypeTyped v3rpc.rpctypes.EtcdError v3rpc.rpctypes.EtcdError.ty ii

end clientErr

/-! ## Nested operations -/

/-- An `Op` as a tree: a plain operation with its `OpFull` model (not a transaction), or a nested
transaction `OpTxn(cmps, thn, els)` (its `Op`'s own model `o`, of type `tTxn`). -/
inductive OpT where
  | leaf (o : OpFull)
  | txn (o : OpFull) (cmps : List CmpModel) (thn els : List OpT)

/-- The `OpFull` model of the tree's own `Op`. -/
def OpT.top : OpT → OpFull
  | .leaf o => o
  | .txn o _ _ _ => o

mutual
/-- The transaction operation a tree stands for (`none` if some leaf is not one a transaction can
run, `txnOpOf`). -/
def OpT.txnOp : OpT → Option TxnOp
  | .leaf o => txnOpOf o
  | .txn _ cs ts es =>
    match OpT.txnOps ts, OpT.txnOps es with
    | some a, some b => some (.txn cs a b)
    | _, _ => none

/-- The transaction operations of a list of trees. -/
def OpT.txnOps : List OpT → Option (List TxnOp)
  | [] => some []
  | t :: ts =>
    match t.txnOp, OpT.txnOps ts with
    | some a, some b => some (a :: b)
    | _, _ => none
end

mutual
/-- The plain operations of a tree, in order (a transaction's then-operations, then its
else-operations: `gatherOps`). -/
def OpT.leaves : OpT → List OpFull
  | .leaf o => [o]
  | .txn _ _ ts es => OpT.leavesL ts ++ OpT.leavesL es

/-- The plain operations of a list of trees, in order. -/
def OpT.leavesL : List OpT → List OpFull
  | [] => []
  | t :: ts => t.leaves ++ OpT.leavesL ts
end

mutual
/-- The plain operations of a tree that ran, given its result (`gatherResponseOps`): a leaf, or the
chosen branch's. -/
def OpT.chosen : OpT → TxnOpResult → List OpFull
  | .leaf o, _ => [o]
  | .txn _ _ ts es, .txn ok rs =>
    match ok with
    | true => OpT.chosenL ts rs
    | false => OpT.chosenL es rs
  | .txn _ _ _ _, _ => []

/-- The plain operations that ran of a list of trees with their results (in order). -/
def OpT.chosenL : List OpT → List TxnOpResult → List OpFull
  | [], _ => []
  | _ :: _, [] => []
  | t :: ts, r :: rs => t.chosen r ++ OpT.chosenL ts rs
end

theorem txnOpOf_t {o : OpFull} {op : TxnOp} (h : txnOpOf o = some op) : o.t ≠ W64 4 := by
  intro ht
  simp [txnOpOf, ht] at h

theorem txnOps_leaves (os : List OpFull) (ops : List TxnOp) (h : os.map txnOpOf = ops.map some) :
    OpT.txnOps (os.map OpT.leaf) = some ops := by
  induction os generalizing ops with
  | nil =>
    cases ops with
    | nil => rfl
    | cons _ _ => simp at h
  | cons o os ih =>
    cases ops with
    | nil => simp at h
    | cons op ops =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      simp [OpT.txnOps, OpT.txnOp, h1, ih ops h2]

theorem leavesL_leaves (os : List OpFull) : OpT.leavesL (os.map OpT.leaf) = os := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [OpT.leavesL, OpT.leaves, ih]

mutual
/-- Every operation is under the empty prefix (every key is). -/
theorem TxnOp.under_nil : ∀ op : TxnOp, op.Under []
  | .get _ => fun _ _ => List.nil_prefix
  | .put _ _ _ => List.nil_prefix
  | .delete _ => fun _ _ => List.nil_prefix
  | .putKeep _ _ => List.nil_prefix
  | .putIgnVal _ _ => List.nil_prefix
  | .txn _ ts es => ⟨fun _ _ _ _ => List.nil_prefix, TxnOp.underL_nil ts, TxnOp.underL_nil es⟩

theorem TxnOp.underL_nil : ∀ ops : List TxnOp, TxnOp.UnderL [] ops
  | [] => trivial
  | op :: ops => ⟨TxnOp.under_nil op, TxnOp.underL_nil ops⟩
end

/-- Every transaction is under the empty prefix: the leasing KV's contracts are at prefix `[]`. -/
theorem TxnModel.under_nil (t : TxnModel) : t.Under [] :=
  ⟨fun _ _ _ _ => List.nil_prefix, fun op _ => TxnOp.under_nil op, fun op _ => TxnOp.under_nil op⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]

/-! ## Headers and owned key-values -/

/-- The `*pb.ResponseHeader` `h` (not nil) holds the fields `m`, read-only (a header is shared:
the leasing cache's latest header and its entries' responses point to the ones the client
returned). -/
def hdrFull (h : Loc) (m : HdrM) : IProp GF :=
  iprop(⌜h ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"ClusterId" h ↦□ m.clusterId ∗
    structFieldRef etcdserverpb.ResponseHeader go!"MemberId" h ↦□ m.memberId ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ m.revision ∗
    structFieldRef etcdserverpb.ResponseHeader go!"RaftTerm" h ↦□ m.raftTerm ∗
    structFieldRef etcdserverpb.ResponseHeader go!"LeaderId" h ↦□ m.leaderId)

instance hdrFull_persistent (h : Loc) (m : HdrM) : Persistent (hdrFull (GF := GF) h m) := by
  unfold hdrFull; infer_instance

/-- The fields of a `*mvccpb.KeyValue` (not nil), with fraction `dq` (the contents of its `Key` and
`Value` slices read-only). -/
def cachedKvOwn (c : CachedKv) (dq : DFrac) : IProp GF :=
  iprop(⌜c.p ≠ null⌝ ∗ structFieldRef mvccpb.KeyValue go!"Key" c.p ↦{dq} c.keySl ∗ c.keySl ↦*□ c.kv.key ∗
    structFieldRef mvccpb.KeyValue go!"CreateRevision" c.p ↦{dq} c.kv.createRev ∗
    structFieldRef mvccpb.KeyValue go!"ModRevision" c.p ↦{dq} c.kv.modRev ∗
    structFieldRef mvccpb.KeyValue go!"Version" c.p ↦{dq} c.kv.version ∗
    structFieldRef mvccpb.KeyValue go!"Value" c.p ↦{dq} c.valSl ∗ c.valSl ↦*□ c.kv.value ∗
    structFieldRef mvccpb.KeyValue go!"Lease" c.p ↦{dq} c.kv.lease)

instance cachedKvOwn_dfractional (c : CachedKv) :
    DFractional (fun dq => cachedKvOwn (GF := GF) c dq) := by
  unfold cachedKvOwn; infer_instance

/-! ## Nested operations, as `Op` values -/

mutual
/-- **The `Op` value `v` is the tree `t`** (see the module docstring): its `OpFull` model, and for
a nested transaction its comparisons and its two lists (read-only), each element the subtree;
with `c = true`, also the spare capacity of the `thenOps` slice (owned). -/
def opTAtC (c : Bool) (v : go_etcd_io.etcd.client.v3.Op) : OpT → IProp GF
  | .leaf o => iprop(opFullAt v o ∗ ⌜o.t ≠ W64 4⌝)
  | .txn o cs ts es => iprop(opFullAt v o ∗ ⌜o.t = W64 4⌝ ∗ cmpsAt v.cmps' cs ∗
      ∃ (tvs evs : List go_etcd_io.etcd.client.v3.Op), v.thenOps' ↦*□ tvs ∗ v.elseOps' ↦*□ evs ∗
        (if c then ownSliceCap go_etcd_io.etcd.client.v3.Op v.thenOps' (DFrac.own 1)
         else iprop(True)) ∗
        opListAtC c tvs ts ∗ opListAtC c evs es)

/-- The `Op` values `vs` are the trees `ts`, in order. -/
def opListAtC (c : Bool) : List go_etcd_io.etcd.client.v3.Op → List OpT → IProp GF
  | [], [] => iprop(True)
  | v :: vs, t :: ts => iprop(opTAtC c v t ∗ opListAtC c vs ts)
  | _, _ => iprop(False)
end

mutual
theorem opTAtC_false_persistent (v : go_etcd_io.etcd.client.v3.Op) :
    ∀ t : OpT, Persistent (opTAtC (GF := GF) false v t)
  | .leaf o => by unfold opTAtC; infer_instance
  | .txn o cs ts es => by
    haveI : ∀ vs, Persistent (opListAtC (GF := GF) false vs ts) :=
      fun vs => opListAtC_false_persistent vs ts
    haveI : ∀ vs, Persistent (opListAtC (GF := GF) false vs es) :=
      fun vs => opListAtC_false_persistent vs es
    unfold opTAtC
    simp only [Bool.false_eq_true, ↓reduceIte]
    infer_instance

theorem opListAtC_false_persistent :
    ∀ (vs : List go_etcd_io.etcd.client.v3.Op) (ts : List OpT),
      Persistent (opListAtC (GF := GF) false vs ts)
  | [], [] => by unfold opListAtC; infer_instance
  | v :: vs, t :: ts => by
    haveI := opTAtC_false_persistent v t
    haveI := opListAtC_false_persistent vs ts
    unfold opListAtC; infer_instance
  | [], _ :: _ => by unfold opListAtC; infer_instance
  | _ :: _, [] => by unfold opListAtC; infer_instance
end

instance opTAtC_persistent (v : go_etcd_io.etcd.client.v3.Op) (t : OpT) :
    Persistent (opTAtC (GF := GF) false v t) := opTAtC_false_persistent v t

instance opListAtC_persistent (vs : List go_etcd_io.etcd.client.v3.Op) (ts : List OpT) :
    Persistent (opListAtC (GF := GF) false vs ts) := opListAtC_false_persistent vs ts

/-- The `[]Op` slice `sl` (read-only) holds the operation trees `ts`, in order. -/
def opsTAt (sl : GoSlice) (ts : List OpT) : IProp GF :=
  iprop(∃ vs : List go_etcd_io.etcd.client.v3.Op, sl ↦*□ vs ∗ opListAtC false vs ts)

instance opsTAt_persistent (sl : GoSlice) (ts : List OpT) : Persistent (opsTAt (GF := GF) sl ts) := by
  unfold opsTAt; infer_instance

/-! ## Nested responses, read-only -/

mutual
/-- **The `*pb.ResponseOp` `p` is the response of the operation `op` with result `res`**
(read-only), nested transactions included: a plain operation's is `txnOpRespAt`'s; a nested
transaction's wraps a `*pb.TxnResponse` with its `Succeeded` and its chosen branch's responses. -/
def txnOpRespN (p : Loc) : TxnOp → TxnOpResult → IProp GF
  | .get o, res => txnOpRespAt p (.get o) res
  | .put k v l, res => txnOpRespAt p (.put k v l) res
  | .delete o, res => txnOpRespAt p (.delete o) res
  | .putKeep k v, res => txnOpRespAt p (.putKeep k v) res
  | .putIgnVal k l, res => txnOpRespAt p (.putIgnVal k l) res
  | .txn _ ts es, .txn ok rs => iprop(⌜p ≠ null⌝ ∗ ∃ (w tr : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ tr ∗ ⌜tr ≠ null⌝ ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" tr ↦□ ok ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" tr ↦□ sl ∗ sl ↦*□ ps ∗
      (match ok with
       | true => txnOpsRespN ps ts rs
       | false => txnOpsRespN ps es rs))
  | .txn _ _ _, _ => iprop(False)

/-- The responses `ps` of the operations `ops` with results `rs`, in order (read-only). -/
def txnOpsRespN : List Loc → List TxnOp → List TxnOpResult → IProp GF
  | [], [], [] => iprop(True)
  | p :: ps, op :: ops, r :: rs => iprop(txnOpRespN p op r ∗ txnOpsRespN ps ops rs)
  | _, _, _ => iprop(False)
end

mutual
theorem txnOpRespN_persistent' (p : Loc) :
    ∀ (op : TxnOp) (res : TxnOpResult), Persistent (txnOpRespN (GF := GF) p op res)
  | .get o, res => by unfold txnOpRespN; infer_instance
  | .put k v l, res => by unfold txnOpRespN; infer_instance
  | .delete o, res => by unfold txnOpRespN; infer_instance
  | .putKeep k v, res => by unfold txnOpRespN; infer_instance
  | .putIgnVal k l, res => by unfold txnOpRespN; infer_instance
  | .txn _ ts es, .txn ok rs => by
    haveI : ∀ ps, Persistent (txnOpsRespN (GF := GF) ps ts rs) :=
      fun ps => txnOpsRespN_persistent' ps ts rs
    haveI : ∀ ps, Persistent (txnOpsRespN (GF := GF) ps es rs) :=
      fun ps => txnOpsRespN_persistent' ps es rs
    unfold txnOpRespN
    cases ok <;> infer_instance
  | .txn _ _ _, .range _ _ => by unfold txnOpRespN; infer_instance
  | .txn _ _ _, .put => by unfold txnOpRespN; infer_instance
  | .txn _ _ _, .delete _ => by unfold txnOpRespN; infer_instance

theorem txnOpsRespN_persistent' :
    ∀ (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult),
      Persistent (txnOpsRespN (GF := GF) ps ops rs)
  | [], [], [] => by unfold txnOpsRespN; infer_instance
  | p :: ps, op :: ops, r :: rs => by
    haveI := txnOpRespN_persistent' p op r
    haveI := txnOpsRespN_persistent' ps ops rs
    unfold txnOpsRespN; infer_instance
  | [], [], _ :: _ => by unfold txnOpsRespN; infer_instance
  | [], _ :: _, _ => by unfold txnOpsRespN; infer_instance
  | _ :: _, [], _ => by unfold txnOpsRespN; infer_instance
  | _ :: _, _ :: _, [] => by unfold txnOpsRespN; infer_instance
end

instance txnOpRespN_persistent (p : Loc) (op : TxnOp) (res : TxnOpResult) :
    Persistent (txnOpRespN (GF := GF) p op res) := txnOpRespN_persistent' p op res

instance txnOpsRespN_persistent (ps : List Loc) (ops : List TxnOp) (rs : List TxnOpResult) :
    Persistent (txnOpsRespN (GF := GF) ps ops rs) := txnOpsRespN_persistent' ps ops rs

/-! ## Owned responses -/

/-- **An owned range response's body** `rr` (a `*pb.RangeResponse`) answering the get `o` whose
selection is `sel` and whose range has `count` keys: its key-values (the slice, its capacity, each
key-value's fields: `cs`), `More` and `Count`, owned. -/
def rangeBodyOwn (rr : Loc) (o : OpFull) (sel : List EtcdKv) (count : Nat) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List CachedKv) (more : Bool),
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" rr ↦ sl ∗ sl ↦* (cs.map CachedKv.p) ∗
    ownSliceCap Loc sl (DFrac.own 1) ∗ ([∗list] c ∈ cs, cachedKvOwn c (DFrac.own 1)) ∗
    ⌜rangeKvsOk o sel (cs.map CachedKv.kv)⌝ ∗
    structFieldRef etcdserverpb.RangeResponse go!"More" rr ↦ more ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" rr ↦ W64 (count : Int))

/-- **An owned range response** `rr`: its `Header` (any) and its body (`rangeBodyOwn`), owned. -/
def rangeRespOwn (rr : Loc) (o : OpFull) (sel : List EtcdKv) (count : Nat) : IProp GF :=
  iprop(∃ h : Loc, structFieldRef etcdserverpb.RangeResponse go!"Header" rr ↦ h ∗
    rangeBodyOwn rr o sel count)

/-- **The `*pb.ResponseOp` `p` is the owned response of the top-level operation `op` with result
`res`**: the `ResponseOp` and its wrapper read-only; a get's range response owned
(`rangeRespOwn`); a put's, delete's or nested transaction's response with its `Header` owned (a
delete's `Deleted`, a nested transaction's `Succeeded` and responses read-only). -/
def txnOpRespOwn (p : Loc) : TxnOp → TxnOpResult → IProp GF
  | .get o, .range sel n => iprop(⌜p ≠ null⌝ ∗ ∃ (w rr : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
      ⌜rr ≠ null⌝ ∗ rangeRespOwn rr o sel n)
  | .put _ _ _, .put => iprop(⌜p ≠ null⌝ ∗ ∃ (w pr h : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ pr ∗ ⌜pr ≠ null⌝ ∗
      structFieldRef etcdserverpb.PutResponse go!"Header" pr ↦ h)
  | .putKeep _ _, .put => iprop(⌜p ≠ null⌝ ∗ ∃ (w pr h : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ pr ∗ ⌜pr ≠ null⌝ ∗
      structFieldRef etcdserverpb.PutResponse go!"Header" pr ↦ h)
  | .putIgnVal _ _, .put => iprop(⌜p ≠ null⌝ ∗ ∃ (w pr h : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ pr ∗ ⌜pr ≠ null⌝ ∗
      structFieldRef etcdserverpb.PutResponse go!"Header" pr ↦ h)
  | .delete _, .delete n => iprop(⌜p ≠ null⌝ ∗ ∃ (w dr h : Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w ↦□ dr ∗
      ⌜dr ≠ null⌝ ∗ structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" dr ↦ h ∗
      structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" dr ↦□ W64 (n : Int))
  | .txn _ ts es, .txn ok rs => iprop(⌜p ≠ null⌝ ∗ ∃ (w tr h : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□
        interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseTxn.ty) #w ∗
      structFieldRef etcdserverpb.ResponseOp_ResponseTxn go!"ResponseTxn" w ↦□ tr ∗ ⌜tr ≠ null⌝ ∗
      structFieldRef etcdserverpb.TxnResponse go!"Header" tr ↦ h ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" tr ↦□ ok ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" tr ↦□ sl ∗ sl ↦*□ ps ∗
      (if ok then txnOpsRespN ps ts rs else txnOpsRespN ps es rs))
  | _, _ => iprop(False)

/-- The owned responses `ps` of the top-level operations `ops` with results `rs`, in order. -/
def txnOpsRespOwn : List Loc → List TxnOp → List TxnOpResult → IProp GF
  | [], [], [] => iprop(True)
  | p :: ps, op :: ops, r :: rs => iprop(txnOpRespOwn p op r ∗ txnOpsRespOwn ps ops rs)
  | _, _, _ => iprop(False)

/-- **An owned transaction response** `resp` (a `*clientv3.TxnResponse`): its header (read-only,
all five fields, `hdrFull`), its `Succeeded` `ok` (owned), its `Responses` slice (read-only) of
the owned responses of `ops` with results `rs`. -/
def txnRespOwn (resp : Loc) (hm : HdrM) (ok : Bool) (ops : List TxnOp) (rs : List TxnOpResult) :
    IProp GF :=
  iprop(∃ (hdr : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ hdrFull hdr hm ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ ok ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
    txnOpsRespOwn ps ops rs)

/-- **A successful `Commit()`, with an owned response**: as `txnCommitResult`'s success case
(`runTxn` at a revision `r` reached, at least `lo` if linearizable, on a state `s` under `pfx`,
`txnStates`), the response owned (`txnRespOwn`, its header's revision `r`). -/
def txnCommitOk (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc) : IProp GF :=
  iprop(∃ (r : w64) (s : List EtcdKv) (hm : HdrM), ⌜hm.revision = r⌝ ∗
    txnRespOwn resp hm (runTxn r s t).1 (t.branch (runTxn r s t).1) (runTxn r s t).2.2 ∗
    etcdReached r ∗
    ⌜(t.linearizable = true → sint.Z lo ≤ sint.Z r) ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧
      EtcdStateWf pfx s⌝ ∗
    txnStates pfx r s (runTxn r s t).2.1 (txnWrote (runTxn r s t).2.2))

/-- **What `Commit()` returns, owned**: an error (`clientErr`), or `txnCommitOk`. -/
def txnCommitResultO (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝) ∨
    (⌜err = GoInterface.nil⌝ ∗ txnCommitOk pfx lo t resp))

/-! ## The builder with nested operations and owned responses -/

/-- **The builder** `t` with abstract state `B`, with nested operations and owned responses (see
the module docstring; `txnBuilderSpec`'s `If`, its `Then`/`Else` on operation trees, its `Commit`
with `txnCommitResultO`). -/
def txnBuilderSpecO (t : GoInterfaceOk) (pfx : GoString) (B : TxnBuild → IProp GF) : IProp GF :=
  iprop(
    (□ ∀ (b : TxnBuild) (sl : GoSlice) (ms : List CmpModel),
      {{ B b ∗ cmpsAt sl ms ∗ ⌜b.cif = false ∧ b.cthen = false ∧ b.celse = false⌝ }}
        (App (Val #(methods t.ty go!"If" t.v)) (Val #sl))
      {{ RET #(GoInterface.ok t);
          B { b with model := { b.model with cmps := b.model.cmps ++ ms }, cif := true } }}) ∗
    (□ ∀ (b : TxnBuild) (sl : GoSlice) (ts : List OpT) (ops : List TxnOp),
      {{ B b ∗ opsTAt sl ts ∗ ⌜OpT.txnOps ts = some ops ∧ b.cthen = false ∧ b.celse = false⌝ }}
        (App (Val #(methods t.ty go!"Then" t.v)) (Val #sl))
      {{ RET #(GoInterface.ok t);
          B { b with model := { b.model with thenOps := b.model.thenOps ++ ops },
                     cthen := true } }}) ∗
    (□ ∀ (b : TxnBuild) (sl : GoSlice) (ts : List OpT) (ops : List TxnOp),
      {{ B b ∗ opsTAt sl ts ∗ ⌜OpT.txnOps ts = some ops ∧ b.celse = false⌝ }}
        (App (Val #(methods t.ty go!"Else" t.v)) (Val #sl))
      {{ RET #(GoInterface.ok t);
          B { b with model := { b.model with elseOps := b.model.elseOps ++ ops },
                     celse := true } }}) ∗
    (□ ∀ (b : TxnBuild) (lo : w64),
      {{ B b ∗ etcdReached lo ∗ ⌜b.model.Under pfx⌝ }}
        (App (Val #(methods t.ty go!"Commit" t.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          txnCommitResultO pfx lo b.model resp err }}))

instance txnBuilderSpecO_persistent (t : GoInterfaceOk) (pfx : GoString)
    (B : TxnBuild → IProp GF) : Persistent (txnBuilderSpecO t pfx B) := by
  unfold txnBuilderSpecO; infer_instance

/-- **The client's transactions, with nested operations and owned responses** (`clientv3.KV`'s
`Txn`; a definition, the assumption a caller makes of `client.KV`, beside `isEtcdTxnKV`):
`kv.Txn(ctx)` returns a builder in its empty state. -/
def isEtcdTxnKVO (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    {{ context.isContext ctx cs }}
      (App (Val #(methods kv.ty go!"Txn" kv.v)) (Val #(GoInterface.ok ctx)))
    {{ (t : GoInterfaceOk), RET #(GoInterface.ok t);
        ∃ B : TxnBuild → IProp GF, B TxnBuild.empty ∗ txnBuilderSpecO t pfx B }})

instance isEtcdTxnKVO_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdTxnKVO (GF := GF) kv pfx) := by
  unfold isEtcdTxnKVO; infer_instance

/-! ## `Do` -/

/-- **The client's `Do` of a get** (`clientv3.KV`'s `Do(ctx, op)`; a definition, the assumption a
caller makes of `client.KV`): for a get `op` (modelled by `o`), the `OpResponse`'s `get` field and
the error are what `Get` returns (`kvGetResult`). -/
def isEtcdDoKV (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF))
      (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (lo : w64),
    {{ context.isContext ctx cs ∗ opFullAt opv o ∗ etcdReached lo ∗ ⌜o.t = W64 1⌝ }}
      (App (App (Val #(methods kv.ty go!"Do" kv.v)) (Val #(GoInterface.ok ctx))) (Val #opv))
    {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
        kvGetResult pfx lo o r.get' err }})

instance isEtcdDoKV_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdDoKV (GF := GF) kv pfx) := by
  unfold isEtcdDoKV; infer_instance

/-! ## Lemmas -/

/-- Plain operations (each one a transaction can run) as operation trees. -/
theorem opsAt_leaves (sl : GoSlice) (os : List OpFull) (ops : List TxnOp)
    (h : os.map txnOpOf = ops.map some) :
    opsAt (GF := GF) sl os ⊢ opsTAt sl (os.map OpT.leaf) := by
  unfold opsAt opsTAt
  iintro ⟨%vs, #Hsl, %Hlen, #Hall⟩
  iexists vs
  iframe Hsl
  iclear Hsl
  have key : ∀ (vs : List go_etcd_io.etcd.client.v3.Op) (os : List OpFull) (ops : List TxnOp),
      os.map txnOpOf = ops.map some → vs.length = os.length →
      (□ ∀ (i : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs[i]? = some v⌝ -∗
        ⌜os[i]? = some o⌝ -∗ opFullAt v o : IProp GF) ⊢
      opListAtC false vs (os.map OpT.leaf) := by
    intro vs
    induction vs with
    | nil =>
      intro os ops _ hl
      cases os with
      | nil => iintro -; simp only [List.map_nil, opListAtC]; itrivial
      | cons _ _ => simp at hl
    | cons v vs ih =>
      intro os ops hm hl
      cases os with
      | nil => simp at hl
      | cons o os =>
        cases ops with
        | nil => simp at hm
        | cons op ops =>
          simp only [List.map_cons, List.cons.injEq] at hm
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
          iintro #H
          simp only [List.map_cons]
          unfold opListAtC opTAtC
          isplitl
          · isplitl
            · iapply H $$ %0 %v %o %rfl %rfl
            · ipureintro; exact txnOpOf_t hm.1
          · iapply ih os ops hm.2 hl
            imodintro
            iintro %i %v' %o' %Hv %Ho
            iapply H $$ %(i + 1) %v' %o' %Hv %Ho
  iapply key vs os ops h Hlen
  iexact Hall

end defs

end EtcdGrove
end Perennial
