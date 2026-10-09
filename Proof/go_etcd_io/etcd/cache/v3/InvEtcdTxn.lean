/-
The etcd model, continued: transactions and leases (Lean-first, no Rocq counterpart). See
`decisions.md`, "the transaction model: sequential ops at one revision, per prefix; leases
without liveness; the create-revision persistence law".

**Transactions, purely.** A transaction (`TxnModel`) is a list of comparisons (`CmpModel`,
`InvCmp.lean`) and two lists of operations (`TxnOp`: a get, a put or a delete). etcd evaluates
the comparisons on its state `s` (`cmpHolds`, etcd's `applyCompare`: a comparison on a range
holds if it holds of every key in it; on no key, it reads the zero key-value — create and mod
revision, version and lease `0` — **except a value comparison, which then fails**), and runs the
chosen branch's operations **in order, each on the state the previous one left** (`runOps`,
`applyTxnOp`), all at one revision `r`: a put of a new key creates it with create and mod
revision `r` and version `1`; a put of an existing key keeps its create revision, sets its mod
revision to `r`, increments its version, and sets its value and lease; a delete removes the keys
its range selects; a get reads the state at that point (`rangeSel`: the keys in its range,
filtered by its revision filters; the response sorts and limits them, `rangeKvsOk`). The
revision advances only if the transaction wrote (`txnWrote`: a put, or a delete of at least one
key); a read-only transaction is answered at the current revision, whose state it leaves as it
was.

**The client's `Txn`** (`isEtcdTxnKV kv pfx`, a definition like `isEtcdKV`): `kv.Txn(ctx)`
returns a builder `t` (a `clientv3.Txn` interface value) with an abstract state `B` (its
`TxnBuild`: the model so far and which of `If`/`Then`/`Else` were called); `If(cs...)`,
`Then(ops...)`, `Else(ops...)` append to the model (each once, in that order: otherwise the
client panics) and return `t`; `Commit()`, for a transaction whose keys are all under `pfx`
and with what the caller knows etcd has reached (`etcdReached lo`), returns an error, or a
response (`txnCommitResult`) at a revision `r ≥ lo` that etcd has reached, with a state `s`
(sorted, under `pfx`) such that: `resp.Succeeded` is `(runTxn r s t).1`; the responses are the
chosen operations' results; if the transaction wrote, `s` was etcd's state at `r - 1` and
`(runTxn r s t).2.1` is its state at `r`; otherwise `s` is its state at `r`. The builder's
methods are the trust boundary (the client's `txn` calls protobuf's `proto.Clone` and gRPC):
see `decisions.md`.

**History laws** (axioms, about `etcdState`): every key-value of etcd's state at `r` has
`0 < createRev ≤ modRev ≤ r` and `0 < version` (`etcdState_revs`); and a key present at `r`
with create revision `c` is present, with the same create revision, at every revision in
`[c, r]` (`etcdState_create_persist`: a key is created once and lives until it is deleted).

**Leases** (`isEtcdLease l`, a definition): `Grant` returns an error or a lease ID other than
`NoLease` with a header revision etcd has reached; `KeepAlive` returns an error, or a channel
(nil or not) on which a receive yields any response or the close (`isChanAny`: no promise that
the stream lasts); `Revoke` returns an error or a response whose header revision etcd has
reached. What a lease does to keys (a put with `WithLease(id)` records `id` in the key-value;
the lease's expiry or revocation deletes them, a step of etcd's history like any other) is not
stated beyond the put's `lease`: nothing about liveness.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd
public import Proof.go_etcd_io.etcd.client.v3.InvCmp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## Key ranges and comparisons -/

/-- The key `k` is in the range `[key, rangeEnd)` of a request or a comparison: the key alone if
`rangeEnd` is empty, every key from `key` on if it is `[0]`. -/
def inRange (key rangeEnd k : GoString) : Bool :=
  if rangeEnd = [] then decide (k = key)
  else if rangeEnd = [W8 0] then !decide (go.GoStringLt k key)
  else !decide (go.GoStringLt k key) && decide (go.GoStringLt k rangeEnd)

/-- Every key of the range `[key, rangeEnd)` has the prefix `pfx`. -/
def KeyRangeUnder (pfx key rangeEnd : GoString) : Prop :=
  ∀ k, inRange key rangeEnd k = true → pfx <+: k

/-- `-1`, `0` or `1`, as `bytes.Compare` and etcd's `compareInt64`. -/
def cmpSign (lt eq : Bool) : Int := if lt then -1 else if eq then 0 else 1

/-- etcd's comparison of two `int64`s. -/
def int64Cmp (a b : w64) : Int := cmpSign (decide (sint.Z a < sint.Z b)) (decide (a = b))

/-- `bytes.Compare`. -/
def bytesCmp (a b : GoString) : Int := cmpSign (decide (go.GoStringLt a b)) (decide (a = b))

/-- The operator applied to a comparison's sign. -/
def CmpOp.holds : CmpOp → Int → Bool
  | .eq, c => c == 0
  | .neq, c => c != 0
  | .gt, c => decide (0 < c)
  | .lt, c => decide (c < 0)

/-- etcd's `compareKV`: the key-value `v` against the comparison `c`. -/
def cmpKv (c : CmpModel) (v : EtcdKv) : Bool :=
  c.op.holds (match c.target with
    | .value => bytesCmp v.value c.val
    | .version => int64Cmp v.version c.num
    | .create => int64Cmp v.createRev c.num
    | .mod => int64Cmp v.modRev c.num
    | .lease => int64Cmp v.lease c.num)

/-- A missing key, as etcd compares it: revisions, version and lease `0`, empty value. -/
def zeroKv (k : GoString) : EtcdKv :=
  { key := k, createRev := W64 0, modRev := W64 0, version := W64 0, value := [], lease := W64 0 }

/-- **etcd's `applyCompare`** on the state `s`: the comparison holds of every key of its range;
if the range has no key, of the zero key-value, except that a value comparison fails. -/
def cmpHolds (s : List EtcdKv) (c : CmpModel) : Bool :=
  let sel := s.filter (fun v => inRange c.key c.rangeEnd v.key)
  if sel = [] then (c.target != .value) && cmpKv c (zeroKv c.key)
  else sel.all (cmpKv c)

/-! ## Transactions -/

/-- An operation of a transaction: a get (a range request, with its `Op`'s model), a put of a
key's value with a lease (`0`: none), or a delete (a range). -/
inductive TxnOp where
  | get (o : OpFull)
  | put (key value : GoString) (lease : w64)
  | delete (o : OpFull)

/-- A transaction: `If(cmps...).Then(thenOps...).Else(elseOps...)`. -/
structure TxnModel where
  cmps : List CmpModel
  thenOps : List TxnOp
  elseOps : List TxnOp

/-- The empty transaction (what `kv.Txn(ctx)` starts from). -/
def TxnModel.empty : TxnModel := { cmps := [], thenOps := [], elseOps := [] }

/-- The result of an operation: a get's selected key-values (in key order) and the number of keys
in its range; a put; a delete's number of deleted keys. -/
inductive TxnOpResult where
  | range (sel : List EtcdKv) (count : Nat)
  | put
  | delete (deleted : Nat)

/-- The operation an `Op` (`Then`'s and `Else`'s arguments) stands for in a transaction: a range
at the current revision, a put (without `WithIgnoreValue`/`WithIgnoreLease`), a delete; nothing
for a nested transaction or another revision (not modelled). -/
def txnOpOf (o : OpFull) : Option TxnOp :=
  if o.t = W64 1 then (if o.base.rev = W64 0 then some (.get o) else none)
  else if o.t = W64 2 then
    (if o.ignoreValue = false ∧ o.ignoreLease = false then some (.put o.key o.val o.leaseID)
     else none)
  else if o.t = W64 3 then some (.delete o)
  else none

/-- The keys of the range of `o`, in the state `s` (in key order). -/
def rangeIn (s : List EtcdKv) (o : OpFull) : List EtcdKv :=
  s.filter (fun v => inRange o.key o.base.rangeEnd v.key)

/-- A range request's revision filters (`0`: no filter). -/
def kvFilterOk (o : OpFull) (v : EtcdKv) : Bool :=
  (decide (o.base.minModRev = W64 0) || decide (sint.Z o.base.minModRev ≤ sint.Z v.modRev)) &&
  (decide (o.base.maxModRev = W64 0) || decide (sint.Z v.modRev ≤ sint.Z o.base.maxModRev)) &&
  (decide (o.base.minCreateRev = W64 0) || decide (sint.Z o.base.minCreateRev ≤ sint.Z v.createRev)) &&
  (decide (o.base.maxCreateRev = W64 0) || decide (sint.Z v.createRev ≤ sint.Z o.base.maxCreateRev))

/-- What a get selects: the keys of its range that pass its filters, in key order. -/
def rangeSel (s : List EtcdKv) (o : OpFull) : List EtcdKv := (rangeIn s o).filter (kvFilterOk o)

/-- A put of `key` at revision `r` (see the module docstring). -/
def putKv (r : w64) (key value : GoString) (lease : w64) (s : List EtcdKv) : List EtcdKv :=
  let nv : EtcdKv := match s.find? (fun v => decide (v.key = key)) with
    | some v => { v with modRev := r, version := v.version + W64 1, value := value, lease := lease }
    | none => { key := key, createRev := r, modRev := r, version := W64 1, value := value,
                lease := lease }
  btInsert etcdKvLess nv s

/-- One operation, at revision `r`, on the state `s`: the state after it and its result. -/
def applyTxnOp (r : w64) (s : List EtcdKv) : TxnOp → List EtcdKv × TxnOpResult
  | .get o => (s, .range (rangeSel s o) (rangeIn s o).length)
  | .put k v l => (putKv r k v l s, .put)
  | .delete o => (s.filter (fun v => !inRange o.key o.base.rangeEnd v.key),
      .delete (rangeIn s o).length)

/-- Operations in order, each on the state the previous one left. -/
def runOps (r : w64) : List EtcdKv → List TxnOp → List EtcdKv × List TxnOpResult
  | s, [] => (s, [])
  | s, op :: ops =>
    let p := applyTxnOp r s op
    let q := runOps r p.1 ops
    (q.1, p.2 :: q.2)

/-- The branch the comparisons choose. -/
def TxnModel.branch (t : TxnModel) (ok : Bool) : List TxnOp := if ok then t.thenOps else t.elseOps

/-- **A transaction** at revision `r` on the state `s`: whether the comparisons held, the state
after the chosen branch, and its operations' results. -/
def runTxn (r : w64) (s : List EtcdKv) (t : TxnModel) : Bool × List EtcdKv × List TxnOpResult :=
  let ok := t.cmps.all (cmpHolds s)
  let q := runOps r s (t.branch ok)
  (ok, q.1, q.2)

/-- An operation's result is a write: a put, or a delete of some key. -/
def TxnOpResult.wrote : TxnOpResult → Bool
  | .put => true
  | .delete n => n != 0
  | .range _ _ => false

/-- The transaction wrote (so it has a revision of its own). -/
def txnWrote (rs : List TxnOpResult) : Bool := rs.any TxnOpResult.wrote

/-- Operations that did not write leave the state as it was. -/
theorem runOps_noWrite (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), txnWrote (runOps r s ops).2 = false →
      (runOps r s ops).1 = s
  | _, [] => fun _ => rfl
  | s, op :: ops => by
    intro h
    cases op with
    | get o =>
      simp only [runOps, applyTxnOp, txnWrote, List.any_cons, TxnOpResult.wrote,
        Bool.false_or] at h ⊢
      exact runOps_noWrite r s ops h
    | put k v l =>
      simp [runOps, applyTxnOp, txnWrote, TxnOpResult.wrote] at h
    | delete o =>
      simp only [runOps, applyTxnOp, txnWrote, List.any_cons, TxnOpResult.wrote,
        Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h ⊢
      obtain ⟨h0, h1⟩ := h
      have hs : s.filter (fun v => !inRange o.key o.base.rangeEnd v.key) = s := by
        rw [List.filter_eq_self]
        intro v hv
        have : v ∉ rangeIn s o := by
          rw [List.length_eq_zero_iff] at h0; rw [h0]; simp
        unfold rangeIn at this
        simp only [List.mem_filter, not_and] at this
        simpa using this hv
      rw [hs] at h1 ⊢
      exact runOps_noWrite r s ops h1

/-- The keys an operation touches are under the prefix `pfx`. -/
def TxnOp.Under (pfx : GoString) : TxnOp → Prop
  | .get o => KeyRangeUnder pfx o.key o.base.rangeEnd
  | .put k _ _ => pfx <+: k
  | .delete o => KeyRangeUnder pfx o.key o.base.rangeEnd

/-- Every key the transaction compares or touches is under the prefix `pfx` (the client's
contract is stated per prefix, as `isEtcdKV`'s). -/
def TxnModel.Under (pfx : GoString) (t : TxnModel) : Prop :=
  (∀ c ∈ t.cmps, KeyRangeUnder pfx c.key c.rangeEnd) ∧ (∀ op ∈ t.thenOps, op.Under pfx) ∧
    (∀ op ∈ t.elseOps, op.Under pfx)

/-! ### A get's response: sort, limit, keys-only, count-only -/

/-- etcd's sort order for a range (`pb.RangeRequest_SortOrder`: `0` none, `1` ascending, `2`
descending): none if not set; a sort by another target than the key with no order is ascending
(etcd's `Range`). -/
def OpFull.effSortOrder (o : OpFull) : w64 :=
  if o.base.sortSet = false then W64 0
  else if o.sortTarget ≠ W64 0 ∧ o.sortOrder = W64 0 then W64 1
  else if o.sortTarget = W64 0 ∧ o.sortOrder = W64 1 then W64 0
  else o.sortOrder

/-- `a` sorts no later than `b` by the target (`0` key, `1` version, `2` create revision,
`3` mod revision, `4` value). -/
def kvLeBy (target : w64) (a b : EtcdKv) : Prop :=
  if target = W64 1 then sint.Z a.version ≤ sint.Z b.version
  else if target = W64 2 then sint.Z a.createRev ≤ sint.Z b.createRev
  else if target = W64 3 then sint.Z a.modRev ≤ sint.Z b.modRev
  else if target = W64 4 then go.GoStringLe a.value b.value
  else go.GoStringLe a.key b.key

/-- **A get's response key-values** `kvs`, for its selection `sel` (key order): a reordering of
`sel` sorted as requested (etcd's sort is not stable: ties in any order), limited (a positive
limit), values dropped if keys-only, nothing if count-only. -/
def rangeKvsOk (o : OpFull) (sel kvs : List EtcdKv) : Prop :=
  ∃ l : List EtcdKv, l.Perm sel ∧
    (o.effSortOrder = W64 0 → l = sel) ∧
    (o.effSortOrder = W64 1 → l.Pairwise (kvLeBy o.sortTarget)) ∧
    (o.effSortOrder = W64 2 → l.Pairwise (fun a b => kvLeBy o.sortTarget b a)) ∧
    kvs = (if o.base.countOnly then []
      else ((if 0 < sint.Z o.base.limit then l.take (sint.Z o.base.limit).toNat else l).map
        (fun v => if o.keysOnly then { v with value := [] } else v)))

/-! ## History laws -/

/-- **Revisions are well formed** (an axiom about etcd's history): a key-value of etcd's state at
`r` was created at a positive revision, last modified at or after it and at or before `r`, and
has a positive version. -/
axiom etcdState_revs {GF : BundledGFunctors} (r : w64) (pfx : GoString) (s : List EtcdKv) :
  etcdState (GF := GF) r pfx s ⊢
    ⌜∀ v ∈ s, 0 < sint.Z v.createRev ∧ sint.Z v.createRev ≤ sint.Z v.modRev ∧
      sint.Z v.modRev ≤ sint.Z r ∧ 0 < sint.Z v.version⌝

/-- **A key lives from its creation** (an axiom about etcd's history): a key present at revision
`r` with create revision `c` is present, with the same create revision, at every revision `a`
in `[c, r]` (a key is created once, at `c`, and lives until it is deleted; a re-created key has a
new create revision). -/
axiom etcdState_create_persist {GF : BundledGFunctors} (r a : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
  etcdState (GF := GF) r pfx s ∗ etcdState a pfx s' ⊢
    ⌜∀ v ∈ s, sint.Z v.createRev ≤ sint.Z a → sint.Z a ≤ sint.Z r →
      ∃ v' ∈ s', v'.key = v.key ∧ v'.createRev = v.createRev⌝

section client
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]

/-! ## The client's transactions -/

/-- The `*mvccpb.KeyValue`s `ps` hold, in order, the key-values `kvs` (read-only). -/
def kvPtrsAt (ps : List Loc) (kvs : List EtcdKv) : IProp GF :=
  iprop(⌜ps.length = kvs.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (v : EtcdKv), ⌜ps[i]? = some p⌝ -∗ ⌜kvs[i]? = some v⌝ -∗ kvValAt p v)

instance kvPtrsAt_persistent (ps : List Loc) (kvs : List EtcdKv) :
    Persistent (kvPtrsAt (GF := GF) ps kvs) := by
  unfold kvPtrsAt; infer_instance

/-- The `*pb.RangeResponse` `rr` answers the get `o` whose selection is `sel` and whose range
has `count` keys (read-only). -/
def rangeRespAt (rr : Loc) (o : OpFull) (sel : List EtcdKv) (count : Nat) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ps : List Loc) (kvs : List EtcdKv),
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" rr ↦□ sl ∗ sl ↦*□ ps ∗ kvPtrsAt ps kvs ∗
    ⌜rangeKvsOk o sel kvs⌝ ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" rr ↦□ W64 (count : Int))

instance rangeRespAt_persistent (rr : Loc) (o : OpFull) (sel : List EtcdKv) (count : Nat) :
    Persistent (rangeRespAt (GF := GF) rr o sel count) := by
  unfold rangeRespAt; infer_instance

/-- The `*pb.ResponseOp` `p` is the response of the operation `op` with result `res` (read-only):
its `Response` oneof holds the wrapper of the operation's kind. -/
def txnOpRespAt (p : Loc) (op : TxnOp) (res : TxnOpResult) : IProp GF :=
  iprop(∃ u : GoInterface, structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□ u ∗
    match op, res with
    | .get o, .range sel n => iprop(∃ (w rr : Loc),
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w⌝ ∗
        structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
        ⌜rr ≠ null⌝ ∗ rangeRespAt rr o sel n)
    | .put _ _ _, .put => iprop(∃ (w pr : Loc),
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w⌝ ∗
        structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ pr ∗
        ⌜pr ≠ null⌝)
    | .delete _, .delete n => iprop(∃ (w dr : Loc),
        ⌜u = interface.mkOk
          (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w⌝ ∗
        structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w ↦□
          dr ∗ ⌜dr ≠ null⌝ ∗
        structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" dr ↦□ W64 (n : Int))
    | _, _ => iprop(False))

instance txnOpRespAt_persistent (p : Loc) (op : TxnOp) (res : TxnOpResult) :
    Persistent (txnOpRespAt (GF := GF) p op res) := by
  unfold txnOpRespAt
  cases op <;> cases res <;> infer_instance

/-- The `*clientv3.TxnResponse` `resp` (read-only): its header has revision `r`, `Succeeded` is
`ok`, and its `Responses` are, in order, the responses of the operations `ops` with results
`rs`. -/
def txnRespAt (resp : Loc) (r : w64) (ok : Bool) (ops : List TxnOp) (rs : List TxnOpResult) :
    IProp GF :=
  iprop(∃ (hdr : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ ⌜hdr ≠ null⌝ ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r ∗
    structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦□ ok ∗
    structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
    ⌜ps.length = ops.length ∧ rs.length = ops.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (op : TxnOp) (res : TxnOpResult), ⌜ps[i]? = some p⌝ -∗
      ⌜ops[i]? = some op⌝ -∗ ⌜rs[i]? = some res⌝ -∗ txnOpRespAt p op res)

instance txnRespAt_persistent (resp : Loc) (r : w64) (ok : Bool) (ops : List TxnOp)
    (rs : List TxnOpResult) : Persistent (txnRespAt (GF := GF) resp r ok ops rs) := by
  unfold txnRespAt; infer_instance

/-- etcd's states around a transaction at revision `r` from the state `s` to `s'`: if it
wrote, `s` at `r - 1` and `s'` at `r`; otherwise `s` at `r`. -/
def txnStates (pfx : GoString) (r : w64) (s s' : List EtcdKv) (wrote : Bool) : IProp GF :=
  if wrote then iprop(□ etcdState (r - W64 1) pfx s ∗ □ etcdState r pfx s')
  else iprop(□ etcdState r pfx s)

instance txnStates_persistent (pfx : GoString) (r : w64) (s s' : List EtcdKv) (wrote : Bool) :
    Persistent (txnStates (GF := GF) pfx r s s' wrote) := by
  unfold txnStates; split <;> infer_instance

/-- **What `Commit()` returns** for the transaction `t` under the prefix `pfx`, called knowing
that etcd has reached `lo`: an error; or a response at a revision `r` (at least `lo`, reached,
below `2^63 - 1`) and a state `s` (sorted, under `pfx`) such that the response is the
transaction run at `r` on `s` (`runTxn`), and either it wrote, `s` was etcd's state at `r - 1`
and the state it leaves is etcd's state at `r`, or it did not write and `s` is etcd's state at
`r` (which it leaves unchanged: `runOps_noWrite`). -/
def txnCommitResult (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (s : List EtcdKv),
      txnRespAt resp r (runTxn r s t).1 (t.branch (runTxn r s t).1) (runTxn r s t).2.2 ∗
      etcdReached r ∗
      ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf pfx s⌝ ∗
      txnStates pfx r s (runTxn r s t).2.1 (txnWrote (runTxn r s t).2.2)))

instance txnCommitResult_persistent (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc)
    (err : GoInterface) : Persistent (txnCommitResult (GF := GF) pfx lo t resp err) := by
  unfold txnCommitResult; infer_instance

/-- A transaction being built: the model so far and which of `If`, `Then`, `Else` were called. -/
structure TxnBuild where
  model : TxnModel
  cif : Bool
  cthen : Bool
  celse : Bool

/-- What `kv.Txn(ctx)` starts from. -/
def TxnBuild.empty : TxnBuild := { model := .empty, cif := false, cthen := false, celse := false }

/-- **The builder** `t` (a `clientv3.Txn` interface value) with abstract state `B` (the client's;
`B b` is owned by the caller): the triples of its four methods. `If(cs...)` (before `Then` and
`Else`, once), `Then(ops...)` (before `Else`, once), `Else(ops...)` (once) append the comparisons
or operations (each `Op` one a transaction can run, `txnOpOf`) and return `t`; `Commit()`, for a
transaction under `pfx`, returns `txnCommitResult`. -/
def txnBuilderSpec (t : GoInterfaceOk) (pfx : GoString) (B : TxnBuild → IProp GF) : IProp GF :=
  iprop(
    (□ ∀ (b : TxnBuild) (sl : GoSlice) (ms : List CmpModel),
      {{ B b ∗ cmpsAt sl ms ∗ ⌜b.cif = false ∧ b.cthen = false ∧ b.celse = false⌝ }}
        (App (Val #(methods t.ty go!"If" t.v)) (Val #sl))
      {{ RET #(GoInterface.ok t);
          B { b with model := { b.model with cmps := b.model.cmps ++ ms }, cif := true } }}) ∗
    (□ ∀ (b : TxnBuild) (sl : GoSlice) (os : List OpFull) (ops : List TxnOp),
      {{ B b ∗ opsAt sl os ∗ ⌜os.map txnOpOf = ops.map some ∧ b.cthen = false ∧
          b.celse = false⌝ }}
        (App (Val #(methods t.ty go!"Then" t.v)) (Val #sl))
      {{ RET #(GoInterface.ok t);
          B { b with model := { b.model with thenOps := b.model.thenOps ++ ops },
                     cthen := true } }}) ∗
    (□ ∀ (b : TxnBuild) (sl : GoSlice) (os : List OpFull) (ops : List TxnOp),
      {{ B b ∗ opsAt sl os ∗ ⌜os.map txnOpOf = ops.map some ∧ b.celse = false⌝ }}
        (App (Val #(methods t.ty go!"Else" t.v)) (Val #sl))
      {{ RET #(GoInterface.ok t);
          B { b with model := { b.model with elseOps := b.model.elseOps ++ ops },
                     celse := true } }}) ∗
    (□ ∀ (b : TxnBuild) (lo : w64),
      {{ B b ∗ etcdReached lo ∗ ⌜b.model.Under pfx⌝ }}
        (App (Val #(methods t.ty go!"Commit" t.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          txnCommitResult pfx lo b.model resp err }}))

instance txnBuilderSpec_persistent (t : GoInterfaceOk) (pfx : GoString)
    (B : TxnBuild → IProp GF) : Persistent (txnBuilderSpec t pfx B) := by
  unfold txnBuilderSpec; infer_instance

/-- **The client's transactions** (`clientv3.KV`'s `Txn`; a definition, the assumption a caller
makes of `client.KV`, as `isEtcdKV`): `kv.Txn(ctx)` returns a builder in its empty state. -/
def isEtcdTxnKV (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    {{ context.isContext ctx cs }}
      (App (Val #(methods kv.ty go!"Txn" kv.v)) (Val #(GoInterface.ok ctx)))
    {{ (t : GoInterfaceOk), RET #(GoInterface.ok t);
        ∃ B : TxnBuild → IProp GF, B TxnBuild.empty ∗ txnBuilderSpec t pfx B }})

instance isEtcdTxnKV_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdTxnKV (GF := GF) kv pfx) := by
  unfold isEtcdTxnKV; infer_instance

/-! ## Leases -/

/-- A channel of pointers with no promise: a receive yields some value or finds it closed (the
invariant holds the channel's state, whatever it is). -/
def isChanAny (γ : ChanNames) (ch : Loc) : IProp GF :=
  iprop(isChan ch γ Loc ∗ inv (nroot .@ "etcd_anychan") (∃ s : ChanState Loc, ownChan γ Loc s))

instance isChanAny_persistent (γ : ChanNames) (ch : Loc) :
    Persistent (isChanAny (GF := GF) γ ch) := by
  unfold isChanAny; infer_instance

/-- **The client's leases** (`clientv3.Lease`; a definition, the assumption a caller makes of
`client.Lease`): `Grant`, `KeepAlive`, `Revoke` (see the module docstring). -/
def isEtcdLease (l : GoInterfaceOk) : IProp GF :=
  iprop(
    (□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (ttl : w64),
      {{ context.isContext ctx cs }}
        (App (App (Val #(methods l.ty go!"Grant" l.v)) (Val #(GoInterface.ok ctx))) (Val #ttl))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          ⌜err ≠ GoInterface.nil⌝ ∨
          (⌜err = GoInterface.nil⌝ ∗ ∃ (id : w64) (hdr : Loc) (r : w64),
            structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ id ∗
            ⌜id ≠ W64 0⌝ ∗
            structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ResponseHeader" resp
              ↦□ hdr ∗ ⌜hdr ≠ null⌝ ∗
            structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r ∗
            etcdReached r) }}) ∗
    (□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (id : w64),
      {{ context.isContext ctx cs }}
        (App (App (Val #(methods l.ty go!"KeepAlive" l.v)) (Val #(GoInterface.ok ctx))) (Val #id))
      {{ (ch : Loc) (err : GoInterface), RET (PairV #ch #err);
          ⌜err ≠ GoInterface.nil⌝ ∨
          (⌜err = GoInterface.nil⌝ ∗ (⌜ch = null⌝ ∨ ∃ γ : ChanNames,
            isChanAny γ ch)) }}) ∗
    (□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (id : w64),
      {{ context.isContext ctx cs }}
        (App (App (Val #(methods l.ty go!"Revoke" l.v)) (Val #(GoInterface.ok ctx))) (Val #id))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          ⌜err ≠ GoInterface.nil⌝ ∨
          (⌜err = GoInterface.nil⌝ ∗ ∃ (hdr : Loc) (r : w64),
            structFieldRef etcdserverpb.LeaseRevokeResponse go!"Header" resp ↦□ hdr ∗
            ⌜hdr ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r ∗
            etcdReached r) }}))

instance isEtcdLease_persistent (l : GoInterfaceOk) : Persistent (isEtcdLease (GF := GF) l) := by
  unfold isEtcdLease; infer_instance

/-- **The client's `Lease`** field: the `*clientv3.Client` `client`'s embedded `Lease` holds, for
good, a lease client (`isEtcdLease`). -/
def isEtcdLeaseClient (client : Loc) : IProp GF :=
  iprop(∃ l : GoInterfaceOk,
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"Lease" client ↦□ GoInterface.ok l ∗
    isEtcdLease l)

instance isEtcdLeaseClient_persistent (client : Loc) :
    Persistent (isEtcdLeaseClient (GF := GF) client) := by
  unfold isEtcdLeaseClient; infer_instance

end client

end EtcdGrove
end Perennial
