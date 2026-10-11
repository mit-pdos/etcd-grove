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
revision to `r`, increments its version, and sets its value and lease (or keeps the lease: a
put with `WithIgnoreLease`, `putKeep`); a delete removes the keys
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
`0 < createRev ≤ modRev ≤ r` and `0 < version` (`etcdState_revs`); a key present at `r`
with create revision `c` is present, with the same create revision, at every revision in
`[c, r]` (`etcdState_create_persist`: a key is created once and lives until it is deleted); and
two states holding a key with the same mod revision hold the same key-value
(`etcdState_modrev_det`: a revision writes a key at most once).

**A written revision is one commit's** (`etcdRevToken r`, an axiom with its exclusivity law
`etcdRevToken_excl`): every committed write is its own revision, so the client's contract hands
the caller of a writing commit an exclusive token for the revision it made (`txnCommitResultTok`,
`putResult`); a read-only transaction makes no revision (etcd answers it at the current one) and
gets no token.

**Linearizability** holds for a transaction with an operation that is not a serializable get
(`TxnModel.linearizable`); etcd answers one of serializable gets alone, or of no operation, from
the member's state, which may lag (`EtcdServer.Txn`, `IsTxnSerializable`).

**Read transactions** (`isEtcdReadTxnKV`): a transaction of gets alone, each at the current
revision or at an earlier one (`WithRev`): `Commit()` returns each get's range response on
etcd's state at its revision (`readTxnResult`); the STM's reads.

**Leases** (`isEtcdLease l`, a definition): `Grant` returns an error or a lease ID other than
`NoLease` with a header revision etcd has reached; `KeepAlive` returns an error, or a channel
(nil or not) on which a receive yields any response or the close (`isChanAny`: no promise that
the stream lasts); `Revoke` returns an error or a response whose header revision etcd has
reached. What a lease does to keys (a put with `WithLease(id)` records `id` in the key-value;
the lease's expiry or revocation deletes them, a step of etcd's history like any other) is not
stated beyond the put's `lease`: nothing about liveness.

**`client/v3/experimental/recipes`' additions**: puts (`putTxn`, `putResult`, `isEtcdPutKV`: a put
as the one-operation transaction `Then(OpPut(...))`, as a delete is `deleteTxn`), the contracts at
`context.TODO()` (`isEtcdKVTodo`, `isEtcdTxnKVTodo`, `isEtcdDeleteKVTodo`, `isEtcdPutKVTodo`:
`TODO()`'s context is not an `isContext`; the get's response also has its `More` flag,
`getRespMore`), and the range watch under the premise that its channel is never closed
(`isEtcdRangeWatcherOpen`).
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
key's value with a lease (`0`: none), a delete (a range), a put that keeps the key's lease
(`WithIgnoreLease`), a put that keeps the key's value (`WithIgnoreValue`), or a nested
transaction (`OpTxn(cmps, thenOps, elseOps)`). -/
inductive TxnOp where
  | get (o : OpFull)
  | put (key value : GoString) (lease : w64)
  | delete (o : OpFull)
  /-- `OpPut(key, value, WithIgnoreLease())`: the key keeps its lease. etcd fails the whole
  transaction (an error) if the key does not exist (`ErrKeyNotFound`); the model then gives it no
  lease, which no successful response claims. -/
  | putKeep (key value : GoString)
  /-- `OpPut(key, "", WithIgnoreValue(), ...)`: the key keeps its value, and its lease too if
  `lease` is `none` (`WithIgnoreLease()`), otherwise gets `lease`. etcd fails the whole transaction
  if the key does not exist (`ErrKeyNotFound`); the model then gives it the empty value. -/
  | putIgnVal (key : GoString) (lease : Option w64)
  /-- A nested transaction, `OpTxn(cmps, thenOps, elseOps)`: run as etcd runs it, at the same
  revision, on the state the operations before it left, its comparisons choosing the branch. -/
  | txn (cmps : List CmpModel) (thenOps elseOps : List TxnOp)

/-- A transaction: `If(cmps...).Then(thenOps...).Else(elseOps...)`. -/
structure TxnModel where
  cmps : List CmpModel
  thenOps : List TxnOp
  elseOps : List TxnOp

/-- The empty transaction (what `kv.Txn(ctx)` starts from). -/
def TxnModel.empty : TxnModel := { cmps := [], thenOps := [], elseOps := [] }

/-- The result of an operation: a get's selected key-values (in key order) and the number of keys
in its range; a put; a delete's number of deleted keys; a nested transaction's outcome (whether its
comparisons held) and its chosen branch's results. -/
inductive TxnOpResult where
  | range (sel : List EtcdKv) (count : Nat)
  | put
  | delete (deleted : Nat)
  | txn (ok : Bool) (rs : List TxnOpResult)

/-- The operation an `Op` (`Then`'s and `Else`'s arguments) stands for in a transaction: a range
at the current revision, a put (with `WithIgnoreLease` and no lease, a put keeping the key's lease;
with `WithIgnoreValue` and no value, a put keeping its value), a delete; nothing for another
revision or what etcd rejects (a value with `WithIgnoreValue`, a lease with `WithIgnoreLease`). A
nested transaction's `Op` has no `OpFull` model of its own: `OpT` (below) describes it. -/
def txnOpOf (o : OpFull) : Option TxnOp :=
  if o.t = W64 1 then (if o.base.rev = W64 0 then some (.get o) else none)
  else if o.t = W64 2 then
    (if o.ignoreValue = false ∧ o.ignoreLease = false then some (.put o.key o.val o.leaseID)
     else if o.ignoreValue = false ∧ o.ignoreLease = true ∧ o.leaseID = W64 0 then
       some (.putKeep o.key o.val)
     else if o.ignoreValue = true ∧ o.val = [] ∧ o.ignoreLease = false then
       some (.putIgnVal o.key (some o.leaseID))
     else if o.ignoreValue = true ∧ o.val = [] ∧ o.ignoreLease = true ∧ o.leaseID = W64 0 then
       some (.putIgnVal o.key none)
     else none)
  else if o.t = W64 3 then some (.delete o)
  else none

/-- A put of `key` at revision `r` (see the module docstring). -/
def putKv (r : w64) (key value : GoString) (lease : w64) (s : List EtcdKv) : List EtcdKv :=
  let nv : EtcdKv := match s.find? (fun v => decide (v.key = key)) with
    | some v => { v with modRev := r, version := v.version + W64 1, value := value, lease := lease }
    | none => { key := key, createRev := r, modRev := r, version := W64 1, value := value,
                lease := lease }
  btInsert etcdKvLess nv s

mutual
/-- One operation, at revision `r`, on the state `s`: the state after it and its result. -/
def applyTxnOp (r : w64) (s : List EtcdKv) : TxnOp → List EtcdKv × TxnOpResult
  | .get o => (s, .range (rangeSel s o) (rangeIn s o).length)
  | .put k v l => (putKv r k v l s, .put)
  | .putKeep k v =>
    (putKv r k v (((s.find? (fun v => decide (v.key = k))).map EtcdKv.lease).getD (W64 0)) s, .put)
  | .delete o => (s.filter (fun v => !inRange o.key o.base.rangeEnd v.key),
      .delete (rangeIn s o).length)
  | .putIgnVal k l =>
    (putKv r k (((s.find? (fun v => decide (v.key = k))).map EtcdKv.value).getD [])
      (l.getD (((s.find? (fun v => decide (v.key = k))).map EtcdKv.lease).getD (W64 0))) s, .put)
  | .txn cs ts es =>
    match cs.all (cmpHolds s) with
    | true => ((runOps r s ts).1, .txn true (runOps r s ts).2)
    | false => ((runOps r s es).1, .txn false (runOps r s es).2)

/-- Operations in order, each on the state the previous one left. -/
def runOps (r : w64) : List EtcdKv → List TxnOp → List EtcdKv × List TxnOpResult
  | s, [] => (s, [])
  | s, op :: ops =>
    let p := applyTxnOp r s op
    let q := runOps r p.1 ops
    (q.1, p.2 :: q.2)
end

/-- The branch the comparisons choose. -/
def TxnModel.branch (t : TxnModel) (ok : Bool) : List TxnOp := if ok then t.thenOps else t.elseOps

/-- **A transaction** at revision `r` on the state `s`: whether the comparisons held, the state
after the chosen branch, and its operations' results. -/
def runTxn (r : w64) (s : List EtcdKv) (t : TxnModel) : Bool × List EtcdKv × List TxnOpResult :=
  let ok := t.cmps.all (cmpHolds s)
  let q := runOps r s (t.branch ok)
  (ok, q.1, q.2)

mutual
/-- An operation's result is a write: a put, a delete of some key, or a nested transaction whose
chosen branch wrote. -/
def TxnOpResult.wrote : TxnOpResult → Bool
  | .put => true
  | .delete n => n != 0
  | .range _ _ => false
  | .txn _ rs => TxnOpResult.wroteL rs

/-- Some result of the list is a write (`List.any TxnOpResult.wrote`, `wroteL_eq`). -/
def TxnOpResult.wroteL : List TxnOpResult → Bool
  | [] => false
  | r :: rs => r.wrote || TxnOpResult.wroteL rs
end

theorem TxnOpResult.wroteL_eq : ∀ rs : List TxnOpResult, TxnOpResult.wroteL rs = rs.any TxnOpResult.wrote
  | [] => rfl
  | r :: rs => by simp [TxnOpResult.wroteL, TxnOpResult.wroteL_eq rs]

/-- An operation that makes a transaction linearizable: anything but a serializable get (a nested
transaction too: etcd's `IsTxnSerializable` looks at the top-level operations only). -/
def TxnOp.linearizable : TxnOp → Bool
  | .get o => !o.base.serializable
  | _ => true

/-- **The transaction is linearizable**: one of its operations (either branch) is not a
serializable get. etcd serves a transaction whose operations are all serializable gets (or
which has none) from the member's own state, without the read barrier (`IsTxnSerializable`,
`EtcdServer.Txn`): its revision may be behind one the caller has seen. -/
def TxnModel.linearizable (t : TxnModel) : Bool := (t.thenOps ++ t.elseOps).any TxnOp.linearizable

/-- The transaction wrote (so it has a revision of its own). -/
def txnWrote (rs : List TxnOpResult) : Bool := rs.any TxnOpResult.wrote

theorem delete_noWrite (s : List EtcdKv) (o : OpFull) (h0 : (rangeIn s o).length = 0) :
    s.filter (fun v => !inRange o.key o.base.rangeEnd v.key) = s := by
  rw [List.filter_eq_self]
  intro v hv
  have : v ∉ rangeIn s o := by
    rw [List.length_eq_zero_iff] at h0; rw [h0]; simp
  unfold rangeIn at this
  simp only [List.mem_filter, not_and] at this
  simpa using this hv

mutual
/-- An operation that did not write leaves the state as it was. -/
theorem applyTxnOp_noWrite (r : w64) (s : List EtcdKv) :
    ∀ op : TxnOp, (applyTxnOp r s op).2.wrote = false → (applyTxnOp r s op).1 = s
  | .get o => fun _ => rfl
  | .put k v l => by simp [applyTxnOp, TxnOpResult.wrote]
  | .putKeep k v => by simp [applyTxnOp, TxnOpResult.wrote]
  | .putIgnVal k l => by simp [applyTxnOp, TxnOpResult.wrote]
  | .delete o => by
    simp only [applyTxnOp, TxnOpResult.wrote, bne_eq_false_iff_eq]
    exact delete_noWrite s o
  | .txn cs ts es => by
    simp only [applyTxnOp]
    split
    · simp only [TxnOpResult.wrote, TxnOpResult.wroteL_eq]
      exact runOps_noWrite r s ts
    · simp only [TxnOpResult.wrote, TxnOpResult.wroteL_eq]
      exact runOps_noWrite r s es

/-- Operations that did not write leave the state as it was. -/
theorem runOps_noWrite (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), txnWrote (runOps r s ops).2 = false →
      (runOps r s ops).1 = s
  | _, [] => fun _ => rfl
  | s, op :: ops => by
    intro h
    simp only [runOps, txnWrote, List.any_cons, Bool.or_eq_false_iff] at h ⊢
    obtain ⟨h0, h1⟩ := h
    have hs := applyTxnOp_noWrite r s op h0
    have h1' := runOps_noWrite r (applyTxnOp r s op).1 ops h1
    rw [h1', hs]
end

mutual
/-- The keys an operation touches (and a nested transaction compares) are under the prefix
`pfx`. -/
def TxnOp.Under (pfx : GoString) : TxnOp → Prop
  | .get o => KeyRangeUnder pfx o.key o.base.rangeEnd
  | .put k _ _ => pfx <+: k
  | .delete o => KeyRangeUnder pfx o.key o.base.rangeEnd
  | .putKeep k _ => pfx <+: k
  | .putIgnVal k _ => pfx <+: k
  | .txn cs ts es => (∀ c ∈ cs, KeyRangeUnder pfx c.key c.rangeEnd) ∧ TxnOp.UnderL pfx ts ∧
      TxnOp.UnderL pfx es

/-- Every operation of the list is under `pfx`. -/
def TxnOp.UnderL (pfx : GoString) : List TxnOp → Prop
  | [] => True
  | op :: ops => op.Under pfx ∧ TxnOp.UnderL pfx ops
end

/-- Every key the transaction compares or touches is under the prefix `pfx` (the client's
contract is stated per prefix, as `isEtcdKV`'s). -/
def TxnModel.Under (pfx : GoString) (t : TxnModel) : Prop :=
  (∀ c ∈ t.cmps, KeyRangeUnder pfx c.key c.rangeEnd) ∧ (∀ op ∈ t.thenOps, op.Under pfx) ∧
    (∀ op ∈ t.elseOps, op.Under pfx)

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

/-- **A key's record is determined by its mod revision** (an axiom about etcd's history): two
states (at any revisions) holding the same key with the same mod revision hold the same
key-value. A revision is one transaction's, which writes a key at most once (etcd rejects a
transaction writing one key twice), and what it writes (value, lease) and the key's create
revision and version then are fixed by the history; a key is never changed without a new mod
revision (a lease's expiry deletes it). Used by the STM: a commit's comparison
`ModRevision(key) = m` on the state before it, for a key read with mod revision `m`, means the
key still holds what was read. -/
axiom etcdState_modrev_det {GF : BundledGFunctors} (a b : w64) (pfx : GoString)
    (s s' : List EtcdKv) :
  etcdState (GF := GF) a pfx s ∗ etcdState b pfx s' ⊢
    ⌜∀ v ∈ s, ∀ v' ∈ s', v.key = v'.key → v.modRev = v'.modRev → v = v'⌝

/-- **The revision `r` was made by the holder's commit** (an axiom: a fact about the server, as
`etcdState`): an exclusive token, which the client's contract gives the caller of a commit that
wrote (`txnCommitResultTok`, `putResult`). A committed write is its own revision: etcd applies
the requests one at a time, and each that writes (a put, a delete of some key, a transaction
whose chosen branch does) advances the revision by one (`Txn` with only comparisons and gets
answers at the current revision and makes none, hence no token for it). Its one law is
exclusivity (`etcdRevToken_excl`): two commits never made the same revision. -/
axiom etcdRevToken {GF : BundledGFunctors} (r : w64) : IProp GF

/-- Two tokens for one revision: impossible (a revision is one commit's). -/
axiom etcdRevToken_excl {GF : BundledGFunctors} (r : w64) :
  etcdRevToken (GF := GF) r ∗ etcdRevToken r ⊢ False

section client
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The client's transactions -/

/-- The `*pb.RangeResponse` `rr` answers the get `o` whose selection is `sel` and whose range
has `count` keys (read-only), and has a header (etcd sets one on every range response: the
revision of the transaction's view, which nothing here needs). -/
def rangeRespAt (rr : Loc) (o : OpFull) (sel : List EtcdKv) (count : Nat) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ps : List Loc) (kvs : List EtcdKv),
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" rr ↦□ sl ∗ sl ↦*□ ps ∗ kvPtrsAt ps kvs ∗
    ⌜rangeKvsOk o sel kvs⌝ ∗
    structFieldRef etcdserverpb.RangeResponse go!"Count" rr ↦□ W64 (count : Int) ∗
    ∃ (h : Loc) (hr : w64), structFieldRef etcdserverpb.RangeResponse go!"Header" rr ↦□ h ∗
      ⌜h ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ hr)

instance rangeRespAt_persistent (rr : Loc) (o : OpFull) (sel : List EtcdKv) (count : Nat) :
    Persistent (rangeRespAt (GF := GF) rr o sel count) := by
  unfold rangeRespAt; infer_instance

/-- The `*pb.ResponseOp` `p` (not nil) is the response of the operation `op` with result `res`
(read-only): its `Response` oneof holds the wrapper of the operation's kind. -/
def txnOpRespAt (p : Loc) (op : TxnOp) (res : TxnOpResult) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ ∃ u : GoInterface, structFieldRef etcdserverpb.ResponseOp go!"Response" p ↦□ u ∗
    match op, res with
    | .get o, .range sel n => iprop(∃ (w rr : Loc),
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseRange.ty) #w⌝ ∗
        structFieldRef etcdserverpb.ResponseOp_ResponseRange go!"ResponseRange" w ↦□ rr ∗
        ⌜rr ≠ null⌝ ∗ rangeRespAt rr o sel n)
    | .put _ _ _, .put => iprop(∃ (w pr : Loc),
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w⌝ ∗
        structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ pr ∗
        ⌜pr ≠ null⌝)
    | .putKeep _ _, .put => iprop(∃ (w pr : Loc),
        ⌜u = interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w⌝ ∗
        structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ pr ∗
        ⌜pr ≠ null⌝)
    | .putIgnVal _ _, .put => iprop(∃ (w pr : Loc),
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
that etcd has reached `lo`: an error; or a response at a revision `r` (reached, below
`2^63 - 1`, and at least `lo` if the transaction is linearizable: `TxnModel.linearizable`) and a
state `s` (sorted, under `pfx`) such that the response is the transaction run at `r` on `s`
(`runTxn`), and either it wrote, `s` was etcd's state at `r - 1` and the state it leaves is
etcd's state at `r`, or it did not write and `s` is etcd's state at `r` (which it leaves
unchanged: `runOps_noWrite`). -/
def txnCommitResult (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (s : List EtcdKv),
      txnRespAt resp r (runTxn r s t).1 (t.branch (runTxn r s t).1) (runTxn r s t).2.2 ∗
      etcdReached r ∗
      ⌜(t.linearizable = true → sint.Z lo ≤ sint.Z r) ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧
        EtcdStateWf pfx s⌝ ∗
      txnStates pfx r s (runTxn r s t).2.1 (txnWrote (runTxn r s t).2.2)))

instance txnCommitResult_persistent (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc)
    (err : GoInterface) : Persistent (txnCommitResult (GF := GF) pfx lo t resp err) := by
  unfold txnCommitResult; infer_instance

/-- **What `Commit()` returns, with the revision's token**: `txnCommitResult`, and, if the
transaction wrote, the token of its revision (`etcdRevToken r`: a committed write is its own
revision; a read-only transaction makes none). What the builder's `Commit` gives
(`txnBuilderSpec`); `txnCommitResultTok_result` drops the token. -/
def txnCommitResultTok (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (s : List EtcdKv),
      txnRespAt resp r (runTxn r s t).1 (t.branch (runTxn r s t).1) (runTxn r s t).2.2 ∗
      etcdReached r ∗
      ⌜(t.linearizable = true → sint.Z lo ≤ sint.Z r) ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧
        EtcdStateWf pfx s⌝ ∗
      txnStates pfx r s (runTxn r s t).2.1 (txnWrote (runTxn r s t).2.2) ∗
      (if txnWrote (runTxn r s t).2.2 then etcdRevToken r else True)))

/-- The token dropped: `txnCommitResult`'s facts (persistent). -/
theorem txnCommitResultTok_result (pfx : GoString) (lo : w64) (t : TxnModel) (resp : Loc)
    (err : GoInterface) :
    txnCommitResultTok (GF := GF) pfx lo t resp err ⊢ txnCommitResult pfx lo t resp err := by
  unfold txnCommitResultTok txnCommitResult
  iintro (%H | ⟨%H, %r, %s, #Hresp, #Hr, %Hp, #Hts, -⟩)
  · ileft; ipureintro; exact H
  · iright
    isplitr
    · ipureintro; exact H
    iexists r, s
    iframe Hresp Hr Hts
    ipureintro; exact Hp

/-- **What `Commit()` returns for any transaction** (one with a key outside the prefix the
contract speaks for, say): an error, or a response with a header and `Succeeded`, read-only, and
nothing else (`Election.Resign` and `Proclaim` after a failed `Proclaim` commit a transaction on the
key `""`). -/
def txnAnyResult (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (hdr : Loc) (ok : Bool),
      structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦□ ok))

instance txnAnyResult_persistent (resp : Loc) (err : GoInterface) :
    Persistent (txnAnyResult (GF := GF) resp err) := by
  unfold txnAnyResult; infer_instance

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
transaction under `pfx`, returns `txnCommitResult` with the token of the revision it made if it
wrote (`txnCommitResultTok`), and for any transaction `txnAnyResult`. -/
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
          txnCommitResultTok pfx lo b.model resp err }}) ∗
    (□ ∀ (b : TxnBuild),
      {{ B b }}
        (App (Val #(methods t.ty go!"Commit" t.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); txnAnyResult resp err }}))

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

/-! ## Read transactions: gets at the current or an earlier revision -/

/-- An operation of a read transaction (`Txn(ctx).Then(ops...).Commit()` with gets only): a get
(`OpGet`) of a range under `pfx`, at the current revision (`rev = 0`) or an earlier one
(`WithRev(rev)`), serializable or not, with any of the response options `rangeKvsOk` covers. -/
def readOpOk (pfx : GoString) (o : OpFull) : Prop :=
  o.t = W64 1 ∧ KeyRangeUnder pfx o.key o.base.rangeEnd

/-- The revision a get `o` of a read transaction answered at `r` reads: `r` for `rev = 0`,
otherwise its `rev`. -/
def readRevAt (r : w64) (o : OpFull) : w64 := if o.base.rev = W64 0 then r else o.base.rev

/-- **What a read transaction's `Commit()` returns** for the gets `os` under `pfx`, called
knowing that etcd has reached `lo`: an error (among others `ErrCompacted` or `ErrFutureRev` for a
revision etcd no longer has or does not have yet); or a response with header revision `r`
(reached, positive, below `2^63 - 1`, at least `lo` unless every get is serializable: etcd then
answers from the member's own state, `IsTxnSerializable`), `Succeeded`, and, for each get `o`, in
order, its range response on etcd's state at `readRevAt r o` (a positive revision at most `r`).
The `Txn` contract `isEtcdTxnKV` covers gets at the current revision only (`txnOpOf`); a get at
an earlier revision reads another state than the transaction's, hence this contract, for
transactions of gets alone (the STM's reads, `stm.fetch`). -/
def readTxnResult (pfx : GoString) (lo : w64) (os : List OpFull) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (hdr : Loc) (sl : GoSlice) (ps : List Loc),
      structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ ⌜hdr ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r ∗
      structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦□ true ∗
      structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ sl ∗ sl ↦*□ ps ∗
      etcdReached r ∗
      ⌜ps.length = os.length ∧
        (os.any (fun o => !o.base.serializable) = true → sint.Z lo ≤ sint.Z r) ∧
        0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1⌝ ∗
      □ ∀ (i : Nat) (p : Loc) (o : OpFull), ⌜ps[i]? = some p⌝ -∗ ⌜os[i]? = some o⌝ -∗
        ∃ (s : List EtcdKv) (n : Nat), □ etcdState (readRevAt r o) pfx s ∗
          ⌜EtcdStateWf pfx s ∧ 0 < sint.Z (readRevAt r o) ∧ sint.Z (readRevAt r o) ≤ sint.Z r⌝ ∗
          txnOpRespAt p (.get o) (.range (rangeSel s o) n)))

instance readTxnResult_persistent (pfx : GoString) (lo : w64) (os : List OpFull) (resp : Loc)
    (err : GoInterface) : Persistent (readTxnResult (GF := GF) pfx lo os resp err) := by
  unfold readTxnResult; infer_instance

/-- **A read transaction's builder** `t` with abstract state `B` (`none` before `Then`, the gets
after it): `Then(ops...)` of gets under `pfx` (`readOpOk`), then `Commit()`, returning
`readTxnResult`. -/
def readTxnBuilderSpec (t : GoInterfaceOk) (pfx : GoString)
    (B : Option (List OpFull) → IProp GF) : IProp GF :=
  iprop(
    (□ ∀ (sl : GoSlice) (os : List OpFull),
      {{ B none ∗ opsAt sl os ∗ ⌜∀ o ∈ os, readOpOk pfx o⌝ }}
        (App (Val #(methods t.ty go!"Then" t.v)) (Val #sl))
      {{ RET #(GoInterface.ok t); B (some os) }}) ∗
    (□ ∀ (os : List OpFull) (lo : w64),
      {{ B (some os) ∗ etcdReached lo }}
        (App (Val #(methods t.ty go!"Commit" t.v)) (Val #()))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          readTxnResult pfx lo os resp err }}))

instance readTxnBuilderSpec_persistent (t : GoInterfaceOk) (pfx : GoString)
    (B : Option (List OpFull) → IProp GF) : Persistent (readTxnBuilderSpec t pfx B) := by
  unfold readTxnBuilderSpec; infer_instance

/-- **The client's read transactions** (`clientv3.KV`'s `Txn`, used with gets alone; a
definition, the assumption a caller makes of `client.KV`, beside `isEtcdTxnKV` for the same
method): `kv.Txn(ctx)` returns a builder in its empty state. -/
def isEtcdReadTxnKV (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    {{ context.isContext ctx cs }}
      (App (Val #(methods kv.ty go!"Txn" kv.v)) (Val #(GoInterface.ok ctx)))
    {{ (t : GoInterfaceOk), RET #(GoInterface.ok t);
        ∃ B : Option (List OpFull) → IProp GF, B none ∗ readTxnBuilderSpec t pfx B }})

instance isEtcdReadTxnKV_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdReadTxnKV (GF := GF) kv pfx) := by
  unfold isEtcdReadTxnKV; infer_instance

/-! ## The client's deletes -/

/-- The one-operation transaction of a delete `o` (`kv.Delete` is `kv.Do(OpDelete(...))`, a
`DeleteRange` request, which etcd applies as a transaction of that one operation). -/
def deleteTxn (o : OpFull) : TxnModel := { cmps := [], thenOps := [.delete o], elseOps := [] }

/-- **What `kv.Delete` returns** for the delete `o` under the prefix `pfx`, called knowing that etcd
has reached `lo`: an error, or a revision `r` (at least `lo`, reached, below `2^63 - 1`) and a state
`s` such that the delete ran as a one-operation transaction (`deleteTxn`): if it deleted a key, `s`
was etcd's state at `r - 1` and the state without the range's keys is its state at `r`; if it
deleted nothing, `s` is etcd's state at `r` (`txnStates`). The response itself is not modelled
(`client/v3/concurrency` ignores it). -/
def deleteResult (pfx : GoString) (lo : w64) (o : OpFull) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (s : List EtcdKv), etcdReached r ∗
      ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf pfx s⌝ ∗
      txnStates pfx r s (runTxn r s (deleteTxn o)).2.1 (txnWrote (runTxn r s (deleteTxn o)).2.2)))

instance deleteResult_persistent (pfx : GoString) (lo : w64) (o : OpFull) (err : GoInterface) :
    Persistent (deleteResult (GF := GF) pfx lo o err) := by
  unfold deleteResult; infer_instance

/-- **The client's deletes** (`clientv3.KV`'s `Delete(ctx, key, opts...)`; a definition, the
assumption a caller makes of `client.KV`, as `isEtcdKV` for `Get`): for options with which
`OpDelete` does not panic, of a range under `pfx`, the result is `deleteResult` (linearizable, as
`Get` and `Commit`). -/
def isEtcdDeleteKV (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)) (lo : w64),
    {{ context.isContext ctx cs ∗ optsAt sl gs ∗ etcdReached lo ∗
        ⌜¬ opDeletePanics key gs ∧
          KeyRangeUnder pfx (opDeleteModel key gs).key (opDeleteModel key gs).base.rangeEnd⌝ }}
      (App (App (App (Val #(methods kv.ty go!"Delete" kv.v)) (Val #(GoInterface.ok ctx)))
        (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        deleteResult pfx lo (opDeleteModel key gs) err }})

instance isEtcdDeleteKV_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdDeleteKV (GF := GF) kv pfx) := by
  unfold isEtcdDeleteKV; infer_instance

/-! ## The client's puts (`client/v3/experimental/recipes`' addition) -/

/-- The one-operation transaction of a put `op` (`kv.Put` is `kv.Do(OpPut(...))`, a `Put`
request, which etcd applies as a transaction of that one operation, as a delete: `deleteTxn`).
The recipes' addition (`RemoteKV.Put`, the double barrier's ready key), stated through the
transaction model: no new etcd semantics. -/
def putTxn (op : TxnOp) : TxnModel := { cmps := [], thenOps := [op], elseOps := [] }

/-- **What `kv.Put` returns** for the put `op` (`txnOpOf` of `OpPut`'s model) under the prefix
`pfx`, called knowing that etcd has reached `lo`: an error, or a revision `r` (at least `lo`,
reached, below `2^63 - 1`) and a state `s` such that the put ran as a one-operation transaction
(`putTxn`): `s` was etcd's state at `r - 1` and the state with the put applied is its state at
`r` (`txnStates`; a put always writes), and the caller holds the token of the revision `r`
(`etcdRevToken`: a committed write is its own revision). The response itself is not modelled
(the recipes ignore it). The recipes' addition, as `deleteResult`. -/
def putResult (pfx : GoString) (lo : w64) (op : TxnOp) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∨
    (⌜err = GoInterface.nil⌝ ∗ ∃ (r : w64) (s : List EtcdKv), etcdReached r ∗
      ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf pfx s⌝ ∗
      txnStates pfx r s (runTxn r s (putTxn op)).2.1 (txnWrote (runTxn r s (putTxn op)).2.2) ∗
      etcdRevToken r))

/-- **The client's puts** (`clientv3.KV`'s `Put(ctx, key, val, opts...)`; a definition, the
assumption a caller makes of `client.KV`, as `isEtcdDeleteKV` for `Delete`): for options with
which `OpPut` does not panic and which make a put a transaction can run (`txnOpOf`), of a key
under `pfx`, the result is `putResult` (linearizable, as `Delete` and `Commit`).
`client/v3/experimental/recipes`' addition (the first plain put a verified client makes). -/
def isEtcdPutKV (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key val : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)) (op : TxnOp) (lo : w64),
    {{ context.isContext ctx cs ∗ optsAt sl gs ∗ etcdReached lo ∗
        ⌜¬ (opPutModel key val gs).putPanics ∧ txnOpOf (opPutModel key val gs) = some op ∧
          op.Under pfx⌝ }}
      (App (App (App (App (Val #(methods kv.ty go!"Put" kv.v)) (Val #(GoInterface.ok ctx)))
        (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); putResult pfx lo op err }})

instance isEtcdPutKV_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdPutKV (GF := GF) kv pfx) := by
  unfold isEtcdPutKV; infer_instance

/-! ## The client at `context.TODO()` (`client/v3/experimental/recipes`' addition) -/

/-- `context.TODO()`: a `todoCtx{}` as a `Context` (`Spec/context/TODO.lean`). Its `Done()` is
`nil` (it is never canceled), so it is not an `isContext` (whose `Done()` returns a channel), and
the contracts above, which take an `isContext`, do not cover a call with it. -/
abbrev todoCtxVal : GoInterfaceOk :=
  interface.mk context.todoCtx.ty #(zero_val context.todoCtx)

/-- **A get's `More` flag** (read-only): for the get `o` answered without error at the header
revision `r`, `resp.More` is `more`; for a get at the latest revision of a range under `pfx`, it
is etcd's: whether a positive limit cut the selection (`rangeSel`) on etcd's state at `r`
(`asembleRangeResponse`: `More` is set when the range result, fetched with the limit plus one or
in full for a sort or a filter, has more key-values than the limit; a count-only get fetches
none). The queue's `Dequeue` reads it (`More`: retry, the first item claimed by others). The
recipes' addition, beside `kvGetResult` in `isEtcdKVTodo`. (Classical, as `getRespRange`.) -/
def getRespMore (pfx : GoString) (o : OpFull) (resp : Loc) (err : GoInterface) : IProp GF :=
  open Classical in
  iprop(⌜err ≠ GoInterface.nil⌝ ∨ ∃ (r : w64) (more : Bool), getRespRev resp r ∗
    structFieldRef go_etcd_io.etcd.client.v3.GetResponse go!"More" resp ↦□ more ∗
    if o.base.rev = W64 0 ∧ KeyRangeUnder pfx o.key o.base.rangeEnd then
      iprop(∃ s : List EtcdKv, □ etcdState r pfx s ∗
        ⌜more = (!o.base.countOnly && decide (0 < sint.Z o.base.limit) &&
          decide (sint.Z o.base.limit < ((rangeSel s o).length : Int)))⌝)
    else iprop(True))

instance getRespMore_persistent (pfx : GoString) (o : OpFull) (resp : Loc) (err : GoInterface) :
    Persistent (getRespMore (GF := GF) pfx o resp err) := by
  unfold getRespMore; split <;> infer_instance

/-- **`isEtcdKV` at `context.TODO()`** (a definition, the assumption a caller makes of
`client.KV`): `kv.Get(context.TODO(), key, opts...)` returns `kvGetResult`, as `isEtcdKV` does
for a context (whose descriptor no postcondition mentions), and the response's `More` flag
(`getRespMore`). The recipes' addition: every call
the recipes make through `client.KV` passes `context.TODO()`. The options' closures may need a
resource `R` (`optsAtRes`: the client calls them one at a time, in the caller's goroutine), which
the call gives back (`WithFirstKey()`'s sort option writes a variable it captured; `optsAt_res`
for the others). -/
def isEtcdKVTodo (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF)
      (lo : w64),
    {{ optsAtRes sl gs R ∗ R ∗ etcdReached lo ∗ ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ }}
      (App (App (App (Val #(methods kv.ty go!"Get" kv.v)) (Val #(GoInterface.ok todoCtxVal)))
        (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        R ∗ kvGetResult pfx lo (opGetModel key gs) resp err ∗
        getRespMore pfx (opGetModel key gs) resp err }})

instance isEtcdKVTodo_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdKVTodo (GF := GF) kv pfx) := by
  unfold isEtcdKVTodo; infer_instance

/-- **`isEtcdTxnKV` at `context.TODO()`**: `kv.Txn(context.TODO())` returns a builder in its
empty state. The recipes' addition, as `isEtcdKVTodo`. -/
def isEtcdTxnKVTodo (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ {{ True }}
      (App (Val #(methods kv.ty go!"Txn" kv.v)) (Val #(GoInterface.ok todoCtxVal)))
    {{ (t : GoInterfaceOk), RET #(GoInterface.ok t);
        ∃ B : TxnBuild → IProp GF, B TxnBuild.empty ∗ txnBuilderSpec t pfx B }})

instance isEtcdTxnKVTodo_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdTxnKVTodo (GF := GF) kv pfx) := by
  unfold isEtcdTxnKVTodo; infer_instance

/-- **`isEtcdDeleteKV` at `context.TODO()`**: `kv.Delete(context.TODO(), key, opts...)` returns
`deleteResult`. The recipes' addition, as `isEtcdKVTodo`. -/
def isEtcdDeleteKVTodo (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (lo : w64),
    {{ optsAt sl gs ∗ etcdReached lo ∗
        ⌜¬ opDeletePanics key gs ∧
          KeyRangeUnder pfx (opDeleteModel key gs).key (opDeleteModel key gs).base.rangeEnd⌝ }}
      (App (App (App (Val #(methods kv.ty go!"Delete" kv.v)) (Val #(GoInterface.ok todoCtxVal)))
        (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        deleteResult pfx lo (opDeleteModel key gs) err }})

instance isEtcdDeleteKVTodo_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdDeleteKVTodo (GF := GF) kv pfx) := by
  unfold isEtcdDeleteKVTodo; infer_instance

/-- **`isEtcdPutKV` at `context.TODO()`**: `kv.Put(context.TODO(), key, val, opts...)` returns
`putResult`. The recipes' addition, as `isEtcdKVTodo`. -/
def isEtcdPutKVTodo (kv : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (op : TxnOp)
      (lo : w64),
    {{ optsAt sl gs ∗ etcdReached lo ∗
        ⌜¬ (opPutModel key val gs).putPanics ∧ txnOpOf (opPutModel key val gs) = some op ∧
          op.Under pfx⌝ }}
      (App (App (App (App (Val #(methods kv.ty go!"Put" kv.v)) (Val #(GoInterface.ok todoCtxVal)))
        (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); putResult pfx lo op err }})

instance isEtcdPutKVTodo_persistent (kv : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdPutKVTodo (GF := GF) kv pfx) := by
  unfold isEtcdPutKVTodo; infer_instance

/-- The key `key` is absent from etcd's state at `r` under the prefix `pfx` (persistent). -/
def etcdAbsent (pfx key : GoString) (r : w64) : IProp GF :=
  iprop(∃ s : List EtcdKv, □ etcdState r pfx s ∗ ⌜∀ v ∈ s, v.key ≠ key⌝)

instance etcdAbsent_persistent (pfx key : GoString) (r : w64) :
    Persistent (etcdAbsent (GF := GF) pfx key r) := by
  unfold etcdAbsent; infer_instance

/-! ## The client's range watch (a key, or a prefix) -/

/-- A watch of the range of `o` (`[o.key, o.base.rangeEnd)`: one key if the range end is empty,
a prefix with `WithPrefix`) from revision `rev` (`WithRev(rev)`), with none of the options that
change which events are sent or how (`WithPrevKV`, `WithFragment`, the event filters); progress
and created notifications allowed, requested or not. -/
def OpFull.isRangeWatch (rev : w64) (o : OpFull) : Bool :=
  decide (o.t = W64 1 ∧ o.base.rev = rev ∧ o.base.prevKV = false ∧ o.base.fragment = false ∧
    o.base.filterPut = false ∧ o.base.filterDelete = false)

/-- A delete event's `*KeyValue` `l`: its `Value` (some byte slice) and `Lease` fields can be read
(read-only). -/
def delKvAt (l : Loc) : IProp GF :=
  iprop(∃ (valSl : GoSlice) (val : GoString) (lease : w64),
    structFieldRef mvccpb.KeyValue go!"Value" l ↦□ valSl ∗ valSl ↦*□ val ∗
    structFieldRef mvccpb.KeyValue go!"Lease" l ↦□ lease)

instance delKvAt_persistent (l : Loc) : Persistent (delKvAt (GF := GF) l) := by
  unfold delKvAt; infer_instance

/-- **etcd's contract for one event** `e` of a watch of the range of `o` (under `pfx`) from
revision `rev`: it is a put or a delete (`mvccpb.Event_EventType` has no other value); its key is
in the range; its revision is at least `rev`, below `2^63 - 1`, and
etcd has reached it; a delete event at `e.rev` means the key is absent from etcd's state at
`e.rev`, and its `*KeyValue`'s `Value` and `Lease` fields can be read (`delKvAt`: etcd sends the
deleted key with empty other fields; the contract does not say which values); a put event's
`*KeyValue` holds a key-value `v` of that key, modified at `e.rev`, which is in etcd's state at
`e.rev`. (etcd emits a delete event only for a key a `DeleteRange` or a lease's expiry removes, and
the events of one revision are one transaction's, which cannot write one key twice, so the
key-value an event carries is the key's at that revision.) -/
def rangeWatchEvOk (pfx : GoString) (o : OpFull) (rev : w64) (e : EvModel) : IProp GF :=
  iprop(⌜inRange o.key o.base.rangeEnd e.key = true ∧ sint.Z rev ≤ sint.Z e.rev ∧
      sint.Z e.rev < 2 ^ 63 - 1 ∧ (e.typ = W32 0 ∨ e.typ = W32 1)⌝ ∗ etcdReached e.rev ∗
    (⌜e.typ = W32 1⌝ -∗ etcdAbsent pfx e.key e.rev ∗ delKvAt e.kv) ∗
    (⌜e.typ = W32 0⌝ -∗ ∃ v : EtcdKv, kvValAt e.kv v ∗ ⌜v.key = e.key ∧ v.modRev = e.rev⌝ ∗
      ∃ s : List EtcdKv, □ etcdState e.rev pfx s ∗ ⌜v ∈ s ∧ EtcdStateWf pfx s⌝))

instance rangeWatchEvOk_persistent (pfx : GoString) (o : OpFull) (rev : w64) (e : EvModel) :
    Persistent (rangeWatchEvOk (GF := GF) pfx o rev e) := by
  unfold rangeWatchEvOk; infer_instance

/-- **etcd's range watch contract**, for one response modelled by `r`, received when the stream
is at position `c` (the revision of the last event before it; `rev - 1` at the start), after
which it is at `c'`: its events are sorted by revision, all above `c`, each satisfying
`rangeWatchEvOk`; the position becomes the last event's revision (`c` if there is none). Nothing
else is promised: errors, compactions, cancellations, created and progress notifications, any;
and no event is promised (the stream may skip some: the contract does not say it is complete). -/
def rangeWatchRespOk (pfx : GoString) (o : OpFull) (rev c c' : w64) (r : RespModel) :
    IProp GF :=
  iprop(⌜EvRevSorted r.events ∧ (∀ e ∈ r.events, sint.Z c < sint.Z e.rev) ∧
      c' = (r.events.getLast?.map EvModel.rev).getD c⌝ ∗
    □ ∀ (i : Nat) (e : EvModel), ⌜r.events[i]? = some e⌝ -∗ rangeWatchEvOk pfx o rev e)

instance rangeWatchRespOk_persistent (pfx : GoString) (o : OpFull) (rev c c' : w64)
    (r : RespModel) : Persistent (rangeWatchRespOk (GF := GF) pfx o rev c c' r) := by
  unfold rangeWatchRespOk; infer_instance

/-- A watch response's header `h`: for a response with events, the receiver owns its `Revision`
field (the client builds each event response from its own gRPC message, whose header no other
watch receives, and does not read it after sending it); otherwise read-only (`hdrAt`: a progress
notification's header is shared by every watch it is broadcast to). -/
def watchHdrOwn (h : Loc) (r : RespModel) : IProp GF :=
  if r.events = [] then hdrAt h r.hdrRev
  else iprop(⌜h ≠ null⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ r.hdrRev)

/-- The `i`-th response `v` of a range watch channel: modelled by some `r` (its events, read-only;
its header, `watchHdrOwn`; the flags), satisfying the contract from the position before it to the
one after it (`γ.cur`, a monotone list of positions). -/
def rangeWatchElem (γ : EtcdWatchNames) (pfx : GoString) (o : OpFull) (rev : w64) (i : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (c c' : w64), eventsAt v.Events' r.events ∗ watchHdrOwn v.Header' r ∗
    ⌜v.CompactRevision' = r.compactRev ∧ v.Canceled' = r.canceled ∧ v.Created' = r.created⌝ ∗
    monoListIdxOwn γ.cur i.toNat c ∗ monoListIdxOwn γ.cur (i.toNat + 1) c' ∗
    rangeWatchRespOk pfx o rev c c' r)

/-- **The client's range watch** (`clientv3.Watcher`'s `Watch`; a definition, as `isEtcdWatcher`
for the cache's prefix watch): a watch of a range under `pfx` (a key, or a sub-prefix with
`WithPrefix`) from revision `rev ≥ 0` (`isRangeWatch`; the options must not make `OpWatch` panic)
returns an SPSC channel (the caller consumes it) whose responses satisfy `rangeWatchRespOk`
from position `rev - 1`, and which may be closed at any time. -/
def isEtcdRangeWatcher (w : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)) (rev : w64),
    {{ context.isContext ctx cs ∗ optsAt sl gs ∗
        ⌜(opWatchModel key gs).isRangeWatch rev = true ∧ ¬ opWatchPanics key gs ∧
          0 ≤ sint.Z rev ∧
          KeyRangeUnder pfx (opWatchModel key gs).key (opWatchModel key gs).base.rangeEnd⌝ }}
      (App (App (App (Val #(methods w.ty go!"Watch" w.v)) (Val #(GoInterface.ok ctx)))
        (Val #key)) (Val #sl))
    {{ (ch : Loc) (γ : EtcdWatchNames), RET #ch;
        isSpsc γ.spsc ch (rangeWatchElem γ pfx (opWatchModel key gs) rev) (fun _ => iprop(True)) ∗
          spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
          monoListIdxOwn γ.cur 0 (rev - W64 1) }})

instance isEtcdRangeWatcher_persistent (w : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdRangeWatcher (GF := GF) w pfx) := by
  unfold isEtcdRangeWatcher; infer_instance

/-- **The client's range watch, under the premise that its channel is never closed**
(`client/v3/experimental/recipes`' bundle): `isEtcdRangeWatcher` with the SPSC channel's close
predicate `False`, so that a receive always yields a response (`spsc_rcv_au`: a close would give
`False`). A premise, not a fact: etcd's client closes a watch channel when the client is closed
or when etcd cancels the watch (a compaction past the watched revision), and the recipes as
shipped are wrong then (`notes/issues/recipes-dequeue-closed-watch.md`,
`recipes-barrier-wait-closed-watch.md`: on a close `waitEvents` returns `nil`, so
`WaitEvents`/`WaitPrefixEvents` return `(nil, nil)`, `Queue.Dequeue` dereferences it and
panics, `Barrier.Wait` reports a release while the barrier is held). Every recipes result is
under this premise (no compaction past a watched revision, the client not closed while a recipe
waits), which the fixed code (returning the canceled response's error) would not need. -/
def isEtcdRangeWatcherOpen (w : GoInterfaceOk) (pfx : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (key : GoString)
      (sl : GoSlice) (gs : List (OpFull → OpFull)) (rev : w64),
    {{ context.isContext ctx cs ∗ optsAt sl gs ∗
        ⌜(opWatchModel key gs).isRangeWatch rev = true ∧ ¬ opWatchPanics key gs ∧
          0 ≤ sint.Z rev ∧
          KeyRangeUnder pfx (opWatchModel key gs).key (opWatchModel key gs).base.rangeEnd⌝ }}
      (App (App (App (Val #(methods w.ty go!"Watch" w.v)) (Val #(GoInterface.ok ctx)))
        (Val #key)) (Val #sl))
    {{ (ch : Loc) (γ : EtcdWatchNames), RET #ch;
        isSpsc γ.spsc ch (rangeWatchElem γ pfx (opWatchModel key gs) rev) (fun _ => iprop(False)) ∗
          spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
          monoListIdxOwn γ.cur 0 (rev - W64 1) }})

instance isEtcdRangeWatcherOpen_persistent (w : GoInterfaceOk) (pfx : GoString) :
    Persistent (isEtcdRangeWatcherOpen (GF := GF) w pfx) := by
  unfold isEtcdRangeWatcherOpen; infer_instance

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
          (⌜err = GoInterface.nil⌝ ∗ ∃ γ : ChanNames, isChanAny γ ch) }}) ∗
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
