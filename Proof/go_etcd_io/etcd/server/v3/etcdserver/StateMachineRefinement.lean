/-
**The server's model of its store agrees with the state machine** (2026-10-19; `notes/decisions.md`,
"The KV specs over a state machine (D22)"). Pure. Lean-first (no Rocq counterpart).

The server's proofs model its store by mvcc's log (`mvcc.Log`, `KVModelDefs.lean`: the state of
a log, `kvStateOf`, and an operation's step, `kvOpStep`, written in terms of mvcc's and the txn
package's functions: `putKv`, `applyChanges`, `delChanges`, `srvRangeOk`, ...). The top-level
specs are stated over the state machine (`StateMachine.lean`), which is written to be read by
etcd's experts and uses none of them. This file proves that the two agree:

* **Requests** (`putReqOf`, `deleteRangeReqOf`): the state machine's request of a request the
  server decodes (an `OpFull`).
* **The maps** (`KVMap.store_eq`, `KVMap.put_eq`, `KVMap.deleteRange_eq`): the state machine's
  map operations are mvcc's (`btInsert`, `putKv`, a delete's changes applied).
* **The steps** (`putNext_eq`, `deleteRangeNext_eq`): the state machine's state after a request
  is `kvOpStep`'s, at every state (so an atomic update stated with one is the other).
* **The responses** (`put_ok`, `deleteRange_resp`): the state machine's response at the state
  of a log is the one the server's outcome predicates (`apply.putOutcomeIs`, ...) give.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open mvcc

/-! ## Requests -/

/-- **The put request** the server's decoded put `o` is. -/
def putReqOf (o : OpFull) : EtcdSM.PutRequest :=
  { key := o.key, value := o.val, lease := o.leaseID, prevKv := o.base.prevKV,
    ignoreValue := o.ignoreValue, ignoreLease := o.ignoreLease }

/-- **The delete request** the server's decoded delete `o` is. -/
def deleteRangeReqOf (o : OpFull) : EtcdSM.DeleteRangeRequest :=
  { key := o.key, rangeEnd := o.base.rangeEnd, prevKv := o.base.prevKV }

/-- The put the fields of a `*pb.PutRequest` denote (`txn.putOpOf`) is that request. -/
@[simp] theorem putReqOf_putOpOf (k v : GoString) (l : w64) (pk iv il : Bool) :
    putReqOf (txn.putOpOf k v l pk iv il) =
      { key := k, value := v, lease := l, prevKv := pk, ignoreValue := iv, ignoreLease := il } :=
  rfl

/-- The delete the fields of a `*pb.DeleteRangeRequest` denote (`txn.deleteOpOf`) is that
request. -/
@[simp] theorem deleteRangeReqOf_deleteOpOf (k re : GoString) (pk : Bool) :
    deleteRangeReqOf (txn.deleteOpOf k re pk) = { key := k, rangeEnd := re, prevKv := pk } :=
  rfl

/-! ## The maps -/

theorem EtcdSM.KVMap.get_eq (m : EtcdSM.KVMap) (k : GoString) : m.get k = findKey k m := rfl

theorem EtcdSM.KVMap.store_eq (v : EtcdKv) (m : EtcdSM.KVMap) :
    EtcdSM.KVMap.store v m = btInsert etcdKvLess v m := by
  induction m with
  | nil => rfl
  | cons w ws ih => simp only [EtcdSM.KVMap.store, btInsert, etcdKvLess, ih]

theorem EtcdSM.KVMap.put_eq (r : w64) (k v : GoString) (l : w64) (m : EtcdSM.KVMap) :
    EtcdSM.KVMap.put r k v l m = putKv r k v l m := by
  unfold EtcdSM.KVMap.put putKv
  rw [EtcdSM.KVMap.store_eq]
  rfl

theorem EtcdSM.KVMap.range_eq (m : EtcdSM.KVMap) (o : OpFull) :
    m.range o.key o.base.rangeEnd = rangeIn m o := rfl

theorem EtcdSM.KVMap.deleteRange_eq (r : w64) (m : EtcdSM.KVMap) (o : OpFull) :
    m.deleteRange o.key o.base.rangeEnd = applyChanges r m (txn.delChanges m o) :=
  (txn.applyChanges_delChanges r m o).symm

/-! ## The steps -/

/-- **A put's state is `kvOpStep`'s.** -/
theorem putNext_eq (o : OpFull) : EtcdSM.putNext (putReqOf o) = kvOpStep (.put o) := by
  funext σ
  unfold EtcdSM.putNext EtcdSM.put kvOpStep
  simp only [putReqOf, EtcdSM.KVMap.get_eq]
  by_cases h : (txn.needsPrev o && (findKey o.key σ.kvs).isNone) = true
  · have h' : ((o.ignoreValue || o.ignoreLease) && (findKey o.key σ.kvs).isNone) = true := h
    simp only [h', h, ↓reduceIte]
  · have h' : ¬ ((o.ignoreValue || o.ignoreLease) && (findKey o.key σ.kvs).isNone) = true := h
    simp only [h', h, Bool.false_eq_true, ↓reduceIte, KVState.commit, reduceCtorEq]
    congr 1
    rw [EtcdSM.KVMap.put_eq]
    simp only [applyChanges, applyChange, txn.putChangeOf, txn.putValOf, txn.putLeaseOf,
      List.foldl_cons, List.foldl_nil]
    congr

/-- **A delete's state is `kvOpStep`'s.** -/
theorem deleteRangeNext_eq (o : OpFull) :
    EtcdSM.deleteRangeNext (deleteRangeReqOf o) = kvOpStep (.deleteRange o) := by
  funext σ
  unfold EtcdSM.deleteRangeNext EtcdSM.deleteRange kvOpStep KVState.commit
  simp only [deleteRangeReqOf, EtcdSM.KVMap.range_eq]
  by_cases h : rangeIn σ.kvs o = []
  · have hd : txn.delChanges σ.kvs o = [] := by simp [txn.delChanges, h]
    simp only [h, hd, ↓reduceIte]
  · have hd : txn.delChanges σ.kvs o ≠ [] := by simpa [txn.delChanges] using h
    simp only [h, hd, ↓reduceIte]
    rw [EtcdSM.KVMap.deleteRange_eq (W64 ((σ.rev + 1 : Nat) : Int))]

/-! ## The responses -/

/-- **A put that passes its key check** (the key exists if the put keeps its value or lease)
succeeds, at `kvOpStep`'s state, with the next revision and the key's key-value before it if
asked. -/
theorem put_ok (o : OpFull) (σ : KVState)
    (h : txn.needsPrev o = true → (findKey o.key σ.kvs).isSome) :
    EtcdSM.put (putReqOf o) σ =
      .ok (kvOpStep (.put o) σ,
        { revision := σ.rev + 1, prevKv := if o.base.prevKV then findKey o.key σ.kvs else none }) := by
  have hn : ¬ ((o.ignoreValue || o.ignoreLease) && (findKey o.key σ.kvs).isNone) = true := by
    intro hc
    simp only [Bool.and_eq_true] at hc
    have := h hc.1
    simp_all
  have hstep := congrFun (putNext_eq o) σ
  unfold EtcdSM.putNext at hstep
  unfold EtcdSM.put at hstep ⊢
  simp only [putReqOf, EtcdSM.KVMap.get_eq] at hstep ⊢
  simp only [hn, Bool.false_eq_true, ↓reduceIte] at hstep ⊢
  rw [← hstep]
  congr

/-- **A delete's response**: at `kvOpStep`'s state, the revision after (`writeRev`'s: the next
one if it deleted something), the number of keys of its range, and those keys if asked. -/
theorem deleteRange_resp (o : OpFull) (σ : KVState) (hne : σ.revs ≠ []) :
    EtcdSM.deleteRange (deleteRangeReqOf o) σ =
      (kvOpStep (.deleteRange o) σ,
        { revision := if txn.delChanges σ.kvs o = [] then σ.rev else σ.rev + 1,
          deleted := (rangeIn σ.kvs o).length,
          prevKvs := if o.base.prevKV then rangeIn σ.kvs o else [] }) := by
  have hstep := congrFun (deleteRangeNext_eq o) σ
  unfold EtcdSM.deleteRangeNext at hstep
  rw [← hstep]
  unfold EtcdSM.deleteRange
  simp only [deleteRangeReqOf, EtcdSM.KVMap.range_eq]
  congr 2
  by_cases h : rangeIn σ.kvs o = []
  · have hd : txn.delChanges σ.kvs o = [] := by simp [txn.delChanges, h]
    simp only [h, hd, ↓reduceIte]
  · have hd : txn.delChanges σ.kvs o ≠ [] := by simpa [txn.delChanges] using h
    simp only [h, hd, ↓reduceIte]
    exact EtcdSM.State.rev_newRevision σ _ hne

/-! ## Range -/

/-- **The range request** the server's decoded range `o` is. -/
def rangeReqOf (o : OpFull) : EtcdSM.RangeRequest :=
  { key := o.key, rangeEnd := o.base.rangeEnd, limit := o.base.limit, revision := o.base.rev,
    sortOrder := o.sortOrder, sortTarget := o.sortTarget, serializable := o.base.serializable,
    keysOnly := o.keysOnly, countOnly := o.base.countOnly, minModRevision := o.base.minModRev,
    maxModRevision := o.base.maxModRev, minCreateRevision := o.base.minCreateRev,
    maxCreateRevision := o.base.maxCreateRev }

/-- A range's sort is set exactly when its order or target is not zero (what `txn.rangeOpOf`
records of a `*pb.RangeRequest`'s enumerations). -/
def SortSetOk (o : OpFull) : Prop :=
  o.base.sortSet = decide (o.sortOrder ≠ W64 0 ∨ o.sortTarget ≠ W64 0)

theorem rangeOpOf_sortSetOk (key re : GoString) (rev limit : w64) (order target : w32)
    (ser ko co : Bool) (minM maxM minC maxC : w64) :
    SortSetOk (txn.rangeOpOf key re rev limit order target ser ko co minM maxM minC maxC) := by
  unfold SortSetOk txn.rangeOpOf
  have h1 := txn.sext32_eq order 0 (by omega) (by omega)
  have h2 := txn.sext32_eq target 0 (by omega) (by omega)
  by_cases ho : order = W32 0 <;> by_cases ht : target = W32 0 <;> simp_all

theorem effectiveSortOrder_eq (o : OpFull) (h : SortSetOk o) :
    EtcdSM.effectiveSortOrder (rangeReqOf o) = o.effSortOrder := by
  unfold SortSetOk at h
  unfold EtcdSM.effectiveSortOrder OpFull.effSortOrder rangeReqOf
  dsimp only
  rw [h]
  unfold EtcdSM.targetKey EtcdSM.sortNone EtcdSM.sortAscend
  by_cases ho : o.sortOrder = W64 0 <;> by_cases ht : o.sortTarget = W64 0 <;>
    by_cases h1 : o.sortOrder = W64 1 <;> simp only [ho, ht, h1, ne_eq, not_true, not_false_eq_true,
      and_true, true_and, and_false, false_and, or_false, false_or, or_true, true_or,
      decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> simp_all

theorem readLimit_eq (o : OpFull) : EtcdSM.readLimit (rangeReqOf o) = txn.rangeLimitOf o := rfl

theorem takeUpTo_eq {α : Type} (n : w64) (l : List α) :
    EtcdSM.takeUpTo n l = takeLimit (limitOf n) l := by
  unfold EtcdSM.takeUpTo limitOf
  split <;> rfl

theorem candidates_eq (o : OpFull) (m : EtcdSM.KVMap) :
    EtcdSM.candidates (rangeReqOf o) m = txn.srvPre o m := by
  unfold EtcdSM.candidates txn.srvPre
  rw [takeUpTo_eq, readLimit_eq]
  have h1 : EtcdSM.revFiltersOk (rangeReqOf o) = kvFilterOk o := by funext v; rfl
  have h2 : EtcdSM.readKv (rangeReqOf o) = txn.kvRead (txn.fastKeysOnly o) := by funext v; rfl
  rw [h1, h2]
  rfl

/-- **The state machine's key-values and `more` of a range are the server's** (`srvRangeOk`). -/
theorem rangeKvsOk_iff (o : OpFull) (h : SortSetOk o) (m : EtcdSM.KVMap) (kvs : List EtcdKv)
    (more : Bool) :
    EtcdSM.RangeKvsOk (rangeReqOf o) m kvs more ↔ txn.srvRangeOk o m kvs more := by
  unfold EtcdSM.RangeKvsOk txn.srvRangeOk txn.srvSorted txn.srvTrunc txn.srvMore txn.respKv
  rw [effectiveSortOrder_eq o h, candidates_eq]
  simp only [EtcdSM.sortAscend, EtcdSM.sortDescend, rangeReqOf]
  have hle : EtcdSM.sortsBefore o.sortTarget = kvLeBy o.sortTarget := rfl
  rw [hle]
  constructor
  · rintro ⟨l, hp, ha, hd, he, hmore, hkvs⟩
    refine ⟨l, ⟨hp, ha, hd, he⟩, hmore, ?_⟩
    rw [hkvs, hmore]
    congr
  · rintro ⟨l, ⟨hp, ha, hd, he⟩, hmore, hkvs⟩
    refine ⟨l, hp, ha, hd, he, hmore, ?_⟩
    rw [hkvs, hmore]
    congr

/-- **The range's count is the server's** (`srvCount` with the total counted). -/
theorem range_count_eq (o : OpFull) (m : EtcdSM.KVMap) :
    txn.srvCount o m true = W64 ((m.range (rangeReqOf o).key (rangeReqOf o).rangeEnd).length : Int) := by
  unfold txn.srvCount
  have ht : ∀ (lim : Option Nat) (n : Nat), totalOf lim true n = n := by
    intro lim n; cases lim <;> rfl
  rw [ht]
  split <;> rfl

/-! ## Txn -/

theorem or_not_iff_not_and {p q : Prop} [Decidable p] : (¬p ∨ ¬q) ↔ ¬(p ∧ q) := by
  constructor
  · rintro (h | h) ⟨hp, hq⟩
    · exact h hp
    · exact h hq
  · intro h
    by_cases hp : p
    · exact Or.inr (fun hq => h ⟨hp, hq⟩)
    · exact Or.inl hp

/-- A comparison's operator as the state machine's result. -/
def cmpResultOf : CmpOp → EtcdSM.CompareResult
  | .eq => .equal
  | .gt => .greater
  | .lt => .less
  | .neq => .notEqual

/-- A comparison's target as the state machine's. -/
def cmpTargetOf : CmpTarget → EtcdSM.CompareTarget
  | .version => .version
  | .create => .create
  | .mod => .mod
  | .value => .value
  | .lease => .lease

/-- **The comparison** the server's decoded comparison `c` is. -/
def compareOf (c : CmpModel) : EtcdSM.Compare :=
  { result := cmpResultOf c.op, target := cmpTargetOf c.target, key := c.key,
    rangeEnd := c.rangeEnd, number := c.num, value := c.val }

theorem int_beq_eq (x y : Int) : (x == y) = decide (x = y) := by
  by_cases h : x = y <;> simp [h]

theorem int_bne_eq (x y : Int) : (x != y) = decide (x ≠ y) := by
  by_cases h : x = y <;> simp [h]

theorem holdsOn_eq (c : CmpModel) (v : EtcdKv) : (compareOf c).holdsOn v = cmpKv c v := by
  obtain ⟨key, re, tg, op, num, val⟩ := c
  cases tg <;> cases op <;>
    simp only [EtcdSM.Compare.holdsOn, compareOf, cmpTargetOf, cmpResultOf, cmpKv, CmpOp.holds,
      int64Cmp, bytesCmp, cmpSign, EtcdSM.compareInt64, EtcdSM.compareBytes, int_beq_eq,
      int_bne_eq, decide_eq_true_eq] <;> congr

theorem holds_eq (c : CmpModel) (m : EtcdSM.KVMap) : (compareOf c).holds m = cmpHolds m c := by
  unfold EtcdSM.Compare.holds cmpHolds EtcdSM.KVMap.range
  have h1 : EtcdSM.absentKv c.key = zeroKv c.key := rfl
  have h2 : (compareOf c).holdsOn = cmpKv c := funext (holdsOn_eq c)
  have h3 : decide ((compareOf c).target ≠ .value) = (c.target != .value) := by
    obtain ⟨key, re, tg, op, num, val⟩ := c
    cases tg <;> rfl
  simp only [h2, h3]
  rfl

theorem all_holds_eq (cs : List CmpModel) (m : EtcdSM.KVMap) :
    (cs.map compareOf).all (·.holds m) = cs.all (cmpHolds m) := by
  rw [List.all_map]
  congr 1
  funext c
  exact holds_eq c m

/-- A put of a transaction (no `prev_kv`, which the server's model does not keep). -/
def txnPutReq (k v : GoString) (l : w64) (iv il : Bool) : EtcdSM.PutRequest :=
  { key := k, value := v, lease := l, prevKv := false, ignoreValue := iv, ignoreLease := il }

mutual
/-- **The operation** the server's transaction operation `op` is (a put's `prev_kv` flag, which
the server's model does not keep, false). -/
def requestOpOf : TxnOp → EtcdSM.RequestOp
  | .get o => .range (rangeReqOf o)
  | .put k v l => .put (txnPutReq k v l false false)
  | .putKeep k v => .put (txnPutReq k v (W64 0) false true)
  | .putIgnVal k l => .put (txnPutReq k [] (l.getD (W64 0)) true l.isNone)
  | .delete o => .deleteRange (deleteRangeReqOf o)
  | .txn cs ts es => .txn (cs.map compareOf) (requestOpsOf ts) (requestOpsOf es)

/-- The operations. -/
def requestOpsOf : List TxnOp → List EtcdSM.RequestOp
  | [] => []
  | op :: ops => requestOpOf op :: requestOpsOf ops
end

/-- **The transaction request** the server's decoded transaction `t` is. -/
def txnReqOf (t : TxnModel) : EtcdSM.TxnRequest :=
  { compare := t.cmps.map compareOf, success := requestOpsOf t.thenOps,
    failure := requestOpsOf t.elseOps }

mutual
/-- **The server's model of an operation's result** (`TxnOpResult`) of the state machine's: a
range's selection (filtered, in key order) and count, a put, a delete's count, a nested
transaction's verdict and results. -/
def resultOf : EtcdSM.OpResult → TxnOpResult
  | .range req m => .range ((m.range req.key req.rangeEnd).filter (EtcdSM.revFiltersOk req))
      (m.range req.key req.rangeEnd).length
  | .put _ => .put
  | .deleteRange n _ => .delete n
  | .txn ok rs => .txn ok (resultsOf rs)

/-- The results. -/
def resultsOf : List EtcdSM.OpResult → List TxnOpResult
  | [] => []
  | r :: rs => resultOf r :: resultsOf rs
end

mutual
/-- **The key check is the server's** (`PathIgnOk`). -/
theorem opKeysOk_iff (s0 : List EtcdKv) :
    ∀ op : TxnOp, EtcdSM.opKeysOk s0 (requestOpOf op) = true ↔ txn.PathIgnOk s0 op
  | .get o => by simp [requestOpOf, txnPutReq, EtcdSM.opKeysOk, txn.PathIgnOk]
  | .put k v l => by simp [requestOpOf, txnPutReq, EtcdSM.opKeysOk, txn.PathIgnOk]
  | .putKeep k v => by simp [requestOpOf, txnPutReq, EtcdSM.opKeysOk, txn.PathIgnOk, EtcdSM.KVMap.get_eq]
  | .putIgnVal k l => by simp [requestOpOf, txnPutReq, EtcdSM.opKeysOk, txn.PathIgnOk, EtcdSM.KVMap.get_eq]
  | .delete o => by simp [requestOpOf, txnPutReq, EtcdSM.opKeysOk, txn.PathIgnOk]
  | .txn cs ts es => by
    simp only [requestOpOf, txnPutReq, EtcdSM.opKeysOk, txn.PathIgnOk, all_holds_eq]
    cases cs.all (cmpHolds s0)
    · exact opsKeysOk_iff s0 es
    · exact opsKeysOk_iff s0 ts

theorem opsKeysOk_iff (s0 : List EtcdKv) :
    ∀ ops : List TxnOp, EtcdSM.opsKeysOk s0 (requestOpsOf ops) = true ↔ txn.PathsIgnOk s0 ops
  | [] => by simp [requestOpsOf, EtcdSM.opsKeysOk, txn.PathsIgnOk]
  | op :: ops => by
    simp only [requestOpsOf, EtcdSM.opsKeysOk, txn.PathsIgnOk, Bool.and_eq_true,
      opKeysOk_iff s0 op, opsKeysOk_iff s0 ops]
end

mutual
/-- **An operation's run is the server's** (`srvOp`): the map after it is its changes applied,
it wrote exactly when it has changes, and its result is the server's. -/
theorem runOp_eq (s0 : List EtcdKv) (r : w64) :
    ∀ (m : List EtcdKv) (op : TxnOp),
      (EtcdSM.runOp s0 r m (requestOpOf op)).1 = applyChanges r m (txn.srvOp s0 r m op).1 ∧
      ((EtcdSM.runOp s0 r m (requestOpOf op)).2.1 = true ↔ (txn.srvOp s0 r m op).1 ≠ []) ∧
      resultOf (EtcdSM.runOp s0 r m (requestOpOf op)).2.2 = (txn.srvOp s0 r m op).2
  | m, .get o => by
    refine ⟨rfl, ?_, rfl⟩
    simp [requestOpOf, EtcdSM.runOp, txn.srvOp]
  | m, .put k v l => by
    simp [requestOpOf, txnPutReq, EtcdSM.runOp, txn.srvOp, resultOf, applyChanges, applyChange,
      EtcdSM.KVMap.put_eq]
  | m, .putKeep k v => by
    simp [requestOpOf, txnPutReq, EtcdSM.runOp, txn.srvOp, resultOf, applyChanges, applyChange,
      EtcdSM.KVMap.put_eq, EtcdSM.KVMap.get_eq]
  | m, .putIgnVal k l => by
    cases l <;>
      simp [requestOpOf, txnPutReq, EtcdSM.runOp, txn.srvOp, resultOf, applyChanges, applyChange,
        EtcdSM.KVMap.put_eq, EtcdSM.KVMap.get_eq]
  | m, .delete o => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [requestOpOf, EtcdSM.runOp, txn.srvOp, deleteRangeReqOf]
      exact EtcdSM.KVMap.deleteRange_eq r m o
    · simp only [requestOpOf, EtcdSM.runOp, txn.srvOp, deleteRangeReqOf, EtcdSM.KVMap.range_eq,
        txn.delChanges, ne_eq, List.map_eq_nil_iff]
      exact decide_eq_true_iff
    · simp [requestOpOf, EtcdSM.runOp, txn.srvOp, resultOf, deleteRangeReqOf,
        EtcdSM.KVMap.range_eq]
  | m, .txn cs ts es => by
    simp only [requestOpOf, EtcdSM.runOp, txn.srvOp, all_holds_eq]
    cases cs.all (cmpHolds s0)
    · have := runOps_eq s0 r m es
      exact ⟨this.1, this.2.1, by simp only [resultOf]; rw [this.2.2]⟩
    · have := runOps_eq s0 r m ts
      exact ⟨this.1, this.2.1, by simp only [resultOf]; rw [this.2.2]⟩

/-- **The operations' run is the server's** (`srvOps`). -/
theorem runOps_eq (s0 : List EtcdKv) (r : w64) :
    ∀ (m : List EtcdKv) (ops : List TxnOp),
      (EtcdSM.runOps s0 r m (requestOpsOf ops)).1 = applyChanges r m (txn.srvOps s0 r m ops).1 ∧
      ((EtcdSM.runOps s0 r m (requestOpsOf ops)).2.1 = true ↔ (txn.srvOps s0 r m ops).1 ≠ []) ∧
      resultsOf (EtcdSM.runOps s0 r m (requestOpsOf ops)).2.2 = (txn.srvOps s0 r m ops).2
  | m, [] => by simp [requestOpsOf, EtcdSM.runOps, txn.srvOps, resultsOf, applyChanges]
  | m, op :: ops => by
    have e1 := runOp_eq s0 r m op
    have e2 := runOps_eq s0 r (applyChanges r m (txn.srvOp s0 r m op).1) ops
    simp only [requestOpsOf, EtcdSM.runOps, txn.srvOps_cons, resultsOf]
    rw [e1.1]
    refine ⟨?_, ?_, ?_⟩
    · rw [e2.1, txn.applyChanges_append]
    · rw [Bool.or_eq_true, e1.2.1, e2.2.1, ne_eq, ne_eq, ne_eq, List.append_eq_nil_iff]
      exact or_not_iff_not_and
    · rw [e1.2.2, e2.2.2]
end

/-- **A transaction's state is `kvOpStep`'s.** -/
theorem txnNext_eq (t : TxnModel) : EtcdSM.txnNext (txnReqOf t) = kvOpStep (.txn t) := by
  funext σ
  unfold EtcdSM.txnNext EtcdSM.txn kvOpStep KVState.commit txn.srvRunTxn
  simp only [txnReqOf, all_holds_eq]
  have hb : (if txn.txnOk σ.kvs t = true then requestOpsOf t.thenOps else requestOpsOf t.elseOps) =
      requestOpsOf (t.branch (txn.txnOk σ.kvs t)) := by
    unfold TxnModel.branch; split <;> rfl
  rw [hb]
  have hk := opsKeysOk_iff σ.kvs (t.branch (txn.txnOk σ.kvs t))
  have hr := runOps_eq σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (t.branch (txn.txnOk σ.kvs t))
  by_cases hp : txn.PathsIgnOk σ.kvs (t.branch (txn.txnOk σ.kvs t))
  · have hk' := hk.2 hp
    simp only [hk', Bool.true_eq_false, ↓reduceIte, hp]
    by_cases hc : (txn.srvOps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
        (t.branch (txn.txnOk σ.kvs t))).1 = []
    · have hw : (EtcdSM.runOps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (requestOpsOf (t.branch (txn.txnOk σ.kvs t)))).2.1 = false := by
        cases h : (EtcdSM.runOps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (requestOpsOf (t.branch (txn.txnOk σ.kvs t)))).2.1
        · rfl
        · exact absurd (hr.2.1.1 h) (by simpa using hc)
      simp only [hw, Bool.false_eq_true, ↓reduceIte, hc]
    · have hw : (EtcdSM.runOps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (requestOpsOf (t.branch (txn.txnOk σ.kvs t)))).2.1 = true := hr.2.1.2 hc
      simp only [hw, ↓reduceIte, hc]
      rw [hr.1]
  · have hk' : EtcdSM.opsKeysOk σ.kvs (requestOpsOf (t.branch (txn.txnOk σ.kvs t))) = false := by
      cases h : EtcdSM.opsKeysOk σ.kvs (requestOpsOf (t.branch (txn.txnOk σ.kvs t)))
      · rfl
      · exact absurd (hk.1 h) hp
    simp only [hk', ↓reduceIte, hp]

/-- **A transaction that passes its key check** succeeds, at `kvOpStep`'s state, with the
revision after (the next one if it wrote), the server's verdict, and results whose server model
is the server's run's. -/
theorem txn_ok (t : TxnModel) (σ : KVState) (hne : σ.revs ≠ [])
    (hp : txn.PathsIgnOk σ.kvs (t.branch (txn.txnOk σ.kvs t))) :
    ∃ res : EtcdSM.TxnResult,
      EtcdSM.txn (txnReqOf t) σ = .ok (kvOpStep (.txn t) σ, res) ∧
      res.revision = (if (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1 = []
        then σ.rev else σ.rev + 1) ∧
      res.succeeded = txn.txnOk σ.kvs t ∧
      resultsOf res.results = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.2 := by
  have hb : (if txn.txnOk σ.kvs t = true then requestOpsOf t.thenOps else requestOpsOf t.elseOps) =
      requestOpsOf (t.branch (txn.txnOk σ.kvs t)) := by
    unfold TxnModel.branch; split <;> rfl
  have hk' := (opsKeysOk_iff σ.kvs (t.branch (txn.txnOk σ.kvs t))).2 hp
  have hr := runOps_eq σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (t.branch (txn.txnOk σ.kvs t))
  generalize hrun : EtcdSM.runOps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
    (requestOpsOf (t.branch (txn.txnOk σ.kvs t))) = run at hr
  have htxn : EtcdSM.txn (txnReqOf t) σ =
      .ok ((if run.2.1 then σ.newRevision run.1 else σ),
        { revision := (if run.2.1 then σ.newRevision run.1 else σ).rev,
          succeeded := txn.txnOk σ.kvs t, results := run.2.2 }) := by
    unfold EtcdSM.txn
    simp only [txnReqOf, all_holds_eq, hb, hk', Bool.true_eq_false, ↓reduceIte, hrun]
  have hnext : EtcdSM.txnNext (txnReqOf t) σ = (if run.2.1 then σ.newRevision run.1 else σ) := by
    unfold EtcdSM.txnNext; rw [htxn]
  refine ⟨⟨(if run.2.1 then σ.newRevision run.1 else σ).rev, txn.txnOk σ.kvs t, run.2.2⟩,
    ?_, ?_, rfl, ?_⟩
  · rw [htxn, ← hnext, txnNext_eq]
  · unfold txn.srvRunTxn
    dsimp only
    by_cases hw : run.2.1 = true
    · have hc := hr.2.1.1 hw
      simp only [hw, ↓reduceIte, hc]
      exact EtcdSM.State.rev_newRevision σ _ hne
    · have hc : (txn.srvOps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
          (t.branch (txn.txnOk σ.kvs t))).1 = [] :=
        Classical.byContradiction fun h => hw (hr.2.1.2 h)
      simp only [hw, Bool.false_eq_true, ↓reduceIte, hc]
  · unfold txn.srvRunTxn; exact hr.2.2

/-! ## The state of a log -/

theorem kvStateOf_revs_ne_nil (l : Log) (h : l ≠ []) : (kvStateOf l).revs ≠ [] := by
  unfold kvStateOf
  simpa using h

theorem kvStateOf_rev_succ (l : Log) (h : l ≠ []) : (kvStateOf l).rev + 1 = l.length := by
  have := List.length_pos_iff.2 h
  rw [kvStateOf_rev]; omega

end EtcdGrove
end Perennial
