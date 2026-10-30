/-
**`Work`'s calls, one at a time** (`notes/authkv-main-plan.md`, "Proving the stubs", layer 4;
2026-10-30). Lean-first (no Rocq counterpart).

A request of `Work`'s is sent in `reqCtx(who)`'s context, whose outgoing metadata is `akOut who`
(`reqCtx_out`). A write sends the update `akWriteAu`: `akHist_writeAu` at the write's grant, which
`akOpGranted_of_grant` reads at `setupSt` (`Q`: the write was granted to `who`). So a write's
reply with no error was granted (`work_put`, `work_delete`): its point permission is `who`'s
(`akGranted_point`), and a refused write's reply is an error.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

section pure
variable [GooseExts]

/-- **`reqCtx(who)`'s context carries `akOut who`** (`reqCtx.spec`'s post). -/
theorem reqCtx_out (who : GoString) (c c0 : GoInterface) (h0 : metadata.outgoingOf c0 = none)
    (h : if who = go!"bad" then
      metadata.outgoingOf c = metadata.mdAdd (metadata.outgoingOf c0) go!"token" badToken
      else c = c0) :
    metadata.outgoingOf c = akOut who := by
  unfold akOut
  by_cases hb : who = go!"bad"
  · rw [if_pos hb] at h; rw [if_pos hb, h, h0]
  · rw [if_neg hb] at h; rw [if_neg hb, h, h0]

/-- A put's request needs the write permission on its key. -/
theorem put_perm_mem (o : OpFull) :
    ((o.key, [], .write) : apply.Perm3) ∈ reqPerms (irrPut o) := by
  simp [reqPerms, irrPut, apply.dispatchKind, apply.putPerms, apply.irrEmpty]

/-- A delete's request needs the write permission on its range. -/
theorem delete_perm_mem (o : OpFull) :
    ((o.key, o.base.rangeEnd, .write) : apply.Perm3) ∈ reqPerms (irrDeleteRange o) := by
  simp [reqPerms, irrDeleteRange, apply.dispatchKind, apply.irrEmpty]

/-- **A granted put of `who`'s on a non-empty key is `who`'s to make.** -/
theorem akOpGranted_put (who k v : GoString) (hk : k ≠ [])
    (h : akOpGranted who (.put (putKeyOp k v))) : permittedK who k :=
  akGranted_point who _ k .write h (put_perm_mem (putKeyOp k v)) hk

/-- **A granted point delete of `who`'s on a non-empty key is `who`'s to make.** -/
theorem akOpGranted_delete (who k : GoString) (hk : k ≠ [])
    (h : akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))) : permittedK who k :=
  akGranted_point who _ k .write h (delete_perm_mem (txn.deleteOpOf k [] false)) hk

/-- **A key `c/…` is no one's to write** (`c` sorts after `hi = "b"`). -/
theorem not_permitted_c (who n : GoString) : ¬ permittedK who (keyOfK go!"c" who n) := by
  intro ⟨_, _, hlt⟩
  rw [show keyOfK go!"c" who n = W8 99 :: (go!"/" ++ who ++ go!"/" ++ n) by
    simp [keyOfK], show hi = [W8 98] from rfl, go.goStringLt_cons_iff] at hlt
  rcases hlt with h | ⟨h, -⟩ <;> revert h <;> decide

/-- `Work`'s keys are not empty. -/
theorem keyOfK_ne_nil (x who n : GoString) (hx : x ≠ []) : keyOfK x who n ≠ [] := by
  unfold keyOfK; simp [hx]

/-- **A granted put of `who`'s on `a/who/n` keeps the history** (`opHistOk_putKey`): it is `u`'s
(`akOpGranted_put`), and `u` writes `a/u/n` (`hw`). -/
theorem opHistOk_put_a (who n v : GoString) (hw : writerK (keyOfK go!"a" go!"u" n) = go!"u")
    (h : akOpGranted who (.put (putKeyOp (keyOfK go!"a" who n) v))) :
    opHistOk (.put (putKeyOp (keyOfK go!"a" who n) v)) := by
  obtain ⟨rfl, hr⟩ := akOpGranted_put who _ v (keyOfK_ne_nil _ _ _ (by decide)) h
  exact opHistOk_putKey _ _ (Or.inl (by rw [hw]; exact ⟨rfl, hr⟩))

/-- **A range reply's keys are in its range** (`srvRangeOk`: the state's range, cut, sorted and
read). -/
theorem srvRangeOk_keys (o : OpFull) (st kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk o st kvs more) :
    ∀ kv ∈ kvs, inRange o.key o.base.rangeEnd kv.key = true := by
  obtain ⟨l, ⟨hperm, -⟩, -, rfl⟩ := h
  intro kv hkv
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hkv
  have hvl : v ∈ l := by
    unfold txn.srvTrunc at hv
    split at hv
    · exact List.mem_of_mem_take hv
    · exact hv
  have hvp := hperm.mem_iff.1 hvl
  unfold txn.srvPre at hvp
  split at hvp
  · simp at hvp
  obtain ⟨hvm, -⟩ := List.mem_filter.1 hvp
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hvm
  have hw' : w ∈ rangeIn st o := by
    unfold mvcc.takeLimit at hw
    split at hw
    · exact List.mem_of_mem_take hw
    · exact hw
  have hk := (List.mem_filter.1 hw').2
  unfold txn.respKv txn.kvRead
  split <;> split <;> simpa using hk

/-! ### A transaction's puts -/

theorem mem_opsPerms (op : txn.TxnOpW) :
    ∀ (ops : List txn.TxnOpW), op ∈ ops → ∀ x ∈ opPerms op, x ∈ opsPerms ops
  | [], h => absurd h List.not_mem_nil
  | o :: ops, h => by
    intro x hx
    simp only [opsPerms, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h'
    · exact Or.inl hx
    · exact Or.inr (mem_opsPerms op ops h' x hx)

/-- A put among a wire transaction's operations needs the write permission on its key. -/
theorem put_mem_opsPerms (k v l : GoString) (le : w64) (ops : List txn.TxnOpW)
    (h : TxnOp.put k v le ∈ txn.TxnOpW.toOps ops) :
    ((k, [], .write) : apply.Perm3) ∈ opsPerms ops := by
  rw [txn.TxnOpW.toOps_eq_map] at h
  obtain ⟨w, hw, he⟩ := List.mem_map.1 h
  cases w with
  | put o =>
    simp only [txn.TxnOpW.toOp, txn.putTxnOp] at he
    split at he
    · cases he
    split at he
    · cases he
    obtain ⟨rfl, -, -⟩ := TxnOp.put.inj he
    exact mem_opsPerms _ _ hw _ (by simp [opPerms, apply.putPerms])
  | get o => simp [txn.TxnOpW.toOp] at he
  | delete o => simp [txn.TxnOpW.toOp] at he
  | txn cs ts es => simp [txn.TxnOpW.toOp] at he

/-- **A granted transaction of `who`'s with a put of a non-empty key `k`** (in either branch) is
`who`'s to make. -/
theorem akOpGranted_txn_put (who k v : GoString) (le : w64) (t : TxnModel) (hk : k ≠ [])
    (hm : TxnOp.put k v le ∈ t.thenOps ++ t.elseOps) (h : akOpGranted who (.txn t)) :
    permittedK who k := by
  obtain ⟨tw, rfl, hg⟩ := h
  refine akGranted_point who _ k .write hg ?_ hk
  rcases List.mem_append.1 hm with hm | hm
  · have h1 := put_mem_opsPerms k v [] le _ hm
    simp [reqPerms, irrTxn, apply.dispatchKind, apply.irrEmpty, h1]
  · have h1 := put_mem_opsPerms k v [] le _ hm
    simp [reqPerms, irrTxn, apply.dispatchKind, apply.irrEmpty, h1]

/-- The shape of a wire operation's permissions, from its model's: a plain put's key not empty, a
get's range of the cache's shape. -/
def opShapeOk : TxnOp → Prop
  | .put k _ _ => k ≠ []
  | .get o => auth.reqShape o.key o.base.rangeEnd
  | _ => False

theorem opsPerms_shape (ops : List txn.TxnOpW)
    (h : ∀ op ∈ txn.TxnOpW.toOps ops, opShapeOk op) :
    ∀ x ∈ opsPerms ops, auth.reqShape x.1 x.2.1 := by
  induction ops with
  | nil => intro x hx; simp [opsPerms] at hx
  | cons w ops ih =>
    intro x hx
    simp only [opsPerms, List.mem_append] at hx
    have hw : opShapeOk w.toOp := h _ (by simp [txn.TxnOpW.toOps])
    rcases hx with hx | hx
    · cases w with
      | put o =>
        simp only [txn.TxnOpW.toOp, txn.putTxnOp] at hw
        split at hw
        · exact hw.elim
        split at hw
        · exact hw.elim
        simp only [opPerms, apply.putPerms] at hx
        split at hx <;> simp at hx <;> rcases hx with rfl | rfl <;>
          exact ⟨hw, Or.inl rfl⟩
      | get o =>
        simp only [opPerms, List.mem_singleton] at hx
        subst hx; exact hw
      | delete o => exact hw.elim
      | txn cs ts es => exact hw.elim
    · exact ih (fun op hop => h op (by simp [txn.TxnOpW.toOps, hop])) x hx

/-- **A transaction's permissions have the shape the cache decides** when its comparisons' and
operations' models do. -/
theorem kvShapeAll_irrTxn (tw : txn.TxnModelW)
    (hc : ∀ c ∈ tw.toModel.cmps, auth.reqShape c.key c.rangeEnd)
    (ho : ∀ op ∈ tw.toModel.thenOps ++ tw.toModel.elseOps, opShapeOk op) :
    kvShapeAll (irrTxn tw) := by
  intro x hx
  have hr : reqPerms (irrTxn tw) = tw.cmps.map (fun cm => ((cm.key, cm.rangeEnd, .read) :
      apply.Perm3)) ++ opsPerms tw.thenOps ++ opsPerms tw.elseOps := by
    simp [reqPerms, irrTxn, apply.dispatchKind, apply.irrEmpty]
  rw [hr, List.mem_append, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨c, hcm, rfl⟩ := List.mem_map.1 hx
    exact hc c hcm
  · exact opsPerms_shape _ (fun op hop => ho op (List.mem_append_left _ hop)) x hx
  · exact opsPerms_shape _ (fun op hop => ho op (List.mem_append_right _ hop)) x hx

/-! ### `Work`'s transactions T1–T3 -/

/-- `OpPut(k, v)`'s model operation. -/
theorem txnOpOf_put (k v : GoString) : txnOpOf (opPutModel k v []) = some (.put k v (W64 0)) := by
  simp [txnOpOf, opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]

theorem not_putPanics (k v : GoString) : ¬ (opPutModel k v []).putPanics := by
  simp [OpFull.putPanics, opPutModel, opFold, OpFull.putInit, OpFull.newOp, OpModel.zero]

/-- `OpGet(lo, WithRange(hi))`'s model operation. -/
theorem txnOpOf_get_ab :
    txnOpOf (opGetModel lo [withRangeM hi]) = some (.get (opGetModel lo [withRangeM hi])) := by
  simp [txnOpOf, opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero, withRangeM]

/-- What `work_commit` asks of a transaction's model. -/
def akTxnOk (m : TxnModel) : Prop :=
  TxnModel.plain (txnWireOf m) ∧ txnModelIn (txnWireOf m) ∧
  (∀ tw : txn.TxnModelW, tw.toModel = txnWireOf m → kvShapeAll (irrTxn tw)) ∧
  txn.txnReadonly (txnWireOf m) = false ∧
  (txn.txnPlain (txnWireOf m) ∧ txnNoZeroEnd (txnWireOf m))

/-- T1: `Then(OpPut(k1, v), OpGet(lo, WithRange(hi)))`. -/
def t1M (k v : GoString) : TxnModel :=
  { cmps := [], thenOps := [.put k v (W64 0), .get (opGetModel lo [withRangeM hi])], elseOps := [] }

/-- T2: `Then(OpPut(k1, v), OpPut(k2, v))`. -/
def t2M (k1 k2 v : GoString) : TxnModel :=
  { cmps := [], thenOps := [.put k1 v (W64 0), .put k2 v (W64 0)], elseOps := [] }

/-- T3: `If(c).Then(OpPut(k1, v)).Else(OpPut(k2, v))`. -/
def t3M (c : CmpModel) (k1 k2 v : GoString) : TxnModel :=
  { cmps := [c], thenOps := [.put k1 v (W64 0)], elseOps := [.put k2 v (W64 0)] }

theorem t1M_ok (k v : GoString) (hk : k ≠ []) : akTxnOk (t1M k v) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro op hop; simp [t1M, txnWireOf, opWire] at hop; rcases hop with rfl | rfl <;> trivial
  · intro op hop; simp [t1M, txnWireOf] at hop
  · intro o ho
    simp [t1M, txnWireOf, opWire] at ho
    subst ho
    simp [rangeWireOf, txn.rangeOpOf, opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero, withRangeM,
      txn.cutEarly, OpFull.effSortOrder, sortOrderWire, sortTargetWire]
  · intro tw htw
    refine kvShapeAll_irrTxn tw (by rw [htw]; simp [t1M, txnWireOf]) ?_
    rw [htw]
    intro op hop
    simp [t1M, txnWireOf, opWire] at hop
    rcases hop with rfl | rfl
    · exact hk
    · simp only [opShapeOk]
      exact ⟨by decide, Or.inr (Or.inr (by decide))⟩
  · simp [t1M, txnWireOf, opWire, txn.txnReadonly, txn.opIsGet]
  · simp [t1M, txnWireOf, opWire, txn.txnPlain, txn.opsPlain, txn.opPlain, rangeWireOf,
      txn.rangeOpOf, opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero, withRangeM]
  · refine ⟨by simp [t1M, txnWireOf], ?_, by simp [t1M, txnWireOf, txnOpsNoZeroEnd]⟩
    simp [t1M, txnWireOf, opWire, txnOpsNoZeroEnd, txnOpNoZeroEnd, rangeWireOf, txn.rangeOpOf,
      opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero, withRangeM]

theorem t2M_ok (k1 k2 v : GoString) (hk1 : k1 ≠ []) (hk2 : k2 ≠ []) : akTxnOk (t2M k1 k2 v) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro op hop; simp [t2M, txnWireOf, opWire] at hop; rcases hop with rfl | rfl <;> trivial
  · intro op hop; simp [t2M, txnWireOf] at hop
  · intro o ho; simp [t2M, txnWireOf, opWire] at ho
  · intro tw htw
    refine kvShapeAll_irrTxn tw (by rw [htw]; simp [t2M, txnWireOf]) ?_
    rw [htw]
    intro op hop
    simp [t2M, txnWireOf, opWire] at hop
    rcases hop with rfl | rfl
    · exact hk1
    · exact hk2
  · simp [t2M, txnWireOf, opWire, txn.txnReadonly, txn.opIsGet]
  · simp [t2M, txnWireOf, opWire, txn.txnPlain, txn.opsPlain, txn.opPlain]
  · simp [t2M, txnWireOf, opWire, txnNoZeroEnd, txnOpsNoZeroEnd, txnOpNoZeroEnd]

theorem t3M_ok (c : CmpModel) (k1 k2 v : GoString) (hc : auth.reqShape c.key c.rangeEnd)
    (hc0 : c.rangeEnd ≠ [W8 0]) (hk1 : k1 ≠ []) (hk2 : k2 ≠ []) : akTxnOk (t3M c k1 k2 v) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro op hop; simp [t3M, txnWireOf, opWire] at hop; subst hop; trivial
  · intro op hop; simp [t3M, txnWireOf, opWire] at hop; subst hop; trivial
  · intro o ho; simp [t3M, txnWireOf, opWire] at ho
  · intro tw htw
    refine kvShapeAll_irrTxn tw (by rw [htw]; simpa [t3M, txnWireOf] using hc) ?_
    rw [htw]
    intro op hop
    simp [t3M, txnWireOf, opWire] at hop
    rcases hop with rfl | rfl
    · exact hk1
    · exact hk2
  · simp [t3M, txnWireOf, opWire, txn.txnReadonly, txn.opIsGet]
  · simp [t3M, txnWireOf, opWire, txn.txnPlain, txn.opsPlain, txn.opPlain]
  · simpa [t3M, txnWireOf, opWire, txnNoZeroEnd, txnOpsNoZeroEnd, txnOpNoZeroEnd] using hc0

/-- No events after the state's revision. -/
theorem revEvents_after (σ : KVState) (r : Nat) (hr : σ.rev < r) : σ.revEvents r = [] := by
  unfold KVState.revEvents
  have hc : σ.changesAt r = [] := by
    unfold KVState.rev at hr
    unfold KVState.changesAt
    split
    · rfl
    · rw [List.getElem?_eq_none (by omega)]; rfl
  rw [hc, mvcc.evsOfRevM_nil]

/-- **`Work`'s transaction T1** (`Then(OpPut(k, v), OpGet(...))`) keeps the history when `k` is its
writer's to write: it commits the put's one change, or nothing. -/
theorem opHistOk_txn_put_get (k v : GoString) (og : OpFull) (h : permittedK (writerK k) k) :
    opHistOk (.txn (txnWireOf
      { cmps := [], thenOps := [.put k v (W64 0), .get og], elseOps := [] })) := by
  intro σ r hr ev hev
  simp only [kvOpStep] at hev
  split at hev
  · have hc : (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf
        { cmps := [], thenOps := [.put k v (W64 0), .get og], elseOps := [] })).2.1 =
        [.put k v (W64 0)] := by
      simp [txn.srvRunTxn, txnWireOf, opWire, TxnModel.branch, txn.srvOps_cons, txn.srvOps_nil,
        txn.srvOp]
    rw [hc, ← kvOpStep_putKeyOp] at hev
    exact opHistOk_putKey k v (Or.inl h) σ r hr ev hev
  · rw [revEvents_after σ r hr] at hev; cases hev

/-- An event of one revision is of one of its changes' keys. -/
theorem evsOfRevM_key (m : Nat) :
    ∀ (cs : List mvcc.Change) (b : List EtcdKv), b.Pairwise etcdKvLess →
      ∀ ev ∈ mvcc.evsOfRevM m b cs, ∃ c ∈ cs, ev.kv.key = c.key
  | [], _, _ => by intro ev hev; rw [mvcc.evsOfRevM_nil] at hev; cases hev
  | c :: cs, b, hb => by
    intro ev hev
    rw [v3rpc.evsOfRevM_cons m b hb c cs, List.mem_cons] at hev
    rcases hev with rfl | hev
    · refine ⟨c, List.mem_cons_self .., ?_⟩
      unfold mvcc.evOfKv; split <;> simp [v3rpc.chKv_key]
    · obtain ⟨c', hc', hk⟩ := evsOfRevM_key m cs _ (mvcc.applyChange_sorted hb _ c) ev hev
      exact ⟨c', List.mem_cons_of_mem _ hc', hk⟩

/-- **The events after a state, in its commit of `cs`, are of `cs`'s keys.** -/
theorem revEvents_commit_key (σ : KVState) (cs : List mvcc.Change) (r : Nat) (hr : σ.rev < r) :
    ∀ ev ∈ (σ.commit cs).revEvents r, ∃ c ∈ cs, ev.kv.key = c.key := by
  intro ev hev
  unfold KVState.revEvents at hev
  have hch : (σ.commit cs).changesAt r = [] ∨ (σ.commit cs).changesAt r = cs := by
    unfold KVState.rev at hr
    by_cases hcs : cs = []
    · left
      subst hcs
      rw [KVState.commit_nil]
      unfold KVState.changesAt
      split
      · rfl
      · rw [List.getElem?_eq_none (by omega)]; rfl
    · unfold KVState.changesAt KVState.commit
      rw [if_neg hcs]
      simp only
      split
      · left; rfl
      · by_cases he : r - σ.compacted - 1 = σ.changes.length
        · right; rw [he, List.getElem?_append_right (Nat.le_refl _)]; simp
        · left; rw [List.getElem?_eq_none (by simp; omega)]; rfl
  rcases hch with h | h
  · rw [h, mvcc.evsOfRevM_nil] at hev; cases hev
  · rw [h] at hev
    exact evsOfRevM_key r cs _ (KVStore.kvs_sorted _) ev hev

/-- **A point delete of a key its writer may write keeps the history.** -/
theorem opHistOk_delete_point (k : GoString) (h : permittedK (writerK k) k) :
    opHistOk (.deleteRange (txn.deleteOpOf k [] false)) := by
  intro σ r hr ev hev
  simp only [kvOpStep] at hev
  obtain ⟨c, hc, hk⟩ := revEvents_commit_key σ _ r hr ev hev
  unfold txn.delChanges at hc
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hc
  have hvk := (List.mem_filter.1 hv).2
  simp [inRange, txn.deleteOpOf] at hvk
  unfold evHistOk
  left
  rw [hk]
  simp only [mvcc.Change.key]
  rw [hvk]; exact h

/-! ### `Work`'s three ranges -/

/-- A key in `[a, b)` is `u`'s to read. -/
theorem permitted_of_inRange_ab (k : GoString) (h : inRange lo hi k = true) :
    permittedK go!"u" k := by
  unfold inRange at h
  rw [_root_.if_neg (by decide), _root_.if_neg (by decide)] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  refine ⟨rfl, ?_, h.2⟩
  by_cases hl : go.GoStringLt lo k
  · exact Or.inr hl
  · exact Or.inl (go.goStringLt_eq_of_not_lt hl h.1)

/-- `Get(lo, WithRange(hi))`: the range `[a, b)`, sent as is. -/
theorem get_ab_ok : (¬ opGetPanics [withRangeM hi] ∧ (opGetModel lo [withRangeM hi]).t = W64 1) ∧
    (opGetModel lo [withRangeM hi]).base.sortSet = false ∧
    (rangeWireOf (opGetModel lo [withRangeM hi])).key = lo ∧
    (rangeWireOf (opGetModel lo [withRangeM hi])).base.rangeEnd = hi :=
  ⟨⟨by simp [opGetPanics, opFold, withRangeM, OpFull.newOp, OpModel.zero], rfl⟩, rfl, rfl, rfl⟩

/-- `Get("c/", WithPrefix())`: the range `[c/, c0)`. -/
theorem get_c_ok : (¬ opGetPanics [withPrefixM] ∧ (opGetModel go!"c/" [withPrefixM]).t = W64 1) ∧
    (opGetModel go!"c/" [withPrefixM]).base.sortSet = false ∧
    (rangeWireOf (opGetModel go!"c/" [withPrefixM])).key = go!"c/" ∧
    (rangeWireOf (opGetModel go!"c/" [withPrefixM])).base.rangeEnd = go!"c0" :=
  ⟨⟨by simp [opGetPanics, opFold, withPrefixM, OpFull.newOp, OpModel.zero], rfl⟩, rfl, rfl, by decide⟩

/-- `Get(lo, WithRange("d"))`: the range `[a, d)`. -/
theorem get_past_ok :
    (¬ opGetPanics [withRangeM go!"d"] ∧ (opGetModel lo [withRangeM go!"d"]).t = W64 1) ∧
    (opGetModel lo [withRangeM go!"d"]).base.sortSet = false ∧
    (rangeWireOf (opGetModel lo [withRangeM go!"d"])).key = lo ∧
    (rangeWireOf (opGetModel lo [withRangeM go!"d"])).base.rangeEnd = go!"d" :=
  ⟨⟨by simp [opGetPanics, opFold, withRangeM, OpFull.newOp, OpModel.zero], rfl⟩, rfl, rfl, rfl⟩

/-- **A read of `[a, b)` granted at `setupSt` to a user of `who`'s is `u`'s.** -/
theorem read_ab_u (who : GoString)
    (h : ∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
      akUser who info.Username' ∧ apply.authEndOf hi e ∧
      auth.granted (setupSt r) (auth.authInfoM info) lo e .read) : who = go!"u" := by
  obtain ⟨r, info, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact granted_ab_u r who _ _ hu hg
  · exact absurd h0 (by decide)

/-- **No read of `[c/, c0)` is granted at `setupSt` to a user of `who`'s.** -/
theorem read_c_refused (who : GoString)
    (h : ∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
      akUser who info.Username' ∧ apply.authEndOf go!"c0" e ∧
      auth.granted (setupSt r) (auth.authInfoM info) go!"c/" e .read) : False := by
  obtain ⟨r, info, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact not_granted_c r who _ _ hu hg
  · exact absurd h0 (by decide)

/-- **No read of `[a, d)` is granted at `setupSt` to a user of `who`'s.** -/
theorem read_past_refused (who : GoString)
    (h : ∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
      akUser who info.Username' ∧ apply.authEndOf go!"d" e ∧
      auth.granted (setupSt r) (auth.authInfoM info) lo e .read) : False := by
  obtain ⟨r, info, e, hu, he, hg⟩ := h
  rcases he with rfl | ⟨-, h0⟩
  · exact not_granted_past r who _ _ hu hg
  · exact absurd h0 (by decide)

/-- A response's range key-values are in `[a, b)` (the other kinds hold none). -/
def respInAB : OpRespM → Prop
  | .range _ kvs _ _ => ∀ kv ∈ kvs, inRange lo hi kv.key = true
  | _ => True

/-- A range reply's key-values are of the selected ones (sorted, cut, keys only). -/
theorem rangeKvsOk_keys (o : OpFull) (sel kvs : List EtcdKv) (h : rangeKvsOk o sel kvs) :
    ∀ kv ∈ kvs, ∃ v ∈ sel, v.key = kv.key := by
  obtain ⟨l, hperm, -, -, -, rfl⟩ := h
  intro kv hkv
  split at hkv
  · simp at hkv
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hkv
  have hvl : v ∈ l := by
    split at hv
    · exact List.mem_of_mem_take hv
    · exact hv
  refine ⟨v, hperm.mem_iff.1 hvl, ?_⟩
  split <;> rfl

/-- Each response is related to an operation of the branch and its result. -/
theorem opRespsRel_mem (skip : Bool) (ops : List TxnOp) :
    ∀ (rs : List TxnOpResult) (ms : List OpRespM), opRespsRel skip ops rs ms →
      ∀ x ∈ ms, ∃ op ∈ ops, ∃ res ∈ rs, opRespRel skip op res x := by
  induction ops with
  | nil =>
    intro rs ms h
    cases rs <;> cases ms <;> simp [opRespsRel] at h ⊢
  | cons op ops ih =>
    intro rs ms h
    cases rs with
    | nil => cases ms <;> simp [opRespsRel] at h
    | cons res rs =>
      cases ms with
      | nil => simp [opRespsRel] at h
      | cons m ms =>
        obtain ⟨h1, h2⟩ := h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨op, List.mem_cons_self .., res, List.mem_cons_self .., h1⟩
        · obtain ⟨op', hop', res', hres', h'⟩ := ih rs ms h2 x hx
          exact ⟨op', List.mem_cons_of_mem _ hop', res', List.mem_cons_of_mem _ hres', h'⟩

/-- **T1's reply reads only `[a, b)`**: its comparisons are none, so its then branch ran; its get's
response holds key-values of the state's range `[a, b)`. -/
theorem t1_reads (k v : GoString) (r : w64) (s : List EtcdKv) (skip : Bool) (m : TxnRespM)
    (hs : m.succeeded = (txn.srvRunTxn r s (txnWireOf (t1M k v))).1)
    (hr : opRespsRel skip ((txnWireOf (t1M k v)).branch m.succeeded)
      (txn.srvRunTxn r s (txnWireOf (t1M k v))).2.2 m.resps) :
    ∀ x ∈ m.resps, respInAB x := by
  have hok : (txn.srvRunTxn r s (txnWireOf (t1M k v))).1 = true := by
    simp [txn.srvRunTxn, t1M, txnWireOf]
  rw [hs, hok] at hr
  simp [txn.srvRunTxn, t1M, txnWireOf, TxnModel.branch, txn.srvOps_cons, txn.srvOps_nil,
    txn.srvOp, opWire] at hr
  intro x hx
  obtain ⟨op, hop, res, hres, h⟩ := opRespsRel_mem skip _ _ _ hr x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop hres
  cases x with
  | range rev kvs more count =>
    simp only [respInAB]
    rcases hop with rfl | rfl
    · rcases hres with rfl | rfl <;> simp [opRespRel] at h
    rcases hres with rfl | rfl
    · simp [opRespRel] at h
    unfold opRespRel at h
    split at h
    · intro kv hkv; simp_all
    obtain ⟨-, kvs', hk, rfl⟩ := h
    intro kv hkv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hkv
    obtain ⟨u, hu, hue⟩ := rangeKvsOk_keys _ _ _ hk w hw
    have hin := (List.mem_filter.1 (List.mem_filter.1 hu).1).2
    rw [get_ab_ok.2.2.1, get_ab_ok.2.2.2] at hin
    have : (txn.leaseZ (txn.fastKeysOnly (rangeWireOf (opGetModel lo [withRangeM hi]))) w).key =
        w.key := by unfold txn.leaseZ; split <;> rfl
    rw [this, ← hue]; exact hin
  | _ => trivial

end pure

section calls
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The set-up's requested log, a lower bound (`akAuthFixed`'s). -/
theorem akAuthFixed_lb (γa : auth.AuthNames) (ρ : ReqNames) (Lset : List EntryModel) (n : Nat) :
    akAuthFixed (GF := GF) γa ρ Lset n ⊢ srvReqLogLb ρ.raft Lset := by
  iintro #Hf
  iunfold akAuthFixed at Hf
  icases Hf with ⟨-, -, #HL, -⟩
  iexact HL

/-- **The update a write of `who`'s sends**: `akHist_writeAu` at the write's grant, read at
`setupSt` (`akOpGranted_of_grant`), at the set-up's log; its result, the write granted to `who`.
`hop`: a granted write is one the history admits. -/
theorem akWriteAu (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (conn : Loc) (ctx : GoInterface)
    (op : KVOp) (hγa : E.authMode = .on γa) (hout : metadata.outgoingOf ctx = akOut who)
    (hop : akOpGranted who op → opHistOk op) :
    akHistInv (GF := GF) ρ.kv ∗ akAuthFixed γa ρ Lset n ∗ attemptTokOk conn (akTokP γa who) ∗
      □ (srvTLSId s -∗ False) ⊢
      □ clientOpAuOn s E ρ conn ctx op (fun _ => iprop(⌜akOpGranted who op⌝)) := by
  iintro ⟨#Hinv, #Hf, #Hat, #Htls⟩
  ihave #HL := akAuthFixed_lb γa ρ Lset n $$ Hf
  ihave #Hw := akHist_writeAu ρ.kv op (clientGrant s E ρ conn ctx op Lset)
    (fun _ => iprop(⌜akOpGranted who op⌝)) $$ [Hinv]
  · iframe Hinv
    iintro !> %σ Hg
    imod (akOpGranted_of_grant s E γa ρ Lset n who conn ctx op σ _ hγa hout authHistN_akMask)
      $$ [] Hg with %Hok
    · iframe #
    imodintro
    isplitl []
    · ipureintro; exact hop Hok
    · ipureintro; exact Hok
  imodintro
  unfold clientOpAuOn
  iexists Lset
  iframe HL
  iexact Hw

/-- A put's reply holds its update's result. -/
theorem putReplied_Q (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (P : Prop) (cid mid : w64) (m : PutRespM) :
    putReplied E γr F o (fun _ => iprop(⌜P⌝)) cid mid m ⊢ ⌜P⌝ := by
  iintro H
  iunfold putReplied at H
  icases H with ⟨%_, %_, %_, %_, %_, -, -, -, -, -, %HP⟩
  ipureintro; exact HP

/-- A delete's reply holds its update's result. -/
theorem deleteReplied_Q (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (o : OpFull)
    (P : Prop) (cid mid : w64) (m : DelRespM) :
    deleteReplied E γr F o (fun _ => iprop(⌜P⌝)) cid mid m ⊢ ⌜P⌝ := by
  iintro H
  iunfold deleteReplied at H
  icases H with ⟨%_, %_, %_, %_, %_, %_, %_, -, -, -, -, -, %HP⟩
  ipureintro; exact HP

/-- **What every call of `Work`'s holds** (persistent): the client's `KV` field over `conn`, whose
attempts carry `who`'s tokens, the member's KV methods with auth on, the TLS refutation, the
history invariant, the auth state fixed after the set-up, an empty index certificate and an
empty option list. -/
def akCallEnv (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
    structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api : GoInterface) ∗
    kvObjAtC api conn [go!"127.0.0.1:23916"] ∗ attemptTokOk conn (akTokP γa who) ∗
    akKVOn go!"127.0.0.1:23916" s E ρ cid mid ∗ □ (srvTLSId s -∗ False) ∗ akHistInv ρ.kv ∗
    akAuthFixed γa ρ Lset n ∗ mvcc.idxCert E.γ.idx [] ∗ optsAt slice.nil [])

instance akCallEnv_persistent (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString) :
    Persistent (akCallEnv (GF := GF) cl api conn s E ρ cid mid γa Lset n who) := by
  unfold akCallEnv; infer_instance

/-- **`cli.Put(ctx, k, v)` of `who`'s**: a reply with no error was granted to `who` (`hop`: a
granted put keeps the history). -/
theorem work_put (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (k v : GoString) (hγa : E.authMode = .on γa)
    (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who)
    (hop : akOpGranted who (.put (putKeyOp k v)) → opHistOk (.put (putKeyOp k v))) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #v)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err = GoInterface.nil → akOpGranted who (.put (putKeyOp k v))⌝ }} := by
  iintro %Φ ⟨#Henv, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn (GoInterface.ok ci) (.put (putKeyOp k v))
    hγa hout hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨#Hput, -, -, -⟩
  wp_apply (client_Put_onG cl api conn _ s E ρ cid mid ci cd k v slice.nil _ []) $$ []
    as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, -, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := putReplied_Q _ _ _ _ _ _ _ _ $$ Hr
    ipureintro; intro _; exact Hq
  · ipureintro; intro h; exact absurd h Herr

/-- **`cli.Delete(ctx, k)` of `who`'s**: a reply with no error was granted to `who`. -/
theorem work_delete (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (k : GoString) (hk : k ≠ [])
    (hγa : E.authMode = .on γa) (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who)
    (hop : akOpGranted who (.deleteRange (txn.deleteOpOf k [] false)) →
      opHistOk (.deleteRange (txn.deleteOpOf k [] false))) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #k)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err = GoInterface.nil → akOpGranted who (.deleteRange (txn.deleteOpOf k [] false))⌝ }} := by
  iintro %Φ ⟨#Henv, #Hctx, #Hce⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn (GoInterface.ok ci)
    (.deleteRange (txn.deleteOpOf k [] false)) hγa hout hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, -, #Hdel, -⟩
  wp_apply (client_Delete_on cl api conn _ s E ρ cid mid ci cd k slice.nil _ [] hk) $$ []
    as %resp %err Hout
  · iframe #
  iapply HΦ
  icases Hout with (⟨%Herr, %m, -, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := deleteReplied_Q _ _ _ _ _ _ _ _ $$ Hr
    ipureintro; intro _; exact Hq
  · ipureintro; intro h; exact absurd h Herr.1

/-- **`cli.Get(ctx, key, opts...)` of `who`'s** (no sort, no panic): a reply with no error was
granted at `setupSt` to a user of `who`'s, for the request's range (`akRead_granted`), and its
keys are in that range (`srvRangeOk_keys`). -/
theorem work_get (cl api conn : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (hγa : E.authMode = .on γa)
    (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who)
    (hg : ¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1)
    (hs : (opGetModel key gs).base.sortSet = false) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
        optsAt sl gs }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : RangeRespM, rangeRespMsg resp m ∗
          ⌜(∃ (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (e : GoString),
              akUser who info.Username' ∧
              apply.authEndOf (rangeWireOf (opGetModel key gs)).base.rangeEnd e ∧
              auth.granted (setupSt r) (auth.authInfoM info) (rangeWireOf (opGetModel key gs)).key
                e .read) ∧
            ∀ kv ∈ m.kvs, inRange (rangeWireOf (opGetModel key gs)).key
              (rangeWireOf (opGetModel key gs)).base.rangeEnd kv.key = true⌝) }} := by
  iintro %Φ ⟨#Henv, #Hctx, #Hce, #Hopts⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobj, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, #Hrange, -, -⟩
  ihave #Hpub : auth.authPubLbM E.authMode n $$ []
  · rw [hγa]
    iunfold akAuthFixed at Hf
    icases Hf with ⟨#Hp, -⟩
    unfold auth.authPubLbM
    iexact Hp
  imod (monoNatLbOwn_0 (GF := GF) ρ.rd.committed) with #H0
  ihave #Hc0 : committedAtLeast ρ.rd (W64 0) $$ []
  · unfold committedAtLeast
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  ihave Hres := optsAt_res sl gs iprop(True) $$ Hopts
  iapply wp_fupd
  wp_apply (client_Get_on cl api conn _ s E ρ.rd cid mid (W64 0) n ci cd key sl gs iprop(True)
      (fun _ => iprop(True)) []) $$ [Hres] as %resp %err Hout
  · iframe #
    isplitl []
    · itrivial
    rw [hs]
    isplitl []
    · unfold sortNamesIf; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    isplitl []
    · ipureintro; exact hg
    iintro !>
    ileft
    ipureintro; rfl
  icases Hout with ⟨-, (⟨%Herr, %m, #Hm, #Hok, %md, %Hmd, #Hauth⟩ | ⟨%Herr, -⟩)⟩
  · ihave #Hseen := akTokSeen_attempt γa who conn md (by rw [← hout]; exact Hmd) $$ Hat
    imod (akRead_granted s E γa ρ ρ.rd Lset n who (W64 0) _ _ hγa) $$ [] Hauth with %Hg
    · iframe #
    imodintro
    iapply HΦ
    iunfold rangeReplyOk at Hok
    icases Hok with ⟨%log, -, -, %Hl, -⟩
    iright
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm
    ipureintro
    exact ⟨Hg, srvRangeOk_keys _ _ _ _ Hl.2.2.2.2.2.2.2.1⟩
  · imodintro
    iapply HΦ
    ileft
    ipureintro; exact Herr.1

/-- A writing transaction's reply holds its update's result. -/
theorem txnReplied_Q (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64) (F : mvcc.Log)
    (t : TxnModel) (P : Prop) (cid mid : w64) (m : TxnRespM) (hro : txn.txnReadonly t = false) :
    txnReplied E γw γr c F t (fun _ => iprop(⌜P⌝)) cid mid m ⊢ ⌜P⌝ := by
  iintro H
  unfold txnReplied
  rw [hro]
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%_, %_, %_, %_, %_, %_, %_, %_, -, -, -, -, -, %HP⟩
  ipureintro; exact HP

/-- **A writing transaction's reply, read as itself** (no range end `[0]`, `irrNoZeroEnd_txn`): its
update's result, and its responses those of its branch run on some state. -/
theorem txnReplied_facts (E : apply.AEnv GF) (γw γr : ReadNames) (c : w64) (F : mvcc.Log)
    (t : TxnModel) (P : Prop) (cid mid : w64) (m : TxnRespM) (hro : txn.txnReadonly t = false)
    (hz : txnNoZeroEnd t) :
    txnReplied E γw γr c F t (fun _ => iprop(⌜P⌝)) cid mid m ⊢
      ⌜P ∧ ∃ (r : w64) (s0 : List EtcdKv) (skip : Bool), m.succeeded = (txn.srvRunTxn r s0 t).1 ∧
        opRespsRel skip (t.branch m.succeeded) (txn.srvRunTxn r s0 t).2.2 m.resps⌝ := by
  iintro H
  unfold txnReplied
  rw [hro]
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%tw, %_, %_, %t', %x, %_, %_, %skip, %Hp, -, -, -, -, %HP⟩
  obtain ⟨htw, -, -, hzt, -, -, -, -, -, -, -, hsucc, hrel, -⟩ := Hp
  have ht : t' = t := hzt (irrNoZeroEnd_txn tw t htw hz)
  subst ht
  ipureintro
  exact ⟨HP, _, _, skip, hsucc, hrel⟩

/-- **`t.Commit()` of `who`'s writing transaction** (plain, no range end `[0]`, of the shape the
permission cache decides): a reply with no error was granted to `who` (`hop`: a granted
transaction keeps the history). -/
theorem work_commit (cl api conn tp : Loc) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat) (who : GoString)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (hγa : E.authMode = .on γa) (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who)
    (hp : TxnModel.plain (txnWireOf b.model)) (hin : txnModelIn (txnWireOf b.model))
    (hsh : ∀ tw : txn.TxnModelW, tw.toModel = txnWireOf b.model → kvShapeAll (irrTxn tw))
    (hro : txn.txnReadonly (txnWireOf b.model) = false)
    (hpl : txn.txnPlain (txnWireOf b.model) ∧ txnNoZeroEnd (txnWireOf b.model))
    (hop : akOpGranted who (.txn (txnWireOf b.model)) → opHistOk (.txn (txnWireOf b.model))) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗ txnObjAt tp [go!"127.0.0.1:23916"] ci cd b ∗
        txnKvIs tp api }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        ⌜err = GoInterface.nil → akOpGranted who (.txn (txnWireOf b.model))⌝ ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ m : TxnRespM, txnRespMsg resp m ∗
          ⌜∃ (r : w64) (s0 : List EtcdKv) (skip : Bool),
            m.succeeded = (txn.srvRunTxn r s0 (txnWireOf b.model)).1 ∧
            opRespsRel skip ((txnWireOf b.model).branch m.succeeded)
              (txn.srvRunTxn r s0 (txnWireOf b.model)).2.2 m.resps⌝) }} := by
  iintro %Φ ⟨#Henv, Hobj, #Hkt⟩ HΦ
  iunfold akCallEnv at Henv
  icases Henv with ⟨#Pc, #Hkvf, #Hobjc, #Hat, #Hkv, #Htls, #Hinv, #Hf, #HF, #Hnil⟩
  ihave #Hau := akWriteAu s E γa ρ Lset n who conn (GoInterface.ok ci)
    (.txn (txnWireOf b.model)) hγa hout hop $$ []
  · iframe #
  iunfold akKVOn at Hkv
  icases Hkv with ⟨-, -, -, #Htxn⟩
  ihave #Hpub : auth.authPubLbM E.authMode n $$ []
  · rw [hγa]
    iunfold akAuthFixed at Hf
    icases Hf with ⟨#Hp, -⟩
    unfold auth.authPubLbM
    iexact Hp
  imod (monoNatLbOwn_0 (GF := GF) ρ.rd.committed) with #H0
  ihave #Hc0 : committedAtLeast ρ.rd (W64 0) $$ []
  · unfold committedAtLeast
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  wp_apply (client_txn_on tp api conn _ s E ρ ρ.rd cid mid (W64 0) n ci cd b
      (fun _ => iprop(⌜akOpGranted who (.txn (txnWireOf b.model))⌝)) [] hp hin
      (fun _ => hsh)) $$ [Hobj] as %resp %err Hout
  · iframe #
    iframe Hobj
    ileft
    iintro !>
    unfold txnUpdAtOn
    iright
    iright
    isplitl []
    · ipureintro; exact ⟨hro, hpl⟩
    iexact Hau
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, Hr, -⟩ | ⟨%Herr, -⟩)
  · ihave %Hq := txnReplied_facts _ _ _ _ _ _ _ _ _ _ hro hpl.2 $$ Hr
    isplitl []
    · ipureintro; intro _; exact Hq.1
    iright
    iexists m
    iframe Hm
    ipureintro; exact Hq.2
  · isplitl []
    · ipureintro; intro h; exact absurd h Herr.1
    ileft; ipureintro; exact Herr.1

/-- **T4, a nested transaction putting outside `[a, b)`, is refused** (`sorry`, until the client's
builder and `Commit` specs cover nested transactions: branch `txn-nested`, the plan's T4):
`t.Then(OpTxn(nil, [OpPut(c/who/t3, "vt")], nil))` returns the builder, whose `Commit` replies
with an error (no principal may write `c/...`: `not_permitted_c`; etcd checks a nested
transaction's operations, `checkTxnReqsPermission`). Today's `txn.Then.spec` takes only plain
operations (`txnOpOf` of a transaction is `none`), and `reqOpAt` of one is `False`. -/
theorem then_commit_nested_refused (cl api conn tp : Loc) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) (γa : auth.AuthNames) (Lset : List EntryModel) (n : Nat)
    (who : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl tsl : GoSlice)
    (op : go_etcd_io.etcd.client.v3.Op) (hγa : E.authMode = .on γa)
    (hout : metadata.outgoingOf (GoInterface.ok ci) = akOut who) :
    {{ akCallEnv cl api conn s E ρ cid mid γa Lset n who ∗
        txnObjAt tp [go!"127.0.0.1:23916"] ci cd TxnBuild.empty ∗ txnKvIs tp api ∗
        sl ↦*□ [op] ∗ opFullAt op OpFull.txnInit ∗ cmpsAt op.cmps' [] ∗
        ⌜op.thenOps' = tsl ∧ op.elseOps' = slice.nil⌝ ∗
        opsAt tsl [opPutModel (keyOfK go!"c" who go!"t3") go!"vt" []] }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then"))
        (Val #sl))
    {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp :
          GoInterface);
        ∀ Φ, (∀ (resp : Loc) (err : GoInterface), ⌜err ≠ GoInterface.nil⌝ -∗
            Φ (PairV #resp #err)) -∗
          WP (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!!
            go!"Commit")) (Val #())) {{ Φ }} }} := by
  sorry

/-- **One option** (a `Get(k, opt)`'s variadic slice). -/
theorem optsAt_one (sl : GoSlice) (f : GoFunc) (g : OpFull → OpFull) :
    sl ↦*□ [f] ∗ optSpec (GF := GF) f g ⊢ optsAt sl [g] := by
  iintro ⟨#Hsl, #Hf⟩
  iunfold optsAt
  iexists [f]
  iframe Hsl
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %f' %g' %Hf' %Hg'
  rcases i with _ | i
  · cases Hf'; cases Hg'; iexact Hf
  · simp at Hf'

/-- **One operation** (a `Then(op)`'s variadic slice). -/
theorem opsAt_one (sl : GoSlice) (v1 : go_etcd_io.etcd.client.v3.Op) (o1 : OpFull) :
    sl ↦*□ [v1] ∗ opFullAt (GF := GF) v1 o1 ⊢ opsAt sl [o1] := by
  iintro ⟨#Hsl, #H1⟩
  iunfold opsAt
  iexists [v1]
  iframe Hsl
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %v %o %Hv %Ho
  rcases i with _ | i
  · cases Hv; cases Ho; iexact H1
  · simp at Hv

/-- **Two operations** (a `Then(op1, op2)`'s variadic slice). -/
theorem opsAt_two (sl : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Op)
    (v1 v2 : go_etcd_io.etcd.client.v3.Op) (o1 o2 : OpFull) (hvs : vs = [v1, v2]) :
    sl ↦*□ vs ∗ opFullAt (GF := GF) v1 o1 ∗ opFullAt v2 o2 ⊢ opsAt sl [o1, o2] := by
  subst hvs
  iintro ⟨#Hsl, #H1, #H2⟩
  iunfold opsAt
  iexists [v1, v2]
  iframe Hsl
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %v %o %Hv %Ho
  rcases i with _ | _ | i
  · cases Hv; cases Ho; iexact H1
  · cases Hv; cases Ho; iexact H2
  · simp at Hv

/-- No comparisons: the nil slice. -/
theorem cmpsAt_nil' : ⊢ cmpsAt (GF := GF) slice.nil [] := by
  unfold cmpsAt
  iexists ([] : List go_etcd_io.etcd.client.v3.Cmp)
  isplitl
  · iapply ownSlice_nil
  isplitl
  · ipureintro; rfl
  imodintro
  iintro %i %c %m %Hc %Hm
  simp at Hc

/-- **One comparison** (an `If(c)`'s variadic slice). -/
theorem cmpsAt_one (sl : GoSlice) (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel) :
    sl ↦*□ [c] ∗ cmpAt (GF := GF) c m ⊢ cmpsAt sl [m] := by
  iintro ⟨#Hsl, #H1⟩
  iunfold cmpsAt
  iexists [c]
  iframe Hsl
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %c' %m' %Hc %Hm
  rcases i with _ | i
  · cases Hc; cases Hm; iexact H1
  · simp at Hc

end calls

end authkv
end EtcdGrove
end Perennial
