/-
The lessor window of a transaction's run (auth-lease S4 item 7b, step 5): a revision whose keys are distinct moves
each lease item at most once, toward the items after it (`winOps_txn_of_nodup`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open go_etcd_io.etcd.server.v3.storage.mvcc

section win
variable [GooseExts]

/-! #### Step 5: a revision whose keys are distinct moves each item once, toward the items after it -/

/-- Changes touching no key `k` keep `k`'s key-value. -/
theorem findKey_applyChanges_other (r : w64) (k : GoString) :
    ∀ (cs : List mvcc.Change) (s : List EtcdKv), s.Pairwise etcdKvLess → k ∉ cs.map mvcc.Change.key →
      mvcc.findKey k (mvcc.applyChanges r s cs) = mvcc.findKey k s
  | [], _, _, _ => rfl
  | c :: cs, s, hs, hk => by
    rw [applyChanges_cons]
    have hk1 : c.key ≠ k := fun h => hk (by simp [h])
    have hk2 : k ∉ cs.map mvcc.Change.key := fun h => hk (List.mem_cons_of_mem _ h)
    rw [findKey_applyChanges_other r k cs _ (mvcc.applyChange_sorted hs r c) hk2]
    cases c with
    | put k' v l => exact mvcc.findKey_putKv_other hs r k k' v l hk1
    | del k' =>
      simp only [mvcc.applyChange]
      rw [mvcc.findKey_filter_ne]
      simp only [mvcc.Change.key] at hk1
      simp [hk1]

/-- Deleting a list of keys that holds `k` leaves no `k`. -/
theorem findKey_applyChanges_dels_mem (r : w64) (k : GoString) :
    ∀ (ks : List GoString) (s : List EtcdKv), k ∈ ks →
      mvcc.findKey k (mvcc.applyChanges r s (ks.map .del)) = none
  | [], _, h => by cases h
  | k' :: ks, s, h => by
    rw [List.map_cons, applyChanges_cons]
    by_cases hin : k ∈ ks
    · exact findKey_applyChanges_dels_mem r k ks _ hin
    · have hk : k' = k := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd h hin
      rw [mvcc.findKey_applyChanges_dels r k ks _ hin]
      simp only [mvcc.applyChange]
      rw [mvcc.findKey_filter_ne]
      simp [hk]

/-- The items a delete's range selects are the client's range's. -/
theorem delSelOf_iff (o : OpFull) (it : go_etcd_io.etcd.server.v3.lease.LeaseItem) :
    delSelOf o it ↔ inRange o.key o.base.rangeEnd it.Key' = true := by
  unfold delSelOf mvcc.delSel
  rw [← srvInRange_srvEnd]
  unfold srvInRange
  split <;> simp

/-- **A change list `c` followed by `B`, the keys of `c ++ B` distinct**: `c` moves the items toward those after
`c ++ B` (each item `c` changes, `B` leaves alone). -/
theorem winMove_of_nodup (st : Nat) {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64)
    (c B : List mvcc.Change) (hnd : ((c ++ B).map mvcc.Change.key).Nodup) :
    lease.winMove (some (st, mvcc.leaseItemsOf (mvcc.applyChanges r (mvcc.applyChanges r s c) B)))
      (mvcc.leaseItemsOf s) (mvcc.leaseItemsOf (mvcc.applyChanges r s c)) := by
  intro v hv it hne
  cases hv
  simp only [mvcc.leaseItemsOf_lookup] at hne ⊢
  have hc : it.Key' ∈ c.map mvcc.Change.key := Classical.byContradiction fun hn =>
    hne (by rw [findKey_applyChanges_other r _ c s hs hn])
  have hB : it.Key' ∉ B.map mvcc.Change.key := by
    rw [List.map_append, List.nodup_append] at hnd
    exact fun h => hnd.2.2 _ hc _ h rfl
  rw [findKey_applyChanges_other r _ B _ (mvcc.applyChanges_sorted r c hs) hB]

mutual
/-- **Step 5, per operation**: an operation whose changes, followed by `B`, have distinct keys is within the window
whose target is the items after both. -/
theorem winOp_of_nodup (st : Nat) (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (op : TxnOp) (B : List mvcc.Change), s.Pairwise etcdKvLess →
      (((srvOp s0 r s op).1 ++ B).map mvcc.Change.key).Nodup →
      WinOp (some (st, mvcc.leaseItemsOf
        (mvcc.applyChanges r (mvcc.applyChanges r s (srvOp s0 r s op).1) B))) s0 r s op
  | _, .get _, _, _, _ => trivial
  | s, .put k v l, B, hs, hnd => winMove_of_nodup st hs r _ B hnd
  | s, .putKeep k v, B, hs, hnd => winMove_of_nodup st hs r _ B hnd
  | s, .putIgnVal k l, B, hs, hnd => winMove_of_nodup st hs r _ B hnd
  | s, .delete o, B, hs, hnd => by
    intro v hv it hsel hpres
    cases hv
    rw [srvOp_delete] at hnd ⊢
    simp only [mvcc.leaseItemsOf_lookup] at hpres ⊢
    obtain ⟨kv, hkv⟩ : ∃ kv, mvcc.findKey it.Key' s = some kv := by
      cases h : mvcc.findKey it.Key' s with
      | none => rw [h] at hpres; exact absurd rfl hpres
      | some kv => exact ⟨kv, rfl⟩
    have hmem : kv ∈ s := List.mem_of_find?_eq_some hkv
    have hkk : kv.key = it.Key' := by simpa using List.find?_some hkv
    have hin : kv ∈ rangeIn s o := by
      unfold rangeIn
      rw [List.mem_filter]
      exact ⟨hmem, by rw [hkk]; exact (delSelOf_iff o it).1 hsel⟩
    have hks : it.Key' ∈ (rangeIn s o).map EtcdKv.key := by
      rw [← hkk]; exact List.mem_map_of_mem hin
    have hc : it.Key' ∈ (delChanges s o).map mvcc.Change.key := by
      unfold delChanges; rw [List.map_map]; simpa [Function.comp_def, mvcc.Change.key] using hks
    have hB : it.Key' ∉ B.map mvcc.Change.key := by
      rw [List.map_append, List.nodup_append] at hnd
      exact fun h => hnd.2.2 _ hc _ h rfl
    rw [findKey_applyChanges_other r _ B _ (mvcc.applyChanges_sorted r _ hs) hB]
    have hdel : delChanges s o = ((rangeIn s o).map EtcdKv.key).map .del := by
      unfold delChanges; rw [List.map_map]; rfl
    rw [hdel, findKey_applyChanges_dels_mem r _ _ s hks]
    rfl
  | s, .txn cs ts es, B, hs, hnd => by
    rw [srvOp_txn] at hnd ⊢
    simp only [WinOp]
    cases hb : cs.all (cmpHolds s0)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
      exact winOps_of_nodup st s0 r s es B hs hnd
    · simp only [hb, ↓reduceIte] at hnd ⊢
      exact winOps_of_nodup st s0 r s ts B hs hnd

/-- **Step 5**: operations whose changes, followed by `B`, have distinct keys are within the window whose target is
the items after both. -/
theorem winOps_of_nodup (st : Nat) (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp) (B : List mvcc.Change), s.Pairwise etcdKvLess →
      (((srvOps s0 r s ops).1 ++ B).map mvcc.Change.key).Nodup →
      WinOps (some (st, mvcc.leaseItemsOf
        (mvcc.applyChanges r (mvcc.applyChanges r s (srvOps s0 r s ops).1) B))) s0 r s ops
  | _, [], _, _, _ => trivial
  | s, op :: ops, B, hs, hnd => by
    rw [srvOps_cons] at hnd ⊢
    simp only [List.append_assoc] at hnd
    have hT : mvcc.applyChanges r (mvcc.applyChanges r s ((srvOp s0 r s op).1 ++
        (srvOps s0 r (mvcc.applyChanges r s (srvOp s0 r s op).1) ops).1)) B =
      mvcc.applyChanges r (mvcc.applyChanges r s (srvOp s0 r s op).1)
        ((srvOps s0 r (mvcc.applyChanges r s (srvOp s0 r s op).1) ops).1 ++ B) := by
      rw [applyChanges_append, applyChanges_append]
    rw [hT]
    refine ⟨winOp_of_nodup st s0 r s op _ hs hnd, ?_⟩
    have hnd' : (((srvOps s0 r (mvcc.applyChanges r s (srvOp s0 r s op).1) ops).1 ++ B).map
        mvcc.Change.key).Nodup := by
      rw [List.map_append] at hnd; exact (List.nodup_append.1 hnd).2.1
    have h := winOps_of_nodup st s0 r _ ops B (mvcc.applyChanges_sorted r _ hs) hnd'
    rw [applyChanges_append]; exact h
end

/-- **Step 5 at a transaction's entry**: the changes of a transaction at the log `log` with distinct keys (etcd's
`checkIntervals`, `keys_nodup_iff_check`) make its run within the window whose target is the items after it. -/
theorem winOps_txn_of_nodup (st : Nat) (log : mvcc.Log) (t : TxnModel)
    (hnd : ((txnChs log t).map mvcc.Change.key).Nodup) :
    WinOps (some (st, mvcc.leaseItemsOf (mvcc.applyChanges (W64 (log.length : Int)) (mvcc.stateAfter log)
        (txnChs log t)))) (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
      (t.branch (txnOk (mvcc.stateAfter log) t)) := by
  simp only [txnChs, srvRunTxn] at hnd ⊢
  have h := winOps_of_nodup st (mvcc.stateAfter log) (W64 (log.length : Int)) (mvcc.stateAfter log)
    (t.branch (txnOk (mvcc.stateAfter log) t)) [] (mvcc.stateAfter_sorted log) (by simpa using hnd)
  simpa [applyChanges_nil'] using h


/-- A move to the window's own target (a single put request's entry: the target is the items after it). -/
theorem winMove_to_target (st : Nat) (I I' : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) :
    lease.winMove (some (st, I')) I I' := fun v hv _ _ => by cases hv; rfl

end win
end txn
end EtcdGrove
end Perennial
