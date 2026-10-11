/-
The STM's commit, key by key (pure): a committed attempt's transaction applies its writes to the
state it ran on, each key independently of the order of the write set. The Results' atomicity
theorems (`Results.lean`: `stm_atomicity`, `stm_repeatable_reads`, `stm_read_committed`) read
`STMCommitted` (`InvSTM.lean`) through it. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency

/-- **A write applied to a key** at revision `R`: no write keeps the key-value; a put of `v` with
lease `l` makes it `v`, modified at `R` (a new key: created at `R`, version 1; an existing one:
its create revision kept, its version incremented); a delete removes it. -/
def applyWriteKv (R : w64) (k : GoString) (old : Option EtcdKv) : Option WriteM → Option EtcdKv
  | none => old
  | some (.put v l) => some (match old with
      | some o => { o with modRev := R, version := o.version + W64 1, value := v, lease := l }
      | none => { key := k, createRev := R, modRev := R, version := W64 1, value := v, lease := l })
  | some .del => none

/-! ## One operation, key by key -/

theorem kvAt_cons (w : EtcdKv) (ws : List EtcdKv) (k : GoString) :
    kvAt (w :: ws) k = if w.key = k then some w else kvAt ws k := by
  unfold kvAt; by_cases h : w.key = k <;> simp [h]

/-- `btInsert` on a list sorted by key: the inserted key-value replaces its key's, if any. -/
theorem kvAt_btInsert (nv : EtcdKv) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess → ∀ k,
      kvAt (btInsert etcdKvLess nv s) k = if nv.key = k then some nv else kvAt s k
  | [], _, k => by simp [btInsert, kvAt]
  | w :: ws, hs, k => by
    rw [List.pairwise_cons] at hs
    unfold btInsert
    split
    · rename_i hwv
      rw [kvAt_cons, kvAt_btInsert nv ws hs.2 k, kvAt_cons]
      by_cases hwk : w.key = k
      · have : nv.key ≠ k := by
          intro h; unfold etcdKvLess at hwv; rw [hwk, h] at hwv; exact goStringLt_irrefl _ hwv
        simp [hwk, this]
      · simp [hwk]
    · split
      · rw [kvAt_cons, kvAt_cons]
      · rename_i hwv hvw
        have heq : w.key = nv.key := goStringLt_eq_of_not_lt hwv hvw
        rw [kvAt_cons, kvAt_cons]
        by_cases hk : nv.key = k
        · simp [hk]
        · simp [hk, heq]

/-- `kvAt` of a key-value's own key is the first one with that key; on a sorted list, its key's
only one. -/
theorem kvAt_filter_ne (s : List EtcdKv) (k0 k : GoString) :
    kvAt (s.filter (fun v => !inRange k0 [] v.key)) k = if k0 = k then none else kvAt s k := by
  induction s with
  | nil => simp [kvAt]
  | cons w ws ih =>
    rw [List.filter_cons]
    by_cases hw : w.key = k0
    · have : inRange k0 [] w.key = true := by simp [inRange, hw]
      simp only [this, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [ih, kvAt_cons]
      by_cases hk : k0 = k
      · simp [hk]
      · have : w.key ≠ k := by rw [hw]; exact hk
        simp [hk, this]
    · have : inRange k0 [] w.key = false := by simp [inRange, hw]
      simp only [this, Bool.not_false, ↓reduceIte]
      rw [kvAt_cons, kvAt_cons, ih]
      by_cases hk : k0 = k
      · have : w.key ≠ k := by rw [← hk]; exact hw
        simp [hk, this]
      · simp [hk]

theorem rangeIn_deleteOp_filter (k0 : GoString) (_s : List EtcdKv) :
    (opDeleteModel k0 []).key = k0 ∧ (opDeleteModel k0 []).base.rangeEnd = [] := by
  simp [opDeleteModel, opFold, OpFull.deleteInit, OpFull.newOp, OpModel.zero]

theorem kvAt_put (R : w64) (k0 v : GoString) (l : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) (k : GoString) :
    kvAt (putKv R k0 v l s) k = if k0 = k then applyWriteKv R k0 (kvAt s k0) (some (.put v l))
      else kvAt s k := by
  unfold putKv
  rw [kvAt_btInsert _ s hs k]
  unfold applyWriteKv kvAt
  split
  · rename_i v0 h
    have hk : v0.key = k0 := by simpa using List.find?_some h
    simp [h, hk]
  · rename_i h
    simp [h]

theorem putKv_sorted (R : w64) (k0 v : GoString) (l : w64) (s : List EtcdKv)
    (hs : s.Pairwise etcdKvLess) : (putKv R k0 v l s).Pairwise etcdKvLess := by
  unfold putKv; exact btInsert_sorted etcdKvLess_swo hs

/-! ## The write set's operations -/

/-- The operations of a list of writes (distinct keys). -/
def writesOps (l : List (GoString × WriteM)) : List TxnOp := l.map (fun kw => kw.2.op kw.1)

theorem lookup_none_of_not_mem {V : Type} (k : GoString) :
    ∀ l : List (GoString × V), k ∉ l.map Prod.fst → l.lookup k = none
  | [], _ => rfl
  | (k1, v) :: l, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : (k == k1) = false := by simp [beq_iff_eq]; exact h.1
    simp [List.lookup, hne, lookup_none_of_not_mem k l h.2]

theorem runOps_writes (R : w64) :
    ∀ (l : List (GoString × WriteM)) (s : List EtcdKv), (l.map Prod.fst).Nodup →
      s.Pairwise etcdKvLess →
      (runOps R s (writesOps l)).1.Pairwise etcdKvLess ∧
      ∀ k, kvAt (runOps R s (writesOps l)).1 k = applyWriteKv R k (kvAt s k) (l.lookup k)
  | [], s, _, hs => ⟨hs, fun k => by simp [writesOps, runOps, applyWriteKv, List.lookup]⟩
  | (k0, w) :: l, s, hnd, hs => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk0, hnd⟩ := hnd
    cases w with
    | put v le =>
      have hs' := putKv_sorted R k0 v le s hs
      obtain ⟨ih1, ih2⟩ := runOps_writes R l _ hnd hs'
      refine ⟨by simpa [writesOps, runOps, WriteM.op, applyTxnOp] using ih1, fun k => ?_⟩
      have := ih2 k
      simp only [writesOps, List.map_cons, runOps, WriteM.op, applyTxnOp] at this ⊢
      rw [this, kvAt_put R k0 v le s hs k]
      by_cases hk : k0 = k
      · subst hk
        have : l.lookup k0 = none := lookup_none_of_not_mem k0 l hk0
        simp [this, List.lookup, applyWriteKv]
      · have hne : (k == k0) = false := by simp [beq_iff_eq]; exact fun h => hk h.symm
        simp [hk, List.lookup, hne]
    | del =>
      have hs' : (s.filter (fun v => !inRange (opDeleteModel k0 []).key
          (opDeleteModel k0 []).base.rangeEnd v.key)).Pairwise etcdKvLess :=
        List.Pairwise.sublist List.filter_sublist hs
      obtain ⟨ih1, ih2⟩ := runOps_writes R l _ hnd hs'
      refine ⟨by simpa [writesOps, runOps, WriteM.op, applyTxnOp] using ih1, fun k => ?_⟩
      have := ih2 k
      simp only [writesOps, List.map_cons, runOps, WriteM.op, applyTxnOp] at this ⊢
      rw [this]
      obtain ⟨hkey, hre⟩ := rangeIn_deleteOp_filter k0 s
      rw [hkey, hre, kvAt_filter_ne s k0 k]
      by_cases hk : k0 = k
      · subst hk
        have : l.lookup k0 = none := lookup_none_of_not_mem k0 l hk0
        simp [this, List.lookup, applyWriteKv]
      · have hne : (k == k0) = false := by simp [beq_iff_eq]; exact fun h => hk h.symm
        simp [hk, List.lookup, hne]

/-- The write set's operations, in the order of a key list `ks` of it, are those of the list of
its entries in that order. -/
theorem writeOps_list (writes : GMap GoString WriteM) (ks : List GoString) :
    ks.filterMap (fun k => (writes !! k).map (WriteM.op k)) =
      writesOps (ks.filterMap (fun k => (writes !! k).map (k, ·))) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.filterMap_cons]
    cases h : writes !! k <;> simp [h, ih, writesOps]

theorem writes_list_keys (writes : GMap GoString WriteM) (ks : List GoString) :
    (ks.filterMap (fun k => (writes !! k).map (k, ·))).map Prod.fst =
      ks.filter (fun k => (writes !! k).isSome) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    cases h : writes !! k <;> simp [h, ih]

theorem writes_list_lookup_mem (writes : GMap GoString WriteM) (k : GoString) :
    ∀ ks : List GoString, (ks.filterMap (fun k => (writes !! k).map (k, ·))).lookup k =
      if k ∈ ks then writes !! k else none
  | [] => by simp [List.lookup]
  | k1 :: ks => by
    have ih := writes_list_lookup_mem writes k ks
    simp only [List.filterMap_cons]
    by_cases hk : k1 = k
    · subst hk
      cases h : writes !! k1 with
      | none => simp [h, ih]
      | some w => simp [h, List.lookup]
    · have hne : (k == k1) = false := by simp [beq_iff_eq]; exact fun h => hk h.symm
      have hmem : (k ∈ k1 :: ks) ↔ k ∈ ks := by
        simp only [List.mem_cons]; exact ⟨fun h => h.resolve_left (fun h' => hk h'.symm), Or.inr⟩
      cases h : writes !! k1 <;> simp [h, List.lookup, hne, ih, hmem]

theorem writes_list_lookup (writes : GMap GoString WriteM) (ks : List GoString)
    (hks : MapKeysList writes ks) (k : GoString) :
    (ks.filterMap (fun k => (writes !! k).map (k, ·))).lookup k = writes !! k := by
  rw [writes_list_lookup_mem]
  split
  · rfl
  · rename_i h
    cases hw : writes !! k with
    | none => rfl
    | some w => exact absurd ((hks.2 k).2 (by simp [hw])) h

theorem writes_list_nodup (writes : GMap GoString WriteM) (ks : List GoString)
    (hks : MapKeysList writes ks) :
    ((ks.filterMap (fun k => (writes !! k).map (k, ·))).map Prod.fst).Nodup := by
  rw [writes_list_keys]
  exact hks.1.filter _

/-- **The commit's writes, key by key**: on a state sorted by key, the write set's operations (in
any order of its keys, `WriteOpsOk`) leave each key as `applyWriteKv` of its write (its
key-value untouched if it is not written). -/
theorem runOps_writeOps_kvAt (R : w64) (s : List EtcdKv) (writes : GMap GoString WriteM)
    (ops : List TxnOp) (hs : (s.map EtcdKv.key).Pairwise go.GoStringLt)
    (h : WriteOpsOk writes ops) (k : GoString) :
    kvAt (runOps R s ops).1 k = applyWriteKv R k (kvAt s k) (writes !! k) := by
  obtain ⟨ks, hks, rfl⟩ := h
  rw [writeOps_list]
  have hs' : s.Pairwise etcdKvLess := by
    rw [List.pairwise_map] at hs; exact hs
  rw [(runOps_writes R _ s (writes_list_nodup writes ks hks) hs').2 k,
    writes_list_lookup writes ks hks k]

/-! ## What a committed attempt means, per level -/

/-- **A committed attempt of a serializable level** (`SerializableSnapshot`, `Serializable`): the
attempt's reads are the key-values of the state `s` the commit ran on, and the state `s'` it left
is `s` with the attempt's writes applied, key by key (`applyWriteKv`; an unwritten key is
unchanged); `SerializableSnapshot` also: every written key's mod revision in `s` is at most
`first()`. With `stmOutcome`'s `txnStates`, `s` is etcd's state at `R - 1` and `s'` at `R` if the
commit wrote (`s = s'` at `R` otherwise): the attempt ran atomically at `R`. -/
theorem stmCommitted_serializable (pfx : GoString) (lvl lo : w64) (st : STMSt) (R : w64)
    (s s' : List EtcdKv) (ops : List TxnOp) (h : STMCommitted pfx lvl lo st R s s' ops)
    (hl : lvl = isoSS ∨ lvl = isoS) :
    (∀ k e, st.reads !! k = some e → kvAt s k = e.kv) ∧
    (∀ k, kvAt s' k = applyWriteKv R k (kvAt s k) (st.writes !! k)) ∧
    (lvl = isoSS → ∃ f, FirstOk st.reads f ∧
      ∀ k, (st.writes !! k).isSome → sint.Z (modRevAt s k) < sint.Z (f + W64 1)) := by
  obtain ⟨hwf, rfl, hops, -, -, -, hagree, hss⟩ := h
  refine ⟨hagree (by rcases hl with rfl | rfl <;> decide), fun k => ?_, hss⟩
  exact runOps_writeOps_kvAt R s st.writes ops hwf.1 hops k

/-- **A committed `RepeatableReads` attempt**: as the serializable levels (without the write
comparison): the reads are `s`'s key-values, and `s'` is `s` with the writes applied. -/
theorem stmCommitted_repeatableReads (pfx : GoString) (lo : w64) (st : STMSt) (R : w64)
    (s s' : List EtcdKv) (ops : List TxnOp) (h : STMCommitted pfx isoRR lo st R s s' ops) :
    (∀ k e, st.reads !! k = some e → kvAt s k = e.kv) ∧
    (∀ k, kvAt s' k = applyWriteKv R k (kvAt s k) (st.writes !! k)) := by
  obtain ⟨hwf, rfl, hops, -, -, -, hagree, -⟩ := h
  exact ⟨hagree (by decide), fun k => runOps_writeOps_kvAt R s st.writes ops hwf.1 hops k⟩

/-- **A committed attempt, any level** (`ReadCommitted` included): `s'` is `s` with the writes
applied, key by key; nothing relates the reads to `s` (each read is only its own revision's,
`readFact`). -/
theorem stmCommitted_writes (pfx : GoString) (lvl lo : w64) (st : STMSt) (R : w64)
    (s s' : List EtcdKv) (ops : List TxnOp) (h : STMCommitted pfx lvl lo st R s s' ops) :
    ∀ k, kvAt s' k = applyWriteKv R k (kvAt s k) (st.writes !! k) := by
  obtain ⟨hwf, rfl, hops, -⟩ := h
  exact fun k => runOps_writeOps_kvAt R s st.writes ops hwf.1 hops k

end concurrency
end EtcdGrove
end Perennial
