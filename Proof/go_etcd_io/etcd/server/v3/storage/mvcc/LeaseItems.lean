/-
The lessor's item map of a KV state (unit T3, L2b, 2026-10-25). Lean-first (no Rocq counterpart).

The lessor's item map (`le.itemMap`: a key, as a `lease.LeaseItem`, to its lease) is, for the
store's caller (the lease owner, `lease.leaseOwn γl L I`), the leases of the store's state:
`leaseItemsOf s` maps each key of `s` with a lease (not `0`) to it. A put (`storeTxnWrite.put`:
`GetLease`, then `Detach` of the old lease and `Attach` of the new) and a delete (`GetLease`,
`Detach`) keep the owner's `I` the item map of the store's pending state.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open go_etcd_io.etcd.server.v3.lease

section items
variable [GooseExts]

/-- The lease of the key-value `kv`, as an item map's entry: none for `0` (no lease). -/
def kvLease (kv : EtcdKv) : Option w64 := if kv.lease = W64 0 then none else some kv.lease

/-- **The lessor's item map of the KV state `s`**: each key of `s` with a lease, to it. -/
def leaseItemsOf (s : List EtcdKv) : GMap LeaseItem w64 :=
  ⟨fun it => (findKey it.Key' s).bind kvLease,
   ⟨s.map (fun kv => LeaseItem.mk kv.key), by
     intro it h
     cases hf : findKey it.Key' s with
     | none => rw [hf] at h; cases h
     | some kv =>
       have hm : kv ∈ s := List.mem_of_find?_eq_some hf
       have hk : kv.key = it.Key' := by simpa using List.find?_some hf
       apply List.mem_map.2
       exact ⟨kv, hm, by cases it; simp [hk]⟩⟩⟩

theorem leaseItemsOf_lookup (s : List EtcdKv) (it : LeaseItem) :
    (leaseItemsOf s).lookup it = (findKey it.Key' s).bind kvLease := rfl

theorem leaseItem_eq_iff (it : LeaseItem) (k : GoString) : it = LeaseItem.mk k ↔ it.Key' = k := by
  cases it; simp

/-- **A state with no lease has the empty item map** (unit T3, L3b). -/
theorem leaseItemsOf_zero (s : List EtcdKv) (h : ∀ kv ∈ s, kv.lease = W64 0) :
    leaseItemsOf s = ∅ := by
  apply GMap.ext
  intro it
  rw [leaseItemsOf_lookup]
  cases hf : findKey it.Key' s with
  | none => rfl
  | some kv =>
    have hz := h kv (List.mem_of_find?_eq_some hf)
    simp [kvLease, hz]

/-- A put of `k` with lease `l` makes `k`'s entry `l`'s (none for `0`). -/
theorem leaseItemsOf_putKv {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64)
    (k v : GoString) (l : w64) (it : LeaseItem) :
    (leaseItemsOf (putKv r k v l s)).lookup it =
      if it.Key' = k then (if l = W64 0 then none else some l) else (leaseItemsOf s).lookup it := by
  rw [leaseItemsOf_lookup, leaseItemsOf_lookup]
  by_cases hk : it.Key' = k
  · rw [if_pos hk, hk]
    unfold putKv
    simp only
    rw [findKey_btInsert _ s hs]
    split
    · rename_i kv heq
      have hk' : kv.key = k := by simpa using List.find?_some heq
      by_cases hl : l = W64 0 <;> simp [hk', kvLease, hl]
    · by_cases hl : l = W64 0 <;> simp [kvLease, hl]
  · rw [if_neg hk, findKey_putKv_other hs r it.Key' k v l (Ne.symm hk)]

/-- A delete of `k` removes `k`'s entry. -/
theorem leaseItemsOf_del (s : List EtcdKv) (k : GoString) (it : LeaseItem) :
    (leaseItemsOf (s.filter fun x => !decide (x.key = k))).lookup it =
      if it.Key' = k then none else (leaseItemsOf s).lookup it := by
  rw [leaseItemsOf_lookup, leaseItemsOf_lookup, findKey_filter_ne]
  by_cases hk : it.Key' = k
  · simp [hk]
  · simp [hk, Ne.symm hk]

/-- No key's entry is `0` (a key without a lease has none). -/
theorem leaseItemsOf_ne_zero (s : List EtcdKv) (it : LeaseItem) :
    (leaseItemsOf s).lookup it ≠ some (W64 0) := by
  rw [leaseItemsOf_lookup]
  cases findKey it.Key' s with
  | none => simp
  | some kv => by_cases h : kv.lease = W64 0 <;> simp [kvLease, h]

/-- An entry read with default `0` (`GetLease`'s answer `l`) determines the entry. -/
theorem leaseItemsOf_getD (s : List EtcdKv) (it : LeaseItem) (l : w64)
    (h : ((leaseItemsOf s).lookup it).getD (W64 0) = l) :
    (leaseItemsOf s).lookup it = if l = W64 0 then none else some l := by
  have hnz := leaseItemsOf_ne_zero s it
  cases hl : (leaseItemsOf s).lookup it with
  | none => rw [hl] at h; simp at h; subst h; simp
  | some x =>
    rw [hl] at h hnz; simp at h; subst h
    have : x ≠ W64 0 := fun h => hnz (by rw [h])
    exact (if_neg this).symm

/-- **The item map of the write transaction's pending state** (`ilog` committed, `pend`
pending). -/
abbrev pendItems (ilog : Log) (pend : List Change) : GMap LeaseItem w64 :=
  leaseItemsOf (applyChanges (W64 ilog.length) (stateAfter ilog) pend)

/-- **A put's item map**: any map agreeing with the pending one off the key, and with the put's
lease (none for `0`) on it. -/
theorem pendItems_put (ilog : Log) (pend : List Change) (k v : GoString) (l : w64)
    (J : GMap LeaseItem w64)
    (hJ : ∀ it : LeaseItem, it.Key' ≠ k → J.lookup it = (pendItems ilog pend).lookup it)
    (hJk : J.lookup (LeaseItem.mk k) = if l = W64 0 then none else some l) :
    pendItems ilog (pend ++ [.put k v l]) = J := by
  apply GMap.ext
  intro it
  unfold pendItems
  rw [applyChanges_append_singleton]
  simp only [applyChange]
  rw [leaseItemsOf_putKv (applyChanges_sorted _ pend (stateAfter_sorted ilog))]
  by_cases hk : it.Key' = k
  · rw [if_pos hk, ← hJk, (leaseItem_eq_iff it k).2 hk]
  · rw [if_neg hk, hJ it hk]

/-- **A delete's item map**: any map agreeing with the pending one off the key, and none on
it. -/
theorem pendItems_del (ilog : Log) (pend : List Change) (k : GoString) (J : GMap LeaseItem w64)
    (hJ : ∀ it : LeaseItem, it.Key' ≠ k → J.lookup it = (pendItems ilog pend).lookup it)
    (hJk : J.lookup (LeaseItem.mk k) = none) :
    pendItems ilog (pend ++ [.del k]) = J := by
  apply GMap.ext
  intro it
  unfold pendItems
  rw [applyChanges_append_singleton]
  simp only [applyChange]
  rw [leaseItemsOf_del]
  by_cases hk : it.Key' = k
  · rw [if_pos hk, ← hJk, (leaseItem_eq_iff it k).2 hk]
  · rw [if_neg hk, hJ it hk]

/-- A key the index does not find at the pending revision has no entry. -/
theorem pendItems_absent (ilog : Log) (pend : List Change) (k : GoString)
    (hwf : LogWf (ilog ++ [pend])) (hlen : (ilog ++ [pend]).length < 2 ^ 63)
    (hcs : ∀ cs ∈ ilog ++ [pend], cs.length < 2 ^ 63)
    (hg : kiGet (kiOfKey (evsOf (ilog ++ [pend])) k) (W64 ilog.length) = none) :
    (pendItems ilog pend).lookup (LeaseItem.mk k) = none := by
  have hm := kiGet_indexOf (ilog ++ [pend]) hlen hcs hwf k ilog.length (by simp at hlen; omega)
  rw [idxGet_indexOf_bind, stateAt_pend, hg] at hm
  rw [leaseItemsOf_lookup]
  simp only
  rw [KvMatch_none_left hm]
  rfl

/-- In a sorted state, the key-values of key `k` are `k`'s one, if any. -/
theorem filter_key_sorted (k : GoString) :
    ∀ s : List EtcdKv, s.Pairwise etcdKvLess →
      (s.filter (fun v => decide (v.key = k))).map EtcdKv.key =
        if (findKey k s).isSome then [k] else []
  | [], _ => by simp [findKey]
  | v :: s, hs => by
    have ih := filter_key_sorted k s hs.of_cons
    rw [findKey_cons]
    by_cases hv : v.key = k
    · have hnone : s.filter (fun w => decide (w.key = k)) = [] := by
        apply List.filter_eq_nil_iff.2
        intro w hw hk
        have hlt := (List.pairwise_cons.1 hs).1 w hw
        unfold etcdKvLess at hlt
        rw [hv, of_decide_eq_true hk] at hlt
        exact go.goStringLt_irrefl _ hlt
      simp [hv, hnone]
    · rw [List.filter_cons_of_neg (by simpa using hv), ih]
      simp [hv]

/-- **The item map after deleting the keys `ks`**: none for them, the rest unchanged. -/
theorem leaseItemsOf_dels (r : w64) (ks : List GoString) :
    ∀ (s : List EtcdKv) (it : LeaseItem),
      (leaseItemsOf (applyChanges r s (ks.map Change.del))).lookup it =
        if it.Key' ∈ ks then none else (leaseItemsOf s).lookup it := by
  induction ks with
  | nil => intro s it; rfl
  | cons k ks ih =>
    intro s it
    have h : applyChanges r s ((k :: ks).map Change.del) =
        applyChanges r (applyChange r s (.del k)) (ks.map Change.del) := rfl
    rw [h, ih]
    simp only [applyChange]
    rw [leaseItemsOf_del]
    by_cases h1 : it.Key' = k <;> by_cases h2 : it.Key' ∈ ks <;> simp [h1, h2]

/-! ## A revocation's deletions (the lease-revoke plan, R1, 2026-10-31) -/

/-- **The keys a revocation of `id` deletes** at the state `s`: every key the item map puts on `id`
(none for `0`: a key with lease `0` has no item), in the state's (key) order. -/
def leaseDelKeys (s : List EtcdKv) (id : w64) : List GoString :=
  if id = W64 0 then [] else (s.filter (fun v => decide (v.lease = id))).map EtcdKv.key

/-- **A revocation's deletions**: `leaseDelKeys`'s, one delete each. -/
def leaseDels (s : List EtcdKv) (id : w64) : List Change := (leaseDelKeys s id).map Change.del

/-- In a sorted state, two key-values of one key are one. -/
theorem sorted_key_unique : ∀ {s : List EtcdKv}, s.Pairwise etcdKvLess →
    ∀ {v w : EtcdKv}, v ∈ s → w ∈ s → v.key = w.key → v = w
  | [], _, _, _, hv, _, _ => by cases hv
  | x :: s, hs, v, w, hv, hw, hk => by
    have hx := (List.pairwise_cons.1 hs).1
    rcases List.mem_cons.1 hv with rfl | hv' <;> rcases List.mem_cons.1 hw with rfl | hw'
    · rfl
    · have h := hx w hw'; unfold etcdKvLess at h; rw [hk] at h
      exact absurd h (go.goStringLt_irrefl _)
    · have h := hx v hv'; unfold etcdKvLess at h; rw [hk] at h
      exact absurd h (go.goStringLt_irrefl _)
    · exact sorted_key_unique hs.of_cons hv' hw' hk

/-- In a sorted state, `findKey` finds exactly the key-value of the key. -/
theorem findKey_iff_sorted {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (k : GoString)
    (v : EtcdKv) : findKey k s = some v ↔ v ∈ s ∧ v.key = k := by
  constructor
  · intro h; exact ⟨List.mem_of_find?_eq_some h, findKey_key h⟩
  · rintro ⟨hv, hk⟩
    cases hf : findKey k s with
    | none =>
      have := List.find?_eq_none.1 hf v hv
      simp [hk] at this
    | some w =>
      rw [sorted_key_unique hs (List.mem_of_find?_eq_some hf) hv
        ((findKey_key hf).trans hk.symm)]

/-- **A deleted key is one the item map put on `id`**, and every such key is deleted (a sorted
state). -/
theorem leaseDelKeys_mem {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (id : w64) (k : GoString) :
    k ∈ leaseDelKeys s id ↔ (leaseItemsOf s).lookup (LeaseItem.mk k) = some id := by
  rw [leaseItemsOf_lookup]
  simp only
  unfold leaseDelKeys
  by_cases h0 : id = W64 0
  · subst h0
    simp only [↓reduceIte, List.not_mem_nil, false_iff]
    intro h
    cases hf : findKey k s with
    | none => rw [hf] at h; cases h
    | some v =>
      rw [hf] at h
      simp only [Option.bind_some, kvLease] at h
      split at h
      · cases h
      · rename_i hne; exact hne (Option.some.inj h)
  · rw [if_neg h0]
    constructor
    · intro h
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
      obtain ⟨hvs, hl⟩ := List.mem_filter.1 hv
      have hl' : v.lease = id := of_decide_eq_true hl
      rw [(findKey_iff_sorted hs v.key v).2 ⟨hvs, rfl⟩]
      simp only [Option.bind_some, kvLease, hl']
      rw [if_neg h0]
    · intro h
      cases hf : findKey k s with
      | none => rw [hf] at h; cases h
      | some v =>
        rw [hf] at h
        simp only [Option.bind_some, kvLease] at h
        split at h
        · cases h
        · cases h
          obtain ⟨hvs, hk⟩ := (findKey_iff_sorted hs k v).1 hf
          exact List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hvs, by simp⟩, hk⟩

/-- `leaseDels`'s members: the deletes of `leaseDelKeys`'s. -/
theorem leaseDels_mem {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (id : w64) (c : Change) :
    c ∈ leaseDels s id ↔ ∃ k, c = .del k ∧ (leaseItemsOf s).lookup (LeaseItem.mk k) = some id := by
  unfold leaseDels
  constructor
  · intro h; obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h; exact ⟨k, rfl, (leaseDelKeys_mem hs id k).1 hk⟩
  · rintro ⟨k, rfl, hk⟩; exact List.mem_map.2 ⟨k, (leaseDelKeys_mem hs id k).2 hk, rfl⟩

/-- Every change of `leaseDels` is a delete. -/
theorem leaseDels_isDel (s : List EtcdKv) (id : w64) : ∀ c ∈ leaseDels s id, c.isDel = true := by
  intro c hc; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc; rfl

/-- The deleted keys are strictly increasing (a sorted state). -/
theorem leaseDelKeys_sorted {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (id : w64) :
    (leaseDelKeys s id).Pairwise go.GoStringLt := by
  unfold leaseDelKeys
  split
  · exact List.Pairwise.nil
  · exact List.pairwise_map.2 (hs.filter _)

/-- Two strictly increasing lists with the same members are equal. -/
theorem eq_of_lt_sorted_mem : ∀ {l₁ l₂ : List GoString}, l₁.Pairwise go.GoStringLt →
    l₂.Pairwise go.GoStringLt → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) (List.not_mem_nil)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    have ha := (List.pairwise_cons.1 h₁).1
    have hb := (List.pairwise_cons.1 h₂).1
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | e
      · exact e
      rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e' | e'
      · exact e'.symm
      exact absurd (ha b e') (go.goStringLt_asymm (hb a e))
    subst hab
    congr 1
    apply eq_of_lt_sorted_mem h₁.of_cons h₂.of_cons
    intro x
    constructor
    · intro hx
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (ha x hx) (go.goStringLt_irrefl _)
      · exact e
    · intro hx
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (hb x hx) (go.goStringLt_irrefl _)
      · exact e

/-- **The sorted keys of `id` are `leaseDelKeys`'s** (what `lessor.Revoke` deletes: its item set,
sorted): a list without duplicates, in Go's string order, of exactly the keys the item map puts on
`id`. -/
theorem leaseDelKeys_eq {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (id : w64)
    (ks : List GoString) (hnd : ks.Nodup)
    (hmem : ∀ k : GoString, k ∈ ks ↔ (leaseItemsOf s).lookup (LeaseItem.mk k) = some id)
    (hsort : ∀ (i j : Nat) (ki kj : GoString), ks[i]? = some ki → ks[j]? = some kj → i < j →
      go.GoStringLe ki kj) :
    ks = leaseDelKeys s id := by
  apply eq_of_lt_sorted_mem _ (leaseDelKeys_sorted hs id)
  · intro x; rw [hmem x, leaseDelKeys_mem hs id x]
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hle := hsort i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
    rcases hle with e | e
    · exact absurd e (List.pairwise_iff_getElem.1 hnd i j hi hj hij)
    · exact e

end items

end mvcc
end EtcdGrove
end Perennial
