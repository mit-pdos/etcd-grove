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
variable [FfiSyntax]

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

end items

end mvcc
end EtcdGrove
end Perennial
