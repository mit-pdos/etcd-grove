/-
**etcd's KV store at one revision, as a map** (D45, 2026-10-25): each key's record (`KVRec`: its
value, create and mod revisions, version and lease; `mvccpb.KeyValue` without the key), a finite
map from keys (`KVStore`). The client-visible state (`KVState`, `KVModelDefs.lean`) is one per
revision; the server's model of a revision is the sorted list `mvcc.stateAt` (`List EtcdKv`, keys
increasing), which `storeOf` reads as a map and `KVStore.kvs` lists back (`kvs_storeOf`: they are
inverse on sorted lists), so the range semantics stated over lists (`txn.srvRangeOk`,
`mvcc.findKey`, ...) apply to a store's `kvs`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **A key's record at a revision** (`mvccpb.KeyValue` without its key). -/
structure KVRec where
  createRev : w64
  modRev : w64
  version : w64
  value : GoString
  lease : w64
deriving DecidableEq

/-- The record of a key-value. -/
def KVRec.ofKv (kv : EtcdKv) : KVRec := ⟨kv.createRev, kv.modRev, kv.version, kv.value, kv.lease⟩

/-- The key-value of the key `k` with the record `r`. -/
def KVRec.toKv (k : GoString) (r : KVRec) : EtcdKv :=
  ⟨k, r.createRev, r.modRev, r.version, r.value, r.lease⟩

theorem KVRec.toKv_ofKv (kv : EtcdKv) : KVRec.toKv kv.key (KVRec.ofKv kv) = kv := rfl

instance KVRec.countable : Pos.Countable KVRec :=
  .ofInjective (fun r => Pos.Countable.encode (r.createRev, r.modRev, r.version, r.value, r.lease))
    (by
      rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ h
      have h := Pos.encode_inj h
      simp_all)

/-- **The store at a revision**: each key's record. -/
abbrev KVStore := GMap GoString KVRec

/-- **The store of a list of key-values** (each key's first: `mvcc.findKey`'s). -/
def storeOf (s : List EtcdKv) : KVStore :=
  ⟨fun k => (mvcc.findKey k s).map KVRec.ofKv,
   ⟨s.map EtcdKv.key, fun k h => by
      cases hf : mvcc.findKey k s with
      | none => simp [hf] at h
      | some kv =>
        have hm := List.mem_of_find?_eq_some hf
        have hk := List.find?_some hf
        simp only [decide_eq_true_eq] at hk
        exact List.mem_map.2 ⟨kv, hm, hk⟩⟩⟩

theorem storeOf_lookup (s : List EtcdKv) (k : GoString) :
    (storeOf s).lookup k = (mvcc.findKey k s).map KVRec.ofKv := rfl

/-! ### Listing a store, sorted by key -/

/-- Insert a key-value into a list sorted by key (replacing the key's, if any). -/
def sortedIns (x : EtcdKv) : List EtcdKv → List EtcdKv
  | [] => [x]
  | y :: ys =>
    if go.GoStringLt x.key y.key then x :: y :: ys
    else if x.key = y.key then x :: ys
    else y :: sortedIns x ys

theorem sortedIns_mem (x : EtcdKv) : ∀ (s : List EtcdKv) (z : EtcdKv), z ∈ sortedIns x s →
    z = x ∨ z ∈ s
  | [], z, h => by simp [sortedIns] at h; exact Or.inl h
  | y :: ys, z, h => by
    unfold sortedIns at h
    split at h
    · simpa using h
    · split at h
      · simp at h; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · simp only [List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (by simp [h])
        · rcases sortedIns_mem x ys z h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons_of_mem _ h')

/-- `findKey` on a cons. -/
theorem findKey_cons (k : GoString) (x : EtcdKv) (s : List EtcdKv) :
    mvcc.findKey k (x :: s) = if x.key = k then some x else mvcc.findKey k s := by
  unfold mvcc.findKey
  simp only [List.find?_cons]
  by_cases h : x.key = k <;> simp [h]

theorem findKey_key {k : GoString} {s : List EtcdKv} {kv : EtcdKv}
    (h : mvcc.findKey k s = some kv) : kv.key = k := by
  have := List.find?_some h; simpa using this

/-- `findKey` of a key other than the head's skips the head. -/
theorem findKey_tail_none_of_ne {k : GoString} {x : EtcdKv} {l : List EtcdKv}
    (h : ¬ x.key = k) : mvcc.findKey k (x :: l) = mvcc.findKey k l := by
  rw [findKey_cons, if_neg h]

/-- In a list sorted by key, nothing after the head has its key. -/
theorem findKey_tail_none (x : EtcdKv) (l : List EtcdKv) (hl : (x :: l).Pairwise etcdKvLess) :
    mvcc.findKey x.key l = none := by
  apply List.find?_eq_none.2
  intro z hz
  have := List.rel_of_pairwise_cons hl hz
  unfold etcdKvLess at this
  simp only [decide_eq_true_eq]
  intro hz'
  rw [hz'] at this
  exact go.goStringLt_irrefl _ this

theorem sortedIns_sorted (x : EtcdKv) : ∀ (s : List EtcdKv), s.Pairwise etcdKvLess →
    (sortedIns x s).Pairwise etcdKvLess
  | [], _ => by simp [sortedIns]
  | y :: ys, h => by
    unfold sortedIns
    split
    · rename_i hlt
      refine List.Pairwise.cons (fun z hz => ?_) h
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hlt
      · exact go.goStringLt_trans hlt (List.rel_of_pairwise_cons h hz)
    · split
      · rename_i _ heq
        refine List.Pairwise.cons (fun z hz => ?_) h.of_cons
        unfold etcdKvLess; rw [heq]; exact List.rel_of_pairwise_cons h hz
      · rename_i hlt hne
        have hyx : go.GoStringLt y.key x.key :=
          Classical.byContradiction fun hyx => hne (go.goStringLt_eq_of_not_lt hlt hyx)
        refine List.Pairwise.cons (fun z hz => ?_) (sortedIns_sorted x ys h.of_cons)
        rcases sortedIns_mem x ys z hz with rfl | hz
        · exact hyx
        · exact List.rel_of_pairwise_cons h hz

theorem findKey_sortedIns (x : EtcdKv) (k : GoString) : ∀ (s : List EtcdKv),
    s.Pairwise etcdKvLess →
    mvcc.findKey k (sortedIns x s) = if x.key = k then some x else mvcc.findKey k s
  | [], _ => by unfold sortedIns; rw [findKey_cons]
  | y :: ys, h => by
    unfold sortedIns
    split
    · rw [findKey_cons]
    · split
      · rename_i _ heq
        rw [findKey_cons, findKey_cons]
        by_cases hk : x.key = k
        · simp [hk]
        · simp [hk, ← heq]
      · rename_i hlt hne
        rw [findKey_cons, findKey_cons, findKey_sortedIns x k ys h.of_cons]
        by_cases hy : y.key = k
        · have hxk : x.key ≠ k := fun hx => hne (hx.trans hy.symm)
          simp [hy, hxk]
        · simp [hy]

/-- **A store's key-values, sorted by key.** -/
def KVStore.kvs (m : KVStore) : List EtcdKv :=
  m.toList.foldr (fun p acc => sortedIns (KVRec.toKv p.1 p.2) acc) []

theorem foldr_sortedIns_sorted : ∀ (l : List (GoString × KVRec)),
    (l.foldr (fun p acc => sortedIns (KVRec.toKv p.1 p.2) acc) []).Pairwise etcdKvLess
  | [] => List.Pairwise.nil
  | p :: l => sortedIns_sorted _ _ (foldr_sortedIns_sorted l)

theorem KVStore.kvs_sorted (m : KVStore) : m.kvs.Pairwise etcdKvLess :=
  foldr_sortedIns_sorted m.toList

theorem foldr_sortedIns_find (k : GoString) : ∀ (l : List (GoString × KVRec)),
    (l.map Prod.fst).Nodup →
    mvcc.findKey k (l.foldr (fun p acc => sortedIns (KVRec.toKv p.1 p.2) acc) []) =
      ((l.find? (fun p => decide (p.1 = k))).map fun p => KVRec.toKv p.1 p.2)
  | [], _ => rfl
  | p :: l, hnd => by
    simp only [List.foldr_cons]
    rw [findKey_sortedIns _ _ _ (foldr_sortedIns_sorted l)]
    simp only [List.map_cons] at hnd
    by_cases h : p.1 = k
    · simp [KVRec.toKv, h, List.find?_cons]
    · rw [foldr_sortedIns_find k l (List.nodup_cons.1 hnd).2]
      simp [KVRec.toKv, h, List.find?_cons]

/-- **Listing a store reads its bindings back.** -/
theorem storeOf_kvs (m : KVStore) : storeOf m.kvs = m := by
  apply GMap.ext
  intro k
  rw [storeOf_lookup]
  unfold KVStore.kvs
  rw [foldr_sortedIns_find k _ (GMap.toList_keys_nodup m)]
  cases hm : m.lookup k with
  | none =>
    cases hf : m.toList.find? (fun p => decide (p.1 = k)) with
    | none => rfl
    | some p =>
      have hp := List.mem_of_find?_eq_some hf
      have hk := List.find?_some hf
      simp only [decide_eq_true_eq] at hk
      have := (GMap.mem_toList m p.1 p.2).1 hp
      rw [hk] at this
      exact absurd (hm.symm.trans this) (by simp)
  | some v =>
    have hmem := (GMap.mem_toList m k v).2 hm
    cases hf : m.toList.find? (fun p => decide (p.1 = k)) with
    | none =>
      have := List.find?_eq_none.1 hf (k, v) hmem
      simp at this
    | some p =>
      have hp := List.mem_of_find?_eq_some hf
      have hk := List.find?_some hf
      simp only [decide_eq_true_eq] at hk
      have hpv := (GMap.mem_toList m p.1 p.2).1 hp
      rw [hk, hm] at hpv
      cases hpv
      obtain ⟨p1, p2⟩ := p
      simp only at hk
      subst hk
      rfl

/-- Two sorted lists with the same key-value at every key are equal. -/
theorem sorted_ext : ∀ (s t : List EtcdKv), s.Pairwise etcdKvLess → t.Pairwise etcdKvLess →
    (∀ k, mvcc.findKey k s = mvcc.findKey k t) → s = t
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by
    have := h y.key; rw [findKey_cons, if_pos rfl] at this; cases this
  | x :: _, [], _, _, h => by
    have := h x.key; rw [findKey_cons, if_pos rfl] at this; cases this
  | x :: xs, y :: ys, hs, ht, h => by
    have hxy : x = y := by
      have hx := h x.key
      have hy := h y.key
      rw [findKey_cons, findKey_cons, if_pos rfl] at hx
      rw [findKey_cons, findKey_cons, if_pos rfl] at hy
      by_cases e : y.key = x.key
      · rw [if_pos e] at hx; exact Option.some.inj hx
      · rw [if_neg e] at hx
        rw [if_neg (Ne.symm e)] at hy
        -- `x` is in `ys` and `y` in `xs`: each key below the other
        have hx' := List.mem_of_find?_eq_some hx.symm
        have hy' := List.mem_of_find?_eq_some hy
        have hkx := findKey_key hx.symm
        have hky := findKey_key hy
        have h1 := List.rel_of_pairwise_cons ht hx'
        have h2 := List.rel_of_pairwise_cons hs hy'
        unfold etcdKvLess at h1 h2
        rw [hkx] at h1; rw [hky] at h2
        exact absurd (go.goStringLt_trans h1 h2) (go.goStringLt_irrefl _)
    subst hxy
    congr 1
    refine sorted_ext xs ys hs.of_cons ht.of_cons fun k => ?_
    have hk := h k
    rw [findKey_cons, findKey_cons] at hk
    by_cases e : x.key = k
    · subst e
      rw [findKey_tail_none x xs hs, findKey_tail_none x ys ht]
    · rw [if_neg e, if_neg e] at hk
      exact hk

/-- **A sorted list is its store's listing.** -/
theorem kvs_storeOf (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) : (storeOf s).kvs = s := by
  refine sorted_ext _ _ (KVStore.kvs_sorted _) hs fun k => ?_
  have h := congrArg (fun m : KVStore => m.lookup k) (storeOf_kvs (storeOf s))
  simp only [storeOf_lookup] at h
  -- the key-values at `k` have the key `k`, so their records determine them
  have hkey : ∀ (l : List EtcdKv) (kv : EtcdKv), mvcc.findKey k l = some kv → kv.key = k :=
    fun _ _ hf => findKey_key hf
  cases h1 : mvcc.findKey k (storeOf s).kvs with
  | none => rw [h1] at h; cases h2 : mvcc.findKey k s <;> rw [h2] at h <;> simp_all
  | some a =>
    cases h2 : mvcc.findKey k s with
    | none => rw [h1, h2] at h; simp at h
    | some b =>
      rw [h1, h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have ha := hkey _ _ h1
      have hb := hkey _ _ h2
      rw [← KVRec.toKv_ofKv a, ← KVRec.toKv_ofKv b, ha, hb, h]

/-- **A key's key-value in a store's listing is its binding.** -/
theorem findKey_kvs (m : KVStore) (k : GoString) :
    mvcc.findKey k m.kvs = (m.lookup k).map (KVRec.toKv k) := by
  have h := congrArg (fun m' : KVStore => m'.lookup k) (storeOf_kvs m)
  simp only [storeOf_lookup] at h
  rw [← h]
  cases hf : mvcc.findKey k m.kvs with
  | none => rfl
  | some kv =>
    simp only [Option.map_some, Option.some.injEq]
    rw [← findKey_key hf, KVRec.toKv_ofKv]

end EtcdGrove
end Perennial
