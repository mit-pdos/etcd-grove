/-
Pure lemmas about freelist states (`Model.lean`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- The pending entry of `t` (empty if none). -/
def FLState.pendingOf (σ : FLState) (t : w64) : Pending :=
  (σ.pending !! t).getD ⟨[], [], 0⟩

/-- The pending ids, gathered in the order of any list of the pending transactions (as a
`range` over the map visits them), are the pending ids, up to order. -/
theorem pendingIds_perm_keys (σ : FLState) (keys : List w64)
    (hk : ∀ k, k ∈ keys ↔ (σ.pending !! k).isSome) (hnd : keys.Nodup) :
    (keys.flatMap (fun t => (σ.pendingOf t).ids)).Perm σ.pendingIds := by
  have hperm : (keys.map (fun t => (t, σ.pendingOf t))).Perm σ.pending.toList := by
    rw [List.perm_ext_iff_of_nodup]
    · intro ⟨k, v⟩
      rw [GMap.mem_toList]
      simp only [List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨t, ht, rfl, rfl⟩
        have := (hk t).1 ht
        unfold FLState.pendingOf
        cases h : σ.pending !! t with
        | none => simp [h] at this
        | some p => rfl
      · intro h
        refine ⟨k, (hk k).2 (by simp [h]), rfl, ?_⟩
        simp [FLState.pendingOf, h]
    · exact List.pairwise_map.2 (hnd.imp fun h e => h (Prod.mk.inj e).1)
    · exact List.Pairwise.of_map Prod.fst (fun _ _ h e => h (congrArg Prod.fst e))
        (GMap.toList_keys_nodup _)
  have := hperm.flatMap_right (fun kv => kv.2.ids)
  simpa [List.flatMap_map, FLState.pendingIds] using this

/-- The number of pending pages, summed in the order of any list of the pending
transactions. -/
theorem pendingCount_keys (σ : FLState) (keys : List w64)
    (hk : ∀ k, k ∈ keys ↔ (σ.pending !! k).isSome) (hnd : keys.Nodup) :
    (keys.map (fun t => (σ.pendingOf t).ids.length)).sum = σ.pendingCount := by
  rw [FLState.pendingCount, ← (pendingIds_perm_keys σ keys hk hnd).length_eq]
  simp [List.length_flatMap]

/-- In a list without duplicates, element `n` is not among the first `n`. -/
theorem not_mem_take_of_nodup {α : Type} {l : List α} (h : l.Nodup) {n : Nat} {e : α}
    (he : l[n]? = some e) : e ∉ l.take n := by
  intro hm
  have hd : e ∈ l.drop n := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by simp [List.getElem?_drop, he]⟩
  rw [← List.take_append_drop n l] at h
  exact (List.nodup_append.1 h).2.2 e hm e hd rfl

/-- In a list without duplicates, distinct positions hold distinct elements. -/
theorem nodup_getElem?_ne {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {x y : α}
    (hij : i < j) (hx : l[i]? = some x) (hy : l[j]? = some y) : x ≠ y := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hy
  exact List.pairwise_iff_getElem.1 (List.nodup_iff_pairwise_ne.1 h) i j hi hj hij

/-- Sorted page ids without duplicates increase. -/
theorem pgidsIncr_of_sorted_nodup {l : List w64} (hs : PgidsSorted l) (hn : l.Nodup) :
    PgidsIncr l :=
  (hs.and (List.nodup_iff_pairwise_ne.1 hn)).imp fun ⟨h1, h2⟩ =>
    Int.lt_iff_le_and_ne.2 ⟨h1, fun h => h2 (by word)⟩

/-- Increasing page ids are sorted. -/
theorem pgidsSorted_of_incr {l : List w64} (h : PgidsIncr l) : PgidsSorted l :=
  h.imp fun h => Int.le_of_lt h

/-- Allocating keeps the state well-formed. -/
theorem allocate_WF {σ : FLState} (h : σ.WF) (txid r : w64) (n : Nat) :
    (σ.allocate txid r n).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hsub : (σ.allocate txid r n).allIds.Sublist σ.allIds := by
    unfold FLState.allIds FLState.allocate FLState.pendingIds
    exact List.Sublist.append (by apply List.filter_sublist) (List.Sublist.refl _)
  have hfs : (σ.allocate txid r n).free.Sublist σ.free := by
    unfold FLState.allocate; apply List.filter_sublist
  refine ⟨hsub.nodup h1, fun id hid => h2 id (hsub.subset hid), List.Pairwise.sublist hfs h3,
    by have := hsub.length_le; omega, h5⟩

/-- The cache, its entries of the allocated ids deleted, is that of the state after the
allocation. -/
theorem allocate_cacheOK {σ : FLState} {c c' : GMap w64 Unit} {txid r : w64} {n : Nat}
    (hwf : σ.WF) (hc : cacheOK c σ) (hcan : σ.canAllocate r n)
    (hc' : ∀ x, (c' !! x).isSome ↔ (c !! x).isSome ∧ ¬ inRun r n x) :
    cacheOK c' (σ.allocate txid r n) := by
  intro x
  rw [hc' x, hc x]
  unfold FLState.cached FLState.allIds FLState.allocate FLState.pendingIds
  simp only [List.mem_append, List.mem_filter, decide_eq_true_iff]
  constructor
  · rintro ⟨h | h, hn⟩
    · exact Or.inl ⟨h, hn⟩
    · exact Or.inr h
  · rintro (⟨h, hn⟩ | h)
    · exact ⟨Or.inl h, hn⟩
    · refine ⟨Or.inr h, fun hr => ?_⟩
      exact (List.nodup_append.1 hwf.1).2.2 x (hcan.2 x hr) x h rfl

/-- `l[k] = l[last]; l = l[:last]`, at the first `x` of `l` (`RemoveReadonlyTXID`): `l`
without that `x`, up to order. -/
theorem swapRemove_perm {l : List w64} {k : Nat} {x : w64} (hk : l[k]? = some x)
    (hfirst : ∀ j < k, l[j]? ≠ some x) :
    ((l.set k (l.getD (l.length - 1) 0)).take (l.length - 1)).Perm (l.erase x) := by
  have hkl : k < l.length := (List.getElem?_eq_some_iff.1 hk).1
  have hA : x ∉ l.take k := by
    intro hm
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hm
    simp only [List.length_take] at hj
    apply hfirst j (by omega)
    rw [List.getElem?_eq_getElem (by omega)]
    simp only [List.getElem_take] at e
    rw [e]
  have hdec : l = l.take k ++ x :: l.drop (k + 1) := by
    conv => lhs; rw [← List.take_append_drop k l]
    congr 1
    rw [List.drop_eq_getElem_cons hkl]
    congr 1
    exact (List.getElem?_eq_some_iff.1 hk).2
  generalize hAdef : l.take k = A at hA hdec
  generalize hBdef : l.drop (k + 1) = B at hdec
  have hAl : A.length = k := by rw [← hAdef, List.length_take]; omega
  subst hdec
  rw [List.erase_append_right _ hA, List.erase_cons_head]
  rcases List.eq_nil_or_concat B with rfl | ⟨B', y, rfl⟩
  · simp [hAl, List.set_append_right, List.getD_eq_getElem?_getD]
  · have hgl : (A ++ x :: (B' ++ [y])).getD ((A ++ x :: (B' ++ [y])).length - 1) 0 = y := by
      simp [List.getD_eq_getElem?_getD]
    simp only [List.concat_eq_append] at *
    rw [hgl, ← hAl, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
    rw [show (A ++ x :: (B' ++ [y])).length - 1 = (A ++ y :: B').length by simp,
      show A ++ y :: (B' ++ [y]) = (A ++ y :: B') ++ [y] by simp, List.take_left]
    exact List.Perm.append_left A (List.perm_append_singleton y B').symm

/-- A list of distinct keys with their values is the map's bindings, up to order. -/
theorem toList_perm_of {V : Type} {m : GMap w64 V} {l : List (w64 × V)}
    (hnd : (l.map Prod.fst).Nodup) (h : ∀ k v, (k, v) ∈ l ↔ m !! k = some v) :
    l.Perm m.toList := by
  rw [List.perm_ext_iff_of_nodup]
  · intro ⟨k, v⟩; rw [GMap.mem_toList]; exact h k v
  · exact List.Pairwise.of_map Prod.fst (fun _ _ h e => h (congrArg Prod.fst e)) hnd
  · exact List.Pairwise.of_map Prod.fst (fun _ _ h e => h (congrArg Prod.fst e))
      (GMap.toList_keys_nodup _)

/-- The bindings of `m` with `k ↦ v`: that one and those of the others. -/
theorem toList_insert_perm {V : Type} (m : GMap w64 V) (k : w64) (v : V) :
    (<[k := v]> m).toList.Perm ((k, v) :: (GMap.delete k m).toList) := by
  refine (toList_perm_of ?_ ?_).symm
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, GMap.toList_keys_nodup _⟩
    obtain ⟨⟨k', v'⟩, hkv, rfl⟩ := List.mem_map.1 hm
    rw [GMap.mem_toList, GMap.lookup_delete] at hkv; cases hkv
  · intro k' v'
    simp only [List.mem_cons, Prod.mk.injEq, GMap.mem_toList, GMap.lookup_delete_iff]
    by_cases hk : k = k'
    · subst hk; simp [GMap.lookup_insert]; exact eq_comm
    · simp [hk, GMap.lookup_insert_ne _ _ hk, Ne.symm hk]

/-- The bindings of `m`, which binds `k` to `v`: that one and those of the others. -/
theorem toList_lookup_perm {V : Type} {m : GMap w64 V} {k : w64} {v : V} (h : m !! k = some v) :
    m.toList.Perm ((k, v) :: (GMap.delete k m).toList) := by
  have : <[k := v]> m = m := GMap.insert_id m k v h
  rw [← this]
  have h2 : GMap.delete k (<[k := v]> m) = GMap.delete k m := by
    apply GMap.map_eq; intro k'; simp only [GMap.lookup_delete_iff]
    split
    · rfl
    · rename_i hk; exact GMap.lookup_insert_ne _ _ hk
  rw [h2, this]
  have := toList_insert_perm m k v
  rwa [GMap.insert_id m k v h] at this

/-- The ids of the pending entries of `m`. -/
def flatIds (m : GMap w64 Pending) : List w64 := m.toList.flatMap (fun kv => kv.2.ids)

theorem pendingIds_eq (σ : FLState) : σ.pendingIds = flatIds σ.pending := rfl

theorem flatIds_insert (m : GMap w64 Pending) (t : w64) (pd : Pending) :
    (flatIds (<[t := pd]> m)).Perm (pd.ids ++ flatIds (GMap.delete t m)) := by
  have := (toList_insert_perm m t pd).flatMap_right (fun kv => kv.2.ids)
  simpa [flatIds] using this

theorem flatIds_lookup {m : GMap w64 Pending} {t : w64} {pd : Pending} (h : m !! t = some pd) :
    (flatIds m).Perm (pd.ids ++ flatIds (GMap.delete t m)) := by
  have := (toList_lookup_perm h).flatMap_right (fun kv => kv.2.ids)
  simpa [flatIds] using this

theorem mem_flatIds (m : GMap w64 Pending) (x : w64) :
    x ∈ flatIds m ↔ ∃ t pd, m !! t = some pd ∧ x ∈ pd.ids := by
  simp only [flatIds, List.mem_flatMap, Prod.exists, GMap.mem_toList]

theorem delete_of_none {V : Type} {m : GMap w64 V} {k : w64} (h : m !! k = none) :
    GMap.delete k m = m := by
  apply GMap.map_eq; intro k'; simp only [GMap.lookup_delete_iff]
  split
  · rename_i hk; subst hk; exact h.symm
  · rfl

theorem runIds_succ (id : w64) (m : Nat) : runIds id (m + 1) = runIds id m ++ [id + W64 (m : Int)] := by
  simp [runIds, List.range_succ]

theorem runIds_length (id : w64) (n : Nat) : (runIds id n).length = n := by simp [runIds]

/-- Without wrapping around, the run's ids are the numbers from `id` on. -/
theorem mem_runIds {id x : w64} {n : Nat} (h : uint.Z id + n ≤ 2 ^ 64) :
    x ∈ runIds id n ↔ inRun id n x := by
  simp only [runIds, List.mem_map, List.mem_range, inRun]
  constructor
  · rintro ⟨j, hj, rfl⟩
    constructor <;> word
  · rintro ⟨h1, h2⟩
    refine ⟨(uint.Z x - uint.Z id).toNat, by omega, ?_⟩
    word

theorem runIds_nodup {id : w64} {n : Nat} (h : uint.Z id + n ≤ 2 ^ 64) : (runIds id n).Nodup := by
  unfold runIds
  rw [List.Nodup, List.pairwise_map]
  refine List.nodup_range.imp_of_mem (fun {a b} ha hb hne e => hne ?_)
  simp only [List.mem_range] at ha hb
  have : uint.Z (id + W64 (a : Int)) = uint.Z (id + W64 (b : Int)) := by rw [e]
  have h1 : uint.Z (id + W64 (a : Int)) = uint.Z id + a := by word
  have h2 : uint.Z (id + W64 (b : Int)) = uint.Z id + b := by word
  omega

/-- The pending ids after `Free`: those before and the run. -/
theorem pendingIds_freePages (σ : FLState) (txid id : w64) (n : Nat) :
    (σ.freePages txid id n).pendingIds.Perm (σ.pendingIds ++ runIds id n) := by
  rw [pendingIds_eq, pendingIds_eq]
  unfold FLState.freePages
  simp only
  refine (flatIds_insert _ _ _).trans ?_
  rcases h : σ.pending !! txid with _ | pd
  · simp only [Option.getD_none, List.nil_append, delete_of_none h]
    exact List.perm_append_comm
  · simp only [Option.getD_some]
    refine List.Perm.trans ?_ (List.Perm.append_right _ (flatIds_lookup h).symm)
    simp only [List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

/-- `Free` keeps the state well-formed, and caches exactly the run more. -/
theorem freePages_ok {σ : FLState} {txid id : w64} {n : Nat} (hwf : σ.WF)
    (hcan : σ.canFree txid id n) :
    (∀ x, (σ.freePages txid id n).cached x ↔ σ.cached x ∨ x ∈ runIds id n) ∧
    (σ.freePages txid id n).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  obtain ⟨c1, c2, c3, c4, c5⟩ := hcan
  have hp := pendingIds_freePages σ txid id n
  have hall : (σ.freePages txid id n).allIds.Perm (σ.allIds ++ runIds id n) := by
    unfold FLState.allIds
    rw [List.append_assoc]
    exact List.Perm.append_left _ hp
  have hrun := runIds_nodup (id := id) (n := n) (by omega)
  refine ⟨fun x => ?_, ?_, ?_, h3, ?_, ?_⟩
  · unfold FLState.cached; rw [hall.mem_iff, List.mem_append]
  · rw [hall.nodup_iff, List.nodup_append]
    exact ⟨h1, hrun, fun a ha b hb e => c3 b hb (e ▸ ha)⟩
  · intro x hx
    rcases List.mem_append.1 (hall.mem_iff.1 hx) with hx | hx
    · exact h2 x hx
    · have := ((mem_runIds (id := id) (by omega)).1 hx).1; omega
  · rw [hall.length_eq, List.length_append, runIds_length]; omega
  · intro t p hp'
    unfold FLState.freePages at hp'
    simp only at hp'
    by_cases ht : txid = t
    · subst ht
      rw [GMap.lookup_insert] at hp'
      cases hp'
      simp only [List.length_append, runIds_length, List.length_replicate]
      rcases h : σ.pending !! txid with _ | pd
      · simp
      · simp [h5 txid pd h]
    · rw [GMap.lookup_insert_ne _ _ ht] at hp'
      exact h5 t p hp'

/-- Increasing ids are distinct. -/
theorem PgidsIncr.nodup {l : List w64} (h : PgidsIncr l) : l.Nodup :=
  List.nodup_iff_pairwise_ne.2 (h.imp fun h e => by rw [e] at h; exact Int.lt_irrefl _ h)

/-- The state whose free ids are the increasing ids `xs` (at least 2), but the pending ones
(`NoSyncReload`), is well-formed. -/
theorem reload_WF {σ : FLState} {xs : List w64} (hwf : σ.WF) (hinc : PgidsIncr xs)
    (hge : ∀ x ∈ xs, 2 ≤ uint.Z x) (hlen : xs.length + σ.pendingCount < 2 ^ 63) :
    ({ σ with free := xs.filter (fun x => decide (x ∉ σ.pendingIds)) } : FLState).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  have hfs : (xs.filter (fun x => decide (x ∉ σ.pendingIds))).Sublist xs := by
    apply List.filter_sublist
  unfold FLState.allIds at h1 h2
  refine ⟨?_, ?_, List.Pairwise.sublist hfs hinc, ?_, h5⟩
  · show (_ ++ σ.pendingIds).Nodup
    rw [List.nodup_append]
    refine ⟨hfs.nodup hinc.nodup, (List.nodup_append.1 h1).2.1, fun a ha b hb e => ?_⟩
    subst e
    simp only [List.mem_filter, decide_eq_true_iff] at ha
    exact ha.2 hb
  · intro id hid
    rcases List.mem_append.1 hid with h | h
    · exact hge id (hfs.subset h)
    · exact h2 id (List.mem_append_right _ h)
  · show (_ ++ σ.pendingIds).length < _
    have := hfs.length_le
    unfold FLState.pendingCount at hlen
    rw [List.length_append]; simp only; omega

end bbolt
end EtcdGrove
end Perennial
