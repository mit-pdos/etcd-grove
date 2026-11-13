/-
Pure lemmas about the freelist's state `FLPg` (`Model/FL.lean`), for U2's proofs of the freelist
interface (`notes/bbolt-proof-plan.md`): ported from the old proof's
`old/bbolt/.../internal/freelist/Lemmas.lean` (over `FLState`, with `uint.Z`; here over `FLPg`,
with `toNat`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.FL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


/-- The pending entry of `t` (empty if none). -/
def FLPg.pendingOf (fl : FLPg) (t : w64) : Pending :=
  (fl.pending !! t).getD ⟨[], [], 0⟩

/-- The ids of the pending entries of `m`. -/
def flatIds (m : GMap w64 Pending) : List w64 := m.toList.flatMap (fun kv => kv.2.ids)

theorem pendingIds_eq (fl : FLPg) : fl.pendingIds = flatIds fl.pending := rfl

/-- A list of distinct keys with their values is the map's bindings, up to order. -/
theorem toList_perm_of {V : Type} {m : GMap w64 V} {l : List (w64 × V)}
    (hnd : (l.map Prod.fst).Nodup) (h : ∀ k v, (k, v) ∈ l ↔ m !! k = some v) :
    l.Perm m.toList := by
  rw [List.perm_ext_iff_of_nodup]
  · intro ⟨k, v⟩; rw [GMap.mem_toList]; exact h k v
  · exact List.Pairwise.of_map Prod.fst (fun _ _ h e => h (congrArg Prod.fst e)) hnd
  · exact List.Pairwise.of_map Prod.fst (fun _ _ h e => h (congrArg Prod.fst e))
      (GMap.toList_keys_nodup _)

/-- The ids of the entries of a map, gathered in the order of any list of its keys (as a
`range` over the map visits them), are its ids, up to order. -/
theorem flatIds_keys (m : GMap w64 Pending) (keys : List w64)
    (hk : ∀ k, k ∈ keys ↔ (m !! k).isSome) (hnd : keys.Nodup) :
    (keys.flatMap (fun t => ((m !! t).getD ⟨[], [], 0⟩).ids)).Perm (flatIds m) := by
  have hperm : (keys.map (fun t => (t, (m !! t).getD ⟨[], [], 0⟩))).Perm m.toList := by
    refine toList_perm_of ?_ ?_
    · rw [List.map_map]; simpa [Function.comp_def] using hnd
    · intro k v
      simp only [List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨t, ht, rfl, rfl⟩
        have := (hk t).1 ht
        cases h : m !! t with
        | none => simp [h] at this
        | some p => rfl
      · intro h
        exact ⟨k, (hk k).2 (by simp [h]), rfl, by simp [h]⟩
  have := hperm.flatMap_right (fun kv => kv.2.ids)
  simpa [List.flatMap_map, flatIds] using this

theorem pendingIds_perm_keys (fl : FLPg) (keys : List w64)
    (hk : ∀ k, k ∈ keys ↔ (fl.pending !! k).isSome) (hnd : keys.Nodup) :
    (keys.flatMap (fun t => (fl.pendingOf t).ids)).Perm fl.pendingIds :=
  flatIds_keys fl.pending keys hk hnd

/-- The number of pending pages, summed in the order of any list of the pending
transactions. -/
theorem pendingCount_keys (fl : FLPg) (keys : List w64)
    (hk : ∀ k, k ∈ keys ↔ (fl.pending !! k).isSome) (hnd : keys.Nodup) :
    (keys.map (fun t => (fl.pendingOf t).ids.length)).sum = fl.pendingIds.length := by
  rw [← (pendingIds_perm_keys fl keys hk hnd).length_eq]
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

/-- Increasing ids are distinct. -/
theorem PgidsIncr.nodup {l : List w64} (h : PgidsIncr l) : l.Nodup :=
  List.nodup_iff_pairwise_ne.2 (h.imp fun h e => by rw [e] at h; exact Nat.lt_irrefl _ h)

/-- `sortPgids` is a permutation. -/
theorem sortPgids_perm (l : List w64) : (sortPgids l).Perm l := List.mergeSort_perm _ _

/-- `sortPgids` sorts. -/
theorem sortPgids_sorted (l : List w64) :
    (sortPgids l).Pairwise (fun x y : w64 => x.toNat ≤ y.toNat) := by
  have := List.pairwise_mergeSort (le := fun x y : w64 => decide (x.toNat ≤ y.toNat))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [decide_eq_true_eq, Bool.or_eq_true]; omega) l
  exact this.imp (fun h => by simpa using h)

/-- `sortPgids` of distinct ids increases. -/
theorem sortPgids_incr {l : List w64} (h : l.Nodup) : PgidsIncr (sortPgids l) := by
  have hn : (sortPgids l).Nodup := (sortPgids_perm l).nodup_iff.2 h
  exact ((sortPgids_sorted l).and (List.nodup_iff_pairwise_ne.1 hn)).imp fun ⟨h1, h2⟩ =>
    Nat.lt_of_le_of_ne h1 (fun e => h2 (by
      apply BitVec.eq_of_toNat_eq; exact e))

/-- A sorted permutation of `l` is `sortPgids l`. -/
theorem sortPgids_eq_of_sorted {l ys : List w64}
    (hs : ys.Pairwise (fun x y : w64 => x.toNat ≤ y.toNat)) (hp : ys.Perm l) :
    sortPgids l = ys := by
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ h1 h2 => BitVec.eq_of_toNat_eq (Nat.le_antisymm h1 h2))
    (sortPgids_sorted l) hs ((sortPgids_perm l).trans hp.symm)

/-- An increasing list is its own sort. -/
theorem sortPgids_of_incr {l : List w64} (h : PgidsIncr l) : sortPgids l = l :=
  sortPgids_eq_of_sorted (h.imp fun h => Nat.le_of_lt h) (List.Perm.refl _)

/-- Two increasing lists with the same elements are equal. -/
theorem PgidsIncr.ext {l1 l2 : List w64} (h1 : PgidsIncr l1) (h2 : PgidsIncr l2)
    (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 := by
  have hp : l1.Perm l2 := (List.perm_ext_iff_of_nodup h1.nodup h2.nodup).2 h
  rw [← sortPgids_eq_of_sorted (h1.imp fun h => Nat.le_of_lt h) hp, sortPgids_of_incr h2]

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
    · subst hk; simp; exact eq_comm
    · simp [hk, Ne.symm hk]

/-- The bindings of `m`, which binds `k` to `v`: that one and those of the others. -/
theorem toList_lookup_perm_w64 {V : Type} {m : GMap w64 V} {k : w64} {v : V} (h : m !! k = some v) :
    m.toList.Perm ((k, v) :: (GMap.delete k m).toList) := by
  have h2 : GMap.delete k (<[k := v]> m) = GMap.delete k m := by
    apply GMap.map_eq; intro k'; simp only [GMap.lookup_delete_iff]
    split
    · rfl
    · rename_i hk; exact GMap.lookup_insert_ne _ _ hk
  have := toList_insert_perm m k v
  rwa [GMap.insert_id m k v h] at this

theorem flatIds_insert (m : GMap w64 Pending) (t : w64) (pd : Pending) :
    (flatIds (<[t := pd]> m)).Perm (pd.ids ++ flatIds (GMap.delete t m)) := by
  have := (toList_insert_perm m t pd).flatMap_right (fun kv => kv.2.ids)
  simpa [flatIds] using this

theorem flatIds_lookup {m : GMap w64 Pending} {t : w64} {pd : Pending} (h : m !! t = some pd) :
    (flatIds m).Perm (pd.ids ++ flatIds (GMap.delete t m)) := by
  have := (toList_lookup_perm_w64 h).flatMap_right (fun kv => kv.2.ids)
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

theorem runIds_succ (id : w64) (m : Nat) :
    runIds id (m + 1) = runIds id m ++ [id + W64 (m : Int)] := by
  simp [runIds, List.range_succ]

theorem runIds_length (id : w64) (n : Nat) : (runIds id n).length = n := by simp [runIds]

/-- Without wrapping around, the run's ids are the numbers from `id` on. -/
theorem mem_runIds {id x : w64} {n : Nat} (h : id.toNat + n ≤ 2 ^ 64) :
    x ∈ runIds id n ↔ inRun id n x := by
  simp only [runIds, List.mem_map, List.mem_range, inRun]
  constructor
  · rintro ⟨j, hj, rfl⟩
    constructor <;> word
  · rintro ⟨h1, h2⟩
    refine ⟨x.toNat - id.toNat, by omega, ?_⟩
    word

theorem runIds_nodup {id : w64} {n : Nat} (h : id.toNat + n ≤ 2 ^ 64) : (runIds id n).Nodup := by
  unfold runIds
  rw [List.Nodup, List.pairwise_map]
  refine List.nodup_range.imp_of_mem (fun {a b} ha hb hne e => hne ?_)
  simp only [List.mem_range] at ha hb
  have : (id + W64 (a : Int)).toNat = (id + W64 (b : Int)).toNat := by rw [e]
  have h1 : (id + W64 (a : Int)).toNat = id.toNat + a := by word
  have h2 : (id + W64 (b : Int)).toNat = id.toNat + b := by word
  omega

/-- The pending ids after `Free`: those before and the run. -/
theorem pendingIds_freePages (fl : FLPg) (txid id : w64) (n : Nat) :
    (fl.freePages txid id n).pendingIds.Perm (fl.pendingIds ++ runIds id n) := by
  rw [pendingIds_eq, pendingIds_eq]
  unfold FLPg.freePages
  simp only
  refine (flatIds_insert _ _ _).trans ?_
  rcases h : fl.pending !! txid with _ | pd
  · simp only [Option.getD_none, List.nil_append, delete_of_none h]
    exact List.perm_append_comm
  · simp only [Option.getD_some]
    refine List.Perm.trans ?_ (List.Perm.append_right _ (flatIds_lookup h).symm)
    simp only [List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

/-- `Free` keeps the state well-formed, and adds exactly the run to the free and pending ids. -/
theorem freePages_ok {fl : FLPg} {txid id : w64} {n : Nat} (hwf : fl.WF)
    (hcan : fl.canFree txid id n) :
    (∀ x, x ∈ (fl.freePages txid id n).allIds ↔ x ∈ fl.allIds ∨ x ∈ runIds id n) ∧
    (fl.freePages txid id n).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  obtain ⟨c1, c2, c3, c4, c5⟩ := hcan
  have hp := pendingIds_freePages fl txid id n
  have hall : (fl.freePages txid id n).allIds.Perm (fl.allIds ++ runIds id n) := by
    unfold FLPg.allIds
    rw [List.append_assoc]
    exact List.Perm.append_left _ hp
  have hrun := runIds_nodup (id := id) (n := n) (by omega)
  refine ⟨fun x => ?_, ?_, ?_, h3, ?_, ?_⟩
  · rw [hall.mem_iff, List.mem_append]
  · rw [hall.nodup_iff, List.nodup_append]
    exact ⟨h1, hrun, fun a ha b hb e => c3 b hb (e ▸ ha)⟩
  · intro x hx
    rcases List.mem_append.1 (hall.mem_iff.1 hx) with hx | hx
    · exact h2 x hx
    · have := ((mem_runIds (id := id) (by omega)).1 hx).1; omega
  · rw [hall.length_eq, List.length_append, runIds_length]; omega
  · intro t p hp'
    unfold FLPg.freePages at hp'
    simp only at hp'
    by_cases ht : txid = t
    · subst ht
      rw [GMap.lookup_insert] at hp'
      cases hp'
      simp only [List.length_append, runIds_length, List.length_replicate]
      rcases h : fl.pending !! txid with _ | pd
      · simp
      · simp [h5 txid pd h]
    · rw [GMap.lookup_insert_ne _ _ ht] at hp'
      exact h5 t p hp'

/-- Well-formed but for the free and pending ids being disjoint (what `Read` leaves inside
`Reload`, the page holding ids still pending; `NoSyncReload` drops them again). -/
def FLPg.WFw (fl : FLPg) : Prop :=
  fl.pendingIds.Nodup ∧ (∀ id ∈ fl.allIds, 2 ≤ id.toNat) ∧ PgidsIncr fl.free ∧
  fl.allIds.length < 2 ^ 63 ∧
  (∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length)

theorem FLPg.WF.wfw {fl : FLPg} (h : fl.WF) : fl.WFw :=
  ⟨(List.nodup_append.1 h.1).2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A weakly well-formed state whose free ids are not pending is well-formed. -/
theorem FLPg.WFw.wf {fl : FLPg} (h : fl.WFw) (hd : ∀ x ∈ fl.free, x ∉ fl.pendingIds) :
    fl.WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h2, h3, h4, h5⟩
  unfold FLPg.allIds
  exact List.nodup_append.2 ⟨h3.nodup, h1, fun a ha b hb e => hd a ha (e ▸ hb)⟩

/-- The state whose free ids are the increasing ids `xs` (at least 2) but the pending ones
(`NoSyncReload`) is well-formed, from a weakly well-formed state. -/
theorem reload_WF_w {fl : FLPg} {xs : List w64} (hwf : fl.WFw) (hinc : PgidsIncr xs)
    (hge : ∀ x ∈ xs, 2 ≤ x.toNat) (hlen : xs.length + fl.pendingIds.length < 2 ^ 63) :
    (fl.reload xs).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  have hfs : (xs.filter (fun x => decide (x ∉ fl.pendingIds))).Sublist xs := by
    apply List.filter_sublist
  have hinc' : PgidsIncr (xs.filter (fun x => decide (x ∉ fl.pendingIds))) :=
    List.Pairwise.sublist hfs hinc
  have hr : fl.reload xs = { fl with free := xs.filter (fun x => decide (x ∉ fl.pendingIds)) } := by
    unfold FLPg.reload; rw [sortPgids_of_incr hinc']
  rw [hr]
  refine ⟨?_, ?_, hinc', ?_, h5⟩
  · show (_ ++ fl.pendingIds).Nodup
    rw [List.nodup_append]
    refine ⟨hfs.nodup hinc.nodup, h1, fun a ha b hb e => ?_⟩
    subst e
    simp only [List.mem_filter, decide_eq_true_iff] at ha
    exact ha.2 hb
  · intro id hid
    rcases List.mem_append.1 hid with h | h
    · exact hge id (hfs.subset h)
    · exact h2 id (List.mem_append_right _ h)
  · show (_ ++ fl.pendingIds).length < _
    have := List.length_filter_le (fun x => decide ¬x ∈ fl.pendingIds) xs
    simp only [List.length_append]; omega

theorem reload_free {fl : FLPg} {xs : List w64} (hinc : PgidsIncr xs) :
    (fl.reload xs).free = xs.filter (fun x => decide (x ∉ fl.pendingIds)) := by
  unfold FLPg.reload; rw [sortPgids_of_incr (List.Pairwise.sublist List.filter_sublist hinc)]

/-- Allocating keeps the state well-formed. -/
theorem alloc_WF {fl : FLPg} (h : fl.WF) (txid r : w64) (n : Nat) :
    (fl.alloc txid r n).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hsub : (fl.alloc txid r n).allIds.Sublist fl.allIds := by
    unfold FLPg.allIds FLPg.alloc FLPg.pendingIds
    exact List.Sublist.append (by apply List.filter_sublist) (List.Sublist.refl _)
  have hfs : (fl.alloc txid r n).free.Sublist fl.free := by
    unfold FLPg.alloc; apply List.filter_sublist
  refine ⟨hsub.nodup h1, fun id hid => h2 id (hsub.subset hid), List.Pairwise.sublist hfs h3,
    by have := hsub.length_le; omega, h5⟩

/-- The free and pending ids after an allocation: those before but the run. -/
theorem alloc_allIds {fl : FLPg} {txid r : w64} {n : Nat} (hwf : fl.WF)
    (hcan : fl.canAlloc r n) (x : w64) :
    x ∈ (fl.alloc txid r n).allIds ↔ x ∈ fl.allIds ∧ ¬ inRun r n x := by
  unfold FLPg.allIds FLPg.alloc FLPg.pendingIds
  simp only [List.mem_append, List.mem_filter, decide_eq_true_iff]
  constructor
  · rintro (⟨h, hn⟩ | h)
    · exact ⟨Or.inl h, hn⟩
    · refine ⟨Or.inr h, fun hr => ?_⟩
      exact (List.nodup_append.1 hwf.1).2.2 x (hcan.2 x hr) x h rfl
  · rintro ⟨h | h, hn⟩
    · exact Or.inl ⟨h, hn⟩
    · exact Or.inr h

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

end bbolt
end EtcdGrove
end Perennial
