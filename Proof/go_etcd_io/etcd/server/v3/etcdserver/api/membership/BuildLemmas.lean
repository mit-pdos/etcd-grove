/-
**Pure facts of a new cluster's members** (claim #34, stage 2, 2026-11-25): the members map of a list
of members with distinct ids (`memOfList`) holds each under its id, does not depend on the list's
order, and has distinct names when the members are an initial cluster's entries. Lean-first. A defs
module (`NewClusterFromURLsMap`'s proof and `bootstrapNewClusterNoWAL`'s use them).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver.api

/-- `memOfList` from any start: an id of the list's is its member, any other the start's. -/
theorem membership.foldl_insert_lookup (L : List apply.MemberM) (m0 : GMap w64 apply.MemberM)
    (hnd : (L.map (·.id)).Nodup) (k : w64) :
    (L.foldl (fun mem m => mem.insert m.id m) m0) !! k =
      (L.find? (fun m => m.id = k)).or (m0 !! k) := by
  induction L generalizing m0 with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hna, hnd⟩ := hnd
    simp only [List.foldl_cons]
    rw [ih _ hnd]
    by_cases hk : a.id = k
    · subst hk
      have hnone : L.find? (fun m => decide (m.id = a.id)) = none := by
        rw [List.find?_eq_none]
        intro x hx hxa
        exact hna ⟨x, hx, of_decide_eq_true hxa⟩
      simp [hnone, GMap.lookup_insert]
    · simp [List.find?_cons, hk, GMap.lookup_insert_ne _ _ hk]

/-- **`memOfList`'s lookup**: the member of the list with that id (distinct ids). -/
theorem membership.memOfList_lookup (L : List apply.MemberM) (hnd : (L.map (·.id)).Nodup)
    (k : w64) : membership.memOfList L !! k = L.find? (fun m => m.id = k) := by
  unfold membership.memOfList
  rw [membership.foldl_insert_lookup L ∅ hnd k]
  cases L.find? (fun m => m.id = k) <;> simp

/-- **A member of `memOfList`** is a member of the list with that id (distinct ids). -/
theorem membership.memOfList_lookup_some (L : List apply.MemberM) (hnd : (L.map (·.id)).Nodup)
    (k : w64) (m : apply.MemberM) :
    membership.memOfList L !! k = some m ↔ m ∈ L ∧ m.id = k := by
  rw [membership.memOfList_lookup L hnd k]
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  · rintro ⟨hm, rfl⟩
    cases hf : L.find? (fun x => decide (x.id = m.id)) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (decide_eq_true rfl) (hf m hm)
    | some m' =>
      have hm' := List.mem_of_find?_eq_some hf
      have hid : m'.id = m.id := by simpa using List.find?_some hf
      -- two members of one id are one member (distinct ids)
      have : m' = m := by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm'
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hm
        have hij : i = j := by
          exact (List.Nodup.getElem_inj hnd (i := i) (j := j)
            (hi := by simpa using hi) (hj := by simpa using hj)).1 (by simpa using hid)
        subst hij; rfl
      rw [this]

/-- Each member of `memOfList` is under its own id. -/
theorem membership.memIdsOk_memOfList (L : List apply.MemberM) (hnd : (L.map (·.id)).Nodup) :
    membership.memIdsOk (membership.memOfList L) := by
  intro k m h
  exact ((membership.memOfList_lookup_some L hnd k m).1 h).2

/-- **`memOfList` does not depend on the list's order** (distinct ids). -/
theorem membership.memOfList_perm (L₁ L₂ : List apply.MemberM) (hp : L₁.Perm L₂)
    (hnd : (L₁.map (·.id)).Nodup) : membership.memOfList L₁ = membership.memOfList L₂ := by
  have hnd₂ : (L₂.map (·.id)).Nodup := (hp.map _).nodup_iff.1 hnd
  apply GMap.ext
  intro k
  show membership.memOfList L₁ !! k = membership.memOfList L₂ !! k
  cases h₁ : membership.memOfList L₁ !! k with
  | none =>
    cases h₂ : membership.memOfList L₂ !! k with
    | none => rfl
    | some m =>
      obtain ⟨hm, hid⟩ := (membership.memOfList_lookup_some L₂ hnd₂ k m).1 h₂
      rw [(membership.memOfList_lookup_some L₁ hnd k m).2 ⟨hp.mem_iff.2 hm, hid⟩] at h₁
      cases h₁
  | some m =>
    obtain ⟨hm, hid⟩ := (membership.memOfList_lookup_some L₁ hnd k m).1 h₁
    exact ((membership.memOfList_lookup_some L₂ hnd₂ k m).2 ⟨hp.mem_iff.1 hm, hid⟩).symm

/-- An id of `memOfList` is a list member's. -/
theorem membership.memOfList_isSome (L : List apply.MemberM) (hnd : (L.map (·.id)).Nodup)
    (k : w64) : (membership.memOfList L !! k).isSome ↔ k ∈ L.map (·.id) := by
  rw [membership.memOfList_lookup L hnd k]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 h
    exact List.mem_map.2 ⟨m, List.mem_of_find?_eq_some hm, by simpa using List.find?_some hm⟩
  · intro h
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    cases hf : L.find? (fun x => decide (x.id = m.id)) with
    | none => rw [List.find?_eq_none] at hf; exact absurd (decide_eq_true rfl) (hf m hm)
    | some _ => rfl

/-- `memOfList` of one more member: the insertion. -/
theorem membership.memOfList_append (L : List apply.MemberM) (m : apply.MemberM) :
    membership.memOfList (L ++ [m]) = (membership.memOfList L).insert m.id m := by
  unfold membership.memOfList
  rw [List.foldl_append]
  rfl

/-- **The members of an initial cluster's entries have distinct names** (each its entry's name). -/
theorem membership.memNamesUniq_memOfList (ks : List GoString) (f : GoString → apply.MemberM)
    (hname : ∀ k, (f k).name = k) (hnd : ((ks.map f).map (·.id)).Nodup) :
    membership.memNamesUniq (membership.memOfList (ks.map f)) := by
  intro k1 k2 m1 m2 h1 h2 hn
  obtain ⟨hm1, hid1⟩ := (membership.memOfList_lookup_some _ hnd k1 m1).1 h1
  obtain ⟨hm2, hid2⟩ := (membership.memOfList_lookup_some _ hnd k2 m2).1 h2
  obtain ⟨a1, -, rfl⟩ := List.mem_map.1 hm1
  obtain ⟨a2, -, rfl⟩ := List.mem_map.1 hm2
  rw [hname, hname] at hn
  subst hn
  rw [← hid1, ← hid2]

/-- Inserting the members of `L` adds at most `L.length` keys. -/
theorem membership.foldl_insert_size (L : List apply.MemberM) (m0 : GMap w64 apply.MemberM) :
    GMap.size (L.foldl (fun mem m => mem.insert m.id m) m0) ≤ GMap.size m0 + L.length := by
  induction L generalizing m0 with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (m0.insert a.id a)
    have h2 : GMap.size (m0.insert a.id a) ≤ GMap.size m0 + 1 := by
      show GMap.size (GMap.insert a.id a m0) ≤ _
      rw [GMap.map_size_insert]; split <;> omega
    omega

/-- The size of `memOfList` is at most the list's length. -/
theorem membership.memOfList_size (L : List apply.MemberM) :
    GMap.size (membership.memOfList L) ≤ L.length := by
  have := membership.foldl_insert_size L ∅
  rw [GMap.map_size_empty] at this
  unfold membership.memOfList; omega

/-- A map range's keys are a permutation of the map's `domList`. -/
theorem membership.keys_perm_domList {V : Type} (m : GMap GoString V) (keys : List GoString)
    (hk : ∀ k, k ∈ keys ↔ (m !! k).isSome) (hnd : keys.Nodup) : keys.Perm m.domList :=
  (List.perm_ext_iff_of_nodup hnd (GMap.nodup_dom_list m)).2
    (fun k => (hk k).trans (GMap.mem_dom_list m k).symm)

/-- **The loop's next key has a fresh id** (the keys' ids distinct): none of the keys before it. -/
theorem membership.loop_fresh (keys : List GoString) (g : GoString → w64) (i : Nat)
    (key : GoString) (hnd : (keys.map g).Nodup) (hk : keys[i]? = some key) :
    g key ∉ (keys.take i).map g := by
  have hsub : ((keys.take (i + 1)).map g).Sublist (keys.map g) :=
    (List.take_sublist _ _).map g
  have hnd' := hnd.sublist hsub
  rw [List.take_add_one, hk] at hnd'
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil] at hnd'
  intro hmem
  exact (List.nodup_append.1 hnd').2.2 _ hmem _ (List.mem_singleton_self _) rfl

/-- The loop's prefix grows by its next key. -/
theorem membership.take_succ_map {α β : Type} (keys : List α) (f : α → β) (i : Nat) (key : α)
    (hk : keys[i]? = some key) : (keys.take (i + 1)).map f = (keys.take i).map f ++ [f key] := by
  rw [List.take_add_one, hk]; simp

end EtcdGrove
end Perennial
