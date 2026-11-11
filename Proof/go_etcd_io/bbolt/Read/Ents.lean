/-
U6 (`notes/bbolt-proof-plan.md`): sorted entry lists. `bktEnts m` is sorted and holds `m`'s
bindings; a list map with distinct keys holds exactly its list's bindings; two strictly sorted entry
lists with the same members are equal. (Shared by `Read/LeafOfT` and `Read/TreeEnts`.)
-/
module

public import Proof.go_etcd_io.bbolt.Model.TreeData

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Ents

section ents

/-- Entries strictly increasing by key. -/
def esSorted (es : List BoltEnt) : Prop := es.Pairwise (fun a b => go.GoStringLt a.1 b.1)

/-- `bktEnts` is sorted (`Model/Cursor`'s private `bktEnts_sorted'`). -/
theorem bktEnts_sorted (m : BktData) : esSorted (bktEnts m) := by
  unfold bktEnts esSorted
  have hn : ((m.toList.mergeSort (fun a b => !decide (go.GoStringLt b.1 a.1))).map
      Prod.fst).Nodup :=
    (((List.mergeSort_perm m.toList _).map Prod.fst).nodup_iff).2 (GMap.toList_keys_nodup m)
  have hle : (m.toList.mergeSort (fun a b => !decide (go.GoStringLt b.1 a.1))).Pairwise
      (fun a b => (!decide (go.GoStringLt b.1 a.1)) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at *
      intro h3
      rcases Classical.em (go.GoStringLt b.1 a.1) with h | h
      · exact h1 h
      · rcases Classical.em (go.GoStringLt c.1 b.1) with h' | h'
        · exact h2 h'
        · have e1 := Classical.byContradiction fun hne : ¬ (a.1 = b.1 ∨ go.GoStringLt a.1 b.1) => by
            exact hne (by
              rcases Classical.em (go.GoStringLt a.1 b.1) with h4 | h4
              · exact Or.inr h4
              · exact Or.inl (go.goStringLt_eq_of_not_lt h4 h))
          rcases e1 with e1 | e1
          · rw [e1] at h3; exact h2 h3
          · exact h2 (go.goStringLt_trans h3 e1)
    · intro a b
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true]
      rcases Classical.em (go.GoStringLt b.1 a.1) with h | h
      · right; exact go.goStringLt_asymm h
      · left; exact h
  rw [List.Nodup, List.pairwise_map] at hn
  refine (hle.and hn).imp (fun ⟨h1, h2⟩ => ?_)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
  rcases Classical.em (go.GoStringLt _ _) with h | h
  · exact h
  · exact absurd (go.goStringLt_eq_of_not_lt h h1) h2

theorem mem_bktEnts (m : BktData) (e : BoltEnt) : e ∈ bktEnts m ↔ m !! e.1 = some e.2 := by
  unfold bktEnts
  rw [(List.mergeSort_perm _ _).mem_iff]
  obtain ⟨k, v⟩ := e
  exact GMap.mem_toList _ _ _

/-- A list map with distinct keys holds exactly its list's bindings. -/
theorem ofList_lookup_iff {K V : Type} [DecidableEq K] : ∀ (L : List (K × V)),
    L.Pairwise (fun a b => a.1 ≠ b.1) → ∀ k v, (GMap.ofList L) !! k = some v ↔ (k, v) ∈ L
  | [], _, k, v => by
    have h0 : (GMap.ofList ([] : List (K × V))) !! k = none := rfl
    rw [h0]
    simp
  | (a1, a2) :: L, h, k, v => by
    rw [List.pairwise_cons] at h
    simp only [GMap.ofList, GMap.lookup_insert_eq_iff]
    by_cases hk : a1 = k
    · subst hk
      rw [if_pos rfl]
      constructor
      · intro e; cases e; exact List.mem_cons_self
      · intro hm
        rcases List.mem_cons.1 hm with e | hm'
        · cases e; rfl
        · exact absurd rfl (h.1 (a1, v) hm')
    · rw [if_neg hk, ofList_lookup_iff L h.2 k v]
      constructor
      · intro hm; exact List.mem_cons_of_mem _ hm
      · intro hm
        rcases List.mem_cons.1 hm with e | hm'
        · cases e; exact absurd rfl hk
        · exact hm'

/-- Sorted entry lists with the same members are equal. -/
theorem sorted_ext : ∀ (l1 l2 : List BoltEnt), esSorted l1 → esSorted l2 →
    (∀ e, e ∈ l1 ↔ e ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
    unfold esSorted at h1 h2
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      apply Classical.byContradiction
      intro hne
      have ha := (h a).1 List.mem_cons_self
      have hb := (h b).2 List.mem_cons_self
      rcases List.mem_cons.1 ha with e | ha'
      · exact hne e
      rcases List.mem_cons.1 hb with e | hb'
      · exact hne e.symm
      exact go.goStringLt_asymm (h2.1 a ha') (h1.1 b hb')
    subst hab
    congr 1
    apply sorted_ext t1 t2 h1.2 h2.2
    intro e
    constructor
    · intro he
      rcases List.mem_cons.1 ((h e).1 (List.mem_cons_of_mem _ he)) with e' | he'
      · subst e'; exact absurd (h1.1 _ he) (go.goStringLt_irrefl _)
      · exact he'
    · intro he
      rcases List.mem_cons.1 ((h e).2 (List.mem_cons_of_mem _ he)) with e' | he'
      · subst e'; exact absurd (h2.1 _ he) (go.goStringLt_irrefl _)
      · exact he'


end ents

end Ents

end bbolt
end EtcdGrove
end Perennial
