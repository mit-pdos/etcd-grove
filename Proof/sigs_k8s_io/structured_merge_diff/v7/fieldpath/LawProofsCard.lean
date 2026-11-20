/-
**Counting a set's paths** (`Set.Size`, `SetNodeMap.Size`): a set's count is its members' plus
its children's, a node list's count the sum of its nodes' counts.

Prove phase (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsTrie
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace fpK

variable {α β : Type}

/-- A disjoint union counts its two sides. -/
theorem card_disj [DecidableEq α] {X Y Z : FSet α} (hz : ∀ x, x ∈ Z ↔ x ∈ X ∨ x ∈ Y)
    (hd : ∀ x, x ∈ X → x ∉ Y) : Z.card = X.card + Y.card := by
  obtain ⟨lx, hnx, hex, hlx⟩ := FSet.hasCard_card' X
  obtain ⟨ly, hny, hey, hly⟩ := FSet.hasCard_card' Y
  apply (FSet.hasCard_iff _ _).1
  refine ⟨lx ++ ly, List.nodup_append.2 ⟨hnx, hny, ?_⟩, ?_, by rw [List.length_append, hlx, hly]⟩
  · intro a ha b hb hab
    subst hab
    exact hd a (by rw [← hex, FSet.mem_ofList']; exact ha) (by rw [← hey, FSet.mem_ofList']; exact hb)
  · apply FSet.ext'
    intro x
    rw [FSet.mem_ofList', List.mem_append, hz, ← hex, ← hey, FSet.mem_ofList', FSet.mem_ofList']

/-- An injective image counts as many. -/
theorem card_map_inj [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (X : FSet α) : (FSet.map f X).card = X.card := by
  obtain ⟨lx, hnx, hex, hlx⟩ := FSet.hasCard_card' X
  rw [← hlx]
  apply (FSet.hasCard_iff _ _).1
  refine ⟨lx.map f, List.Pairwise.map f (fun a b h e => h (hf e)) hnx, ?_, by simp⟩
  apply FSet.ext'
  intro y
  rw [FSet.mem_ofList', FSet.mem_map', List.mem_map, ← hex]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (FSet.mem_ofList' _ _).2 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (FSet.mem_ofList' _ _).1 hx, rfl⟩

theorem card_cons_map (k : PE) (S : PathSet) : (FSet.map (k :: ·) S).card = S.card :=
  card_map_inj _ (fun a b h => (List.cons.inj h).2) S

/-- **A set's count**: its members' and its children's. -/
theorem set_card (S : PathSet) (hne : [] ∉ S) : S.card = S.tops.card + S.deep.card := by
  rw [card_disj (X := FSet.map (fun e : PE => [e]) S.tops) (Y := S.deep)]
  · rw [card_map_inj _ (fun a b h => List.cons.inj h |>.1)]
  · intro q
    rw [FSet.mem_map', PathSet_mem_deep_law_holds]
    match q with
    | [] => simp only [List.length_nil]; exact ⟨fun h => absurd h hne, by
        rintro (⟨e, -, h⟩ | ⟨-, h⟩)
        · cases h
        · omega⟩
    | [e] =>
      constructor
      · intro h; exact Or.inl ⟨e, (PathSet_mem_tops_law_holds S e).2 h, rfl⟩
      · rintro (⟨e', he, h⟩ | ⟨h, -⟩)
        · obtain rfl : e = e' := (List.cons.inj h).1
          exact (PathSet_mem_tops_law_holds S e).1 he
        · exact h
    | e :: e' :: r =>
      constructor
      · intro h; exact Or.inr ⟨h, by simp⟩
      · rintro (⟨e'', -, h⟩ | ⟨h, -⟩)
        · cases h
        · exact h
  · intro q hq hd
    rw [FSet.mem_map'] at hq
    obtain ⟨e, -, rfl⟩ := hq
    have := ((PathSet_mem_deep_law_holds S [e]).1 hd).2
    simp at this

/-- **Two sets are equal** when their members and their children are. -/
theorem set_eq_iff (A B : PathSet) (hA : [] ∉ A) (hB : [] ∉ B) :
    A = B ↔ A.tops = B.tops ∧ A.deep = B.deep := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨ht, hd⟩
    apply FSet.ext'
    intro q
    match q with
    | [] => exact ⟨fun h => absurd h hA, fun h => absurd h hB⟩
    | [e] => rw [← PathSet_mem_tops_law_holds, ← PathSet_mem_tops_law_holds, ht]
    | e :: e' :: r =>
      have h1 := PathSet_mem_deep_law_holds A (e :: e' :: r)
      have h2 := PathSet_mem_deep_law_holds B (e :: e' :: r)
      rw [hd] at h1
      simp only [List.length_cons] at h1 h2
      constructor
      · intro h; exact (h2.1 (h1.2 ⟨h, by omega⟩)).1
      · intro h; exact (h1.1 (h2.2 ⟨h, by omega⟩)).1

open fpC in
/-- One more node: its set's count added. -/
theorem nl_card_snoc (l : NL) (k : PE) (S : PathSet) (hk : k ∉ keys l) :
    (nlPaths (l ++ [(k, S)])).card = (nlPaths l).card + S.card := by
  rw [card_disj (X := nlPaths l) (Y := FSet.map (k :: ·) S), card_cons_map]
  · intro q
    rw [nlPaths_append, nlPaths_single, FSet.mem_map']
  · intro q hq hm
    rw [FSet.mem_map'] at hm
    obtain ⟨r, -, rfl⟩ := hm
    exact nl_nokey hk r hq

open fpC in
/-- The nodes before `i` and node `i`. -/
theorem nl_card_take (l : NL) (i : Nat) (hi : i < l.length) (hnd : (keys l).Nodup) :
    (nlPaths (l.take (i + 1))).card = (nlPaths (l.take i)).card + (l[i]).2.card := by
  rw [take_succ' l i hi]
  apply nl_card_snoc
  intro hm
  have hnd' : (keys (l.take (i + 1))).Nodup := by
    simp only [keys, List.map_take]; exact hnd.sublist (List.take_sublist _ _)
  rw [take_succ' l i hi] at hnd'
  simp only [keys, List.map_append, List.map_cons, List.map_nil] at hnd' hm
  exact (List.nodup_append.1 hnd').2.2 _ hm _ (List.mem_singleton_self _) rfl

open fpC in
theorem nl_card_take_le (l : NL) (i : Nat) : (nlPaths (l.take i)).card ≤ (nlPaths l).card := by
  apply FSet.card_le_of_subset
  intro q hq
  rw [← List.take_append_drop i l, nlPaths_append]
  exact Or.inl hq

open fpC in
theorem nl_key_iff {l : NL} (hl : NLok l) (k : PE) :
    k ∈ keys l ↔ ∃ r, k :: r ∈ nlPaths l := by
  constructor
  · intro hk
    simp only [keys, List.mem_map] at hk
    obtain ⟨⟨k', S⟩, hm, rfl⟩ := hk
    obtain ⟨-, ⟨r, hr⟩, -⟩ := hl.2 _ S hm
    exact ⟨r, (nl_col hl hm r).2 hr⟩
  · rintro ⟨r, hr⟩
    obtain ⟨k', r', he, hk⟩ := nl_heads _ hr
    simp only [List.cons.injEq] at he
    rw [he.1]; exact hk

open fpC in
/-- **Two canonical node lists with the same paths are equal.** -/
theorem nl_eq_of {l1 l2 : NL} (h1 : NLok l1) (h2 : NLok l2) (h : nlPaths l1 = nlPaths l2) :
    l1 = l2 := by
  have hk : keys l1 = keys l2 :=
    PE_sorted_ext_law_holds _ _ (nlok_wf h1) (nlok_wf h2) h1.1 h2.1
      (fun k => by rw [nl_key_iff h1, nl_key_iff h2, h])
  have hlen : l1.length = l2.length := by
    have := congrArg List.length hk; simpa [keys] using this
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have hki : (l1[i]).1 = (l2[i]).1 := by
    have := congrArg (fun l => l[i]?) hk
    simp [keys, List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at this
    exact this
  have hm1 : (l1[i].1, l1[i].2) ∈ l1 := List.getElem_mem hi1
  have hm2 : (l2[i].1, l2[i].2) ∈ l2 := List.getElem_mem hi2
  rw [← hki] at hm2
  have hS : l1[i].2 = l2[i].2 := by
    apply FSet.ext'
    intro r
    rw [← nl_col h1 hm1 r, ← nl_col h2 hm2 r, h]
  exact Prod.ext hki hS

end fpK

end smd
end EtcdGrove
end Perennial
