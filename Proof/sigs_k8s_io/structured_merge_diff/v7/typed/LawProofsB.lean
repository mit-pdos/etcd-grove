/-
**Proofs of the pure merge/compare/reconcile laws of `typed`** (`WalkerLaws.lean`), part B:
`merge_mergeO`, `compare_cmpO`, `optU_assoc`, `optU_idem`, `reconOut_scalar`,
`reconOut_granular`, `mergeO_leaf`, `cmpO_below`, and the fuel laws.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace LawB

/-! ## Finite sets -/

theorem fset_union_assoc {α : Type} (a b c : FSet α) :
    FSet.union (FSet.union a b) c = FSet.union a (FSet.union b c) := by
  induction a using Quotient.inductionOn with | h la =>
  induction b using Quotient.inductionOn with | h lb =>
  induction c using Quotient.inductionOn with | h lc =>
  exact congrArg (Quotient.mk _) (List.append_assoc la lb lc)

theorem fset_union_idem {α : Type} (a b : FSet α) :
    FSet.union a (FSet.union a b) = FSet.union a b := by
  induction a using Quotient.inductionOn with | h la =>
  induction b using Quotient.inductionOn with | h lb =>
  exact Quotient.sound (fun x => by simp only [List.mem_append, ← or_assoc, or_self])

theorem ps_union_empty (a : PathSet) : PathSet.union a PathSet.empty = a := by
  induction a using Quotient.inductionOn with | h la =>
  exact congrArg (Quotient.mk _) (List.append_nil la)

theorem cardLt_union_left (a b : PathSet) (n : Nat) (h : (PathSet.union a b).CardLt n) :
    a.CardLt n :=
  Nat.lt_of_le_of_lt (FSet.card_le_of_subset _ _ (fun x hx => (FSet.mem_union' a b x).2 (Or.inl hx))) h

theorem cardLt_union_right (a b : PathSet) (n : Nat) (h : (PathSet.union a b).CardLt n) :
    b.CardLt n :=
  Nat.lt_of_le_of_lt (FSet.card_le_of_subset _ _ (fun x hx => (FSet.mem_union' a b x).2 (Or.inr hx))) h

theorem fset_union_self {α : Type} (a : FSet α) : FSet.union a a = a := by
  induction a using Quotient.inductionOn with | h la =>
  exact Quotient.sound (fun x => by simp only [List.mem_append, or_self])

theorem fset_empty_union {α : Type} (a : FSet α) : FSet.union FSet.empty a = a := by
  induction a using Quotient.inductionOn with | h la =>
  rfl

theorem fset_union_empty {α : Type} (a : FSet α) : FSet.union a FSet.empty = a := by
  induction a using Quotient.inductionOn with | h la =>
  exact congrArg (Quotient.mk _) (List.append_nil la)

theorem fset_filter_false {α : Type} (p : α → Bool) (s : FSet α) (h : ∀ x, p x = false) :
    (s.filter p).isEmpty = true := by
  induction s using Quotient.inductionOn with | h l =>
  show (!(l.filter p).any (fun _ => true)) = true
  rw [List.filter_eq_nil_iff.2 (fun x _ => by simp [h x])]
  rfl

end LawB

open LawB

theorem merge_mergeO_law_holds : merge_mergeO.law := fun _ _ _ _ => rfl

theorem compare_cmpO_law_holds : compare_cmpO.law := fun _ _ _ _ => rfl

theorem optU_assoc_law_holds : optU_assoc.law := by
  intro a b c
  cases a <;> cases b <;> cases c <;> simp only [optU, PathSet.union, fset_union_assoc]

theorem optU_idem_law_holds : optU_idem.law := by
  intro a b
  cases a <;> cases b <;> simp only [optU, PathSet.union, fset_union_idem, fset_union_self]

theorem atomicNodes_scalar (S : Schema) (t : TypeRef) (s : Scalar) (F : PathSet)
    (h : S.find t.name = some (.scalar s)) : (atomicNodes S t F).isEmpty = true := by
  unfold atomicNodes
  apply fset_filter_false
  intro p
  cases p with
  | nil => rfl
  | cons pe p => simp [reconAt, isGranularT, h]

theorem reconOut_scalar_law_holds : reconOut_scalar.law := by
  intro S t p b F s h
  have hn := atomicNodes_scalar S t s F h
  simp [reconOut, reconTouch, h, hn]

theorem reconOut_granular_law_holds : reconOut_granular.law := by
  intro S t p b F h
  unfold reconOut reconBelow
  simp only [h, Bool.false_or, Bool.not_eq_true', Bool.false_eq_true, ite_false]
  cases hn : (atomicNodes S t F).isEmpty
  · simp only [ite_true, PathSet.union, empty, PathSet.empty, fset_empty_union]
    rfl
  · rfl

theorem mergeO_leaf_law_holds : mergeO_leaf.law := by
  intro S t l r hleaf _
  unfold mergeO fuelO
  rw [show sizeO l + sizeO r + 1 = (sizeO l + sizeO r) + 1 from rfl]
  unfold mergeF
  unfold leafAt at hleaf
  split at hleaf <;> rename_i heq <;> simp only [heq] <;> simp_all

/-! ## Fuel -/

namespace LawB

theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr_mem l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem size_pos (x : UVal) : 1 ≤ x.size := by
  cases x <;> simp [UVal.size]

theorem mem_sizeL {x : UVal} : ∀ {vs : List UVal}, x ∈ vs → x.size ≤ UVal.sizeL vs
  | v :: vs, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [UVal.sizeL]; omega
    · have := mem_sizeL h; simp only [UVal.sizeL]; omega

theorem mem_sizeM {k : GoString} {x : UVal} : ∀ {kvs : List (GoString × UVal)},
    (k, x) ∈ kvs → x.size ≤ UVal.sizeM kvs
  | (k', v) :: kvs, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h; simp only [UVal.sizeM]; omega
    · have := mem_sizeM h; simp only [UVal.sizeM]; omega

theorem itemOf_size (ks : List GoString) (vs : List UVal) (pe : PE) :
    sizeO (itemOf ks vs pe) ≤ UVal.sizeL vs := by
  unfold itemOf
  cases h : vs.find? (fun v => decide (keyOf ks v = some pe)) with
  | none => simp [sizeO]
  | some x => exact mem_sizeL (List.mem_of_find?_eq_some h)

theorem listItems_size (l : Option UVal) : UVal.sizeL (listItems l) ≤ sizeO l := by
  rcases l with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp [listItems, sizeO, UVal.sizeL, UVal.size]

theorem listItems_size_ne (l : Option UVal) (h : (listItems l).isEmpty = false) :
    UVal.sizeL (listItems l) + 1 ≤ sizeO l := by
  rcases l with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp_all [listItems, sizeO, UVal.size]

theorem mapItems_size (l : Option UVal) : UVal.sizeM (mapItems l) ≤ sizeO l := by
  rcases l with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp [mapItems, sizeO, UVal.sizeM, UVal.size]

theorem mapItems_size_ne (l : Option UVal) (h : (mapItems l).isEmpty = false) :
    UVal.sizeM (mapItems l) + 1 ≤ sizeO l := by
  rcases l with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp_all [mapItems, sizeO, UVal.size]

/-- What `zipLexical` pairs comes from its sides. -/
def ZipOk (xs ys : List (GoString × UVal)) (e : GoString × Option UVal × Option UVal) : Prop :=
  (∀ x, e.2.1 = some x → (e.1, x) ∈ xs) ∧ (∀ y, e.2.2 = some y → (e.1, y) ∈ ys)

theorem zipLexical_mem : ∀ (f : Nat) (xs ys : List (GoString × UVal)) e,
    e ∈ zipLexical f xs ys → ZipOk xs ys e
  | 0, xs, ys, e, h => by simp [zipLexical] at h
  | f + 1, [], [], e, h => by simp [zipLexical] at h
  | f + 1, (k, a) :: xs, [], e, h => by
    simp only [zipLexical, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨k', a'⟩, hm, rfl⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp only [Option.some.injEq]; rintro _ rfl; exact List.mem_cons_of_mem _ hm,
        by simp⟩
  | f + 1, [], (k, b) :: ys, e, h => by
    simp only [zipLexical, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨k', b'⟩, hm, rfl⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp only [Option.some.injEq]; rintro _ rfl; exact List.mem_cons_of_mem _ hm⟩
  | f + 1, (k, a) :: xs, (k', b) :: ys, e, h => by
    simp only [zipLexical] at h
    split at h
    · rename_i hk
      rcases List.mem_cons.1 h with rfl | h
      · subst hk; exact ⟨by simp, by simp⟩
      · obtain ⟨h1, h2⟩ := zipLexical_mem f xs ys e h
        exact ⟨fun x hx => List.mem_cons_of_mem _ (h1 x hx),
          fun y hy => List.mem_cons_of_mem _ (h2 y hy)⟩
    · split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨by simp, by simp⟩
        · obtain ⟨h1, h2⟩ := zipLexical_mem f xs ((k', b) :: ys) e h
          exact ⟨fun x hx => List.mem_cons_of_mem _ (h1 x hx), h2⟩
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨by simp, by simp⟩
        · obtain ⟨h1, h2⟩ := zipLexical_mem f ((k, a) :: xs) ys e h
          exact ⟨h1, fun y hy => List.mem_cons_of_mem _ (h2 y hy)⟩

theorem zipOk_size {xs ys : List (GoString × UVal)} {e} (h : ZipOk xs ys e) :
    sizeO e.2.1 ≤ UVal.sizeM xs ∧ sizeO e.2.2 ≤ UVal.sizeM ys := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · cases ha : e.2.1 with
    | none => simp [sizeO]
    | some x => exact mem_sizeM (h1 x ha)
  · cases hb : e.2.2 with
    | none => simp [sizeO]
    | some y => exact mem_sizeM (h2 y hb)

/-- The children's fuel at a granular list node. -/
theorem list_child_fuel (ks : List GoString) (l r : Option UVal) (pe : PE)
    (hne : ¬((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true)) :
    fuelO (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe) ≤ sizeO l + sizeO r ∧
    fuelO (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe) ≤
      fuelL (listItems l) (listItems r) := by
  have a1 := itemOf_size ks (listItems l) pe
  have a2 := itemOf_size ks (listItems r) pe
  have b1 := listItems_size l
  have b2 := listItems_size r
  unfold fuelO fuelL
  refine ⟨?_, by omega⟩
  cases hl : (listItems l).isEmpty
  · have := listItems_size_ne l hl; omega
  · cases hr : (listItems r).isEmpty
    · have := listItems_size_ne r hr; omega
    · exact absurd ⟨hl, hr⟩ hne

/-- The children's fuel at a granular map node. -/
theorem map_child_fuel (l r : Option UVal) (e : GoString × Option UVal × Option UVal)
    (he : e ∈ zipLexical ((mapItems l).length + (mapItems r).length + 1) (mapItems l) (mapItems r))
    (hne : ¬((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true)) :
    fuelO e.2.1 e.2.2 ≤ sizeO l + sizeO r ∧
    fuelO e.2.1 e.2.2 ≤ fuelM (mapItems l) (mapItems r) := by
  obtain ⟨a1, a2⟩ := zipOk_size (zipLexical_mem _ _ _ e he)
  have b1 := mapItems_size l
  have b2 := mapItems_size r
  unfold fuelO fuelM
  refine ⟨?_, by omega⟩
  cases hl : (mapItems l).isEmpty
  · have := mapItems_size_ne l hl; omega
  · cases hr : (mapItems r).isEmpty
    · have := mapItems_size_ne r hr; omega
    · exact absurd ⟨hl, hr⟩ hne

theorem fm_congr {α β γ : Type} {L : List α} {f g : α → Option β} (k : List β → γ)
    (h : ∀ a ∈ L, f a = g a) : k (L.filterMap f) = k (L.filterMap g) := by
  rw [filterMap_congr_mem L h]

/-- `mergeF` with any fuel at least `fuelO` is the same. -/
theorem mergeF_stable : ∀ (n m : Nat) (S : Schema) (t : TypeRef) (l r : Option UVal),
    fuelO l r ≤ n → fuelO l r ≤ m → mergeF n S t l r = mergeF m S t l r
  | 0, _, _, _, _, _, h, _ => by unfold fuelO at h; omega
  | _ + 1, 0, _, _, _, _, _, h => by unfold fuelO at h; omega
  | n + 1, m + 1, S, t, l, r, hn, hm => by
    have hn' : sizeO l + sizeO r ≤ n := by unfold fuelO at hn; omega
    have hm' : sizeO l + sizeO r ≤ m := by unfold fuelO at hm; omega
    simp only [mergeF]
    split
    · rfl
    · rename_i e rel ks _
      split
      · rfl
      · rename_i hne
        have hne' : ¬((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true) :=
          fun h => hne (Or.inr h)
        have : (mergeKeys (keysOf ks (listItems l)) (keysOf ks (listItems r))).filterMap
            (fun pe => mergeF n S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)) =
          (mergeKeys (keysOf ks (listItems l)) (keysOf ks (listItems r))).filterMap
            (fun pe => mergeF m S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)) := by
          congr 1; funext pe
          have := (list_child_fuel ks l r pe hne').1
          exact mergeF_stable n m S e _ _ (by omega) (by omega)
        simp only [this]
    · rename_i fs e rel _
      split
      · rfl
      · rename_i hne
        have hne' : ¬((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true) :=
          fun h => hne (Or.inr h)
        refine fm_congr (fun out : List (GoString × UVal) =>
          if out.isEmpty then none else some (UVal.map out)) ?_
        rintro ⟨k, a, b⟩ hmem
        have := (map_child_fuel l r _ hmem hne').1
        simp only at this ⊢
        split
        · rw [mergeF_stable n m S _ a b (by omega) (by omega)]
        · rfl
    · rfl

theorem map_congr' {α β γ : Type} {L : List α} {f g : α → β} (k : List β → γ)
    (h : ∀ a ∈ L, f a = g a) : k (L.map f) = k (L.map g) := by
  rw [List.map_congr_left h]

/-- `cmpF` with any fuel at least `fuelO` is the same. -/
theorem cmpF_stable : ∀ (n m : Nat) (S : Schema) (t : TypeRef) (p : Path) (l r : Option UVal),
    fuelO l r ≤ n → fuelO l r ≤ m → cmpF n S t p l r = cmpF m S t p l r
  | 0, _, _, _, _, _, _, h, _ => by unfold fuelO at h; omega
  | _ + 1, 0, _, _, _, _, _, _, h => by unfold fuelO at h; omega
  | n + 1, m + 1, S, t, p, l, r, hn, hm => by
    have hn' : sizeO l + sizeO r ≤ n := by unfold fuelO at hn; omega
    have hm' : sizeO l + sizeO r ≤ m := by unfold fuelO at hm; omega
    simp only [cmpF]
    split
    · rfl
    · rename_i e rel ks _
      split
      · rfl
      · rename_i hne
        have hne' : ¬((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true) :=
          fun h => hne (Or.inr h)
        refine map_congr' (fun cs => (Cmp.unionAll cs).union (nodeC p l r)) ?_
        intro pe _
        have := (list_child_fuel ks l r pe hne').1
        exact cmpF_stable n m S e _ _ _ (by omega) (by omega)
    · rename_i fs e rel _
      split
      · rfl
      · rename_i hne
        have hne' : ¬((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true) :=
          fun h => hne (Or.inr h)
        refine map_congr' (fun cs => (Cmp.unionAll cs).union (nodeC p l r)) ?_
        rintro ⟨k, a, b⟩ hmem
        have := (map_child_fuel l r _ hmem hne').1
        simp only at this ⊢
        split
        · rw [cmpF_stable n m S _ _ a b (by omega) (by omega)]
        · rfl
    · rfl

end LawB

open LawB

theorem mergeF_fuel_law_holds : mergeF_fuel.law := fun n S t l r h =>
  mergeF_stable n (fuelO l r) S t l r h (Nat.le_refl _)

theorem cmpF_fuel_law_holds : cmpF_fuel.law := fun n S t p l r h =>
  cmpF_stable n (fuelO l r) S t p l r h (Nat.le_refl _)

theorem mergeO_list_law_holds : mergeO_list.law := by
  intro S t e rel ks l r hf hleaf
  simp only [leafAt, hf, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff] at hleaf
  obtain ⟨hrel, hemp⟩ := hleaf
  have hne : ¬((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true) := by
    rintro ⟨h1, h2⟩; rcases hemp with h | h <;> simp_all
  unfold mergeO fuelO
  simp only [mergeF, hf, mergeListOut]
  split
  · rename_i h; exfalso; rcases h with h | h <;> simp_all
  refine fm_congr (fun out : List UVal => if out.isEmpty then none else some (UVal.list out)) ?_
  intro pe _
  have := list_child_fuel ks l r pe hne
  exact mergeF_stable _ _ S e _ _ this.1 this.2

theorem mergeO_map_law_holds : mergeO_map.law := by
  intro S t fs e rel l r hf hleaf
  simp only [leafAt, hf, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff] at hleaf
  obtain ⟨hrel, hemp⟩ := hleaf
  have hne : ¬((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true) := by
    rintro ⟨h1, h2⟩; rcases hemp with h | h <;> simp_all
  unfold mergeO fuelO
  simp only [mergeF, hf, mergeMapOut]
  split
  · rename_i h; exfalso; rcases h with h | h <;> simp_all
  refine fm_congr (fun out : List (GoString × UVal) =>
    if out.isEmpty then none else some (UVal.map out)) ?_
  rintro ⟨k, a, b⟩ hmem
  have := map_child_fuel l r _ hmem hne
  simp only at this ⊢
  rcases hft : fieldType fs e k with _ | t'
  · rfl
  · simp only
    rw [mergeF_stable (sizeO l + sizeO r) (fuelM (mapItems l) (mapItems r)) S t' a b
      this.1 this.2]

/-- **`cmpO_below.law` with the type resolving** (the stated law is false when `t` does not
resolve: `cmpO` is then `Cmp.none`, but `nodeC p none r` adds `p`; Go's `compare` returns an error
there before adding anything). -/
theorem cmpO_below_resolved (S : Schema) (t : TypeRef) (p : Path) (l r : Option UVal)
    (hres : (S.find t.name).isSome) :
    cmpO S t p l r =
      if leafAt S t l r then cmpBelow S t p l r else (cmpBelow S t p l r).union (nodeC p l r) := by
  unfold cmpO cmpBelow fuelO
  simp only [Nat.add_sub_cancel]
  cases hf : S.find t.name with
  | none => simp [hf] at hres
  | some a =>
    cases a with
    | scalar s => simp [cmpF, leafAt, hf]
    | list e rel ks =>
      simp only [cmpF, hf, leafAt]
      by_cases h : rel = .atomic ∨ ((listItems l).isEmpty = true ∧ (listItems r).isEmpty = true)
      · rcases h with h | ⟨h1, h2⟩ <;> simp_all
      · have h' : (decide (rel = .atomic) || ((listItems l).isEmpty && (listItems r).isEmpty)) =
            false := by
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
          refine ⟨fun h1 => h (Or.inl h1), ?_⟩
          cases h1 : (listItems l).isEmpty <;> cases h2 : (listItems r).isEmpty <;> simp_all
        rw [h']; simp only [h, ↓reduceIte]
        rfl
    | map fs e rel =>
      simp only [cmpF, hf, leafAt]
      by_cases h : rel = .atomic ∨ ((mapItems l).isEmpty = true ∧ (mapItems r).isEmpty = true)
      · rcases h with h | ⟨h1, h2⟩ <;> simp_all
      · have h' : (decide (rel = .atomic) || ((mapItems l).isEmpty && (mapItems r).isEmpty)) =
            false := by
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
          refine ⟨fun h1 => h (Or.inl h1), ?_⟩
          cases h1 : (mapItems l).isEmpty <;> cases h2 : (mapItems r).isEmpty <;> simp_all
        rw [h']; simp only [h, ↓reduceIte]
        rfl

namespace LawB

theorem fset_map_append_nil (s : PathSet) : s.map (fun q => ([] : Path) ++ q) = s := by
  induction s using Quotient.inductionOn with | h l =>
  exact Quotient.sound (fun x => by simp)

theorem fset_isEmpty_eq {α : Type} (s : FSet α) (h : s.isEmpty = true) : s = FSet.empty := by
  induction s using Quotient.inductionOn with | h l =>
  cases l with
  | nil => rfl
  | cons a l => simp [FSet.isEmpty, FSet.any] at h

theorem filter_none (s : PathSet) :
    s.filter (fun q => !(FSet.empty : PathSet).any (fun p => p.isPrefixOf q)) = s := by
  induction s using Quotient.inductionOn with | h l =>
  exact congrArg (Quotient.mk _) (List.filter_eq_self.2 (fun _ _ => rfl))

theorem ins_nil : ins ([] : Path) = PathSet.empty := rfl

end LawB

theorem reconOut_reconcile_law_holds : reconOut_reconcile.law := by
  intro S t s _
  unfold reconOut reconcile
  cases ht : reconTouch S t false s <;> cases hn : (atomicNodes S t s).isEmpty <;>
    simp only [hn, Bool.or_true, Bool.or_false, Bool.not_true, Bool.not_false, ite_true,
      ite_false, Bool.false_eq_true, ins_nil, empty, PathSet.union, PathSet.empty,
      fset_empty_union, fset_map_append_nil]
  rw [fset_isEmpty_eq _ hn, filter_none, fset_union_empty]

