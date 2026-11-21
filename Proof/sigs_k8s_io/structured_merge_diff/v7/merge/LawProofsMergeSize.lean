/-
**Merging adds no node** (`merge_size`, `merge/Laws.lean`): for conforming sides of a schema in
scope, `merge`'s size is at most the two sides' together. A list's merged items are one per key of
`mergeKeys` (distinct: `mergeKeys_nodup`, from the sides' distinct keys, which conformance gives
for an associative list, the only granular kind in scope), each the merge of at most one item of
each side; a map's are one per triple of `zipLexical`, which uses each entry of each side once.
Prove phase (2026-11-21).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace MSize

/-- The size of an optional value (`none`: nothing). -/
def sizeO : Option UVal → Nat
  | none => 0
  | some v => v.size

/-- An optional value conforms (`none` does). -/
def confO (S : Schema) (t : TypeRef) : Option UVal → Prop
  | none => True
  | some v => conforms S t v

theorem size_pos (x : UVal) : 1 ≤ x.size := by
  cases x <;> simp [UVal.size]

theorem fm_sizeL {β : Type} (h : β → Nat) (g : β → Option UVal) :
    ∀ (T : List β), (∀ x ∈ T, sizeO (g x) ≤ h x) → UVal.sizeL (T.filterMap g) ≤ (T.map h).sum
  | [], _ => by simp [UVal.sizeL]
  | x :: T, hg => by
    have ih := fm_sizeL h g T (fun y hy => hg y (List.mem_cons_of_mem _ hy))
    have hx := hg x List.mem_cons_self
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases hgx : g x with
    | none => simp only; omega
    | some v => simp only [UVal.sizeL]; rw [hgx] at hx; simp only [sizeO] at hx; omega

theorem fm_sizeM {β : Type} (h : β → Nat) (g : β → Option (GoString × UVal)) :
    ∀ (T : List β), (∀ x ∈ T, sizeO ((g x).map Prod.snd) ≤ h x) →
      UVal.sizeM (T.filterMap g) ≤ (T.map h).sum
  | [], _ => by simp [UVal.sizeM]
  | x :: T, hg => by
    have ih := fm_sizeM h g T (fun y hy => hg y (List.mem_cons_of_mem _ hy))
    have hx := hg x List.mem_cons_self
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases hgx : g x with
    | none => simp only; omega
    | some kv =>
      obtain ⟨k, v⟩ := kv
      simp only [UVal.sizeM]; rw [hgx] at hx; simp only [Option.map, sizeO] at hx; omega


theorem split_sum (g : PE → Nat) (k : Option PE) (c : Nat) :
    ∀ (P : List PE), P.Nodup →
      (P.map (fun pe => if k = some pe then c else g pe)).sum ≤
        c + ((P.filter (fun pe => decide (k ≠ some pe))).map g).sum
  | [], _ => by simp
  | pe :: P, hP => by
    have hP' := List.nodup_cons.1 hP
    have ih := split_sum g k c P hP'.2
    by_cases h : k = some pe
    · have hall : ∀ q ∈ P, k ≠ some q := by
        intro q hq hk; rw [h] at hk; cases hk; exact hP'.1 hq
      have e1 : (P.map (fun pe => if k = some pe then c else g pe)) = P.map g :=
        List.map_congr_left (fun q hq => by simp [hall q hq])
      have e2 : P.filter (fun pe => decide (k ≠ some pe)) = P :=
        List.filter_eq_self.2 (fun q hq => decide_eq_true (hall q hq))
      simp only [List.map_cons, List.sum_cons, List.filter_cons, h, ne_eq,
        not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      rw [← h, e1, e2]
      exact Nat.le_refl _
    · rw [List.map_cons, List.sum_cons, List.filter_cons_of_pos (by simp [h]), List.map_cons,
        List.sum_cons]
      have : (if k = some pe then c else g pe) = g pe := by simp [h]
      omega

theorem zero_sum (P : List PE) : (P.map (fun _ => (0 : Nat))).sum = 0 := by
  induction P <;> simp_all

/-- Distinct keys pick distinct items: the items of `vs` at the keys `P` count at most `vs`. -/
theorem itemOf_sum (ks : List GoString) :
    ∀ (vs : List UVal) (P : List PE), P.Nodup →
      (P.map (fun pe => sizeO (itemOf ks vs pe))).sum ≤ UVal.sizeL vs
  | [], P, _ => by
    have : (fun pe => sizeO (itemOf ks [] pe)) = fun _ => 0 := by
      funext pe; simp [itemOf, sizeO]
    rw [this, zero_sum]; exact Nat.zero_le _
  | v :: vs, P, hP => by
    have hstep : (fun pe => sizeO (itemOf ks (v :: vs) pe)) =
        fun pe => if keyOf ks v = some pe then v.size else sizeO (itemOf ks vs pe) := by
      funext pe
      unfold itemOf
      simp only [List.find?_cons]
      by_cases h : keyOf ks v = some pe
      · simp [h, sizeO]
      · simp [h]
    rw [hstep]
    have h1 := split_sum (fun pe => sizeO (itemOf ks vs pe)) (keyOf ks v) v.size P hP
    have h2 := itemOf_sum ks vs _ (hP.filter (fun pe => decide (keyOf ks v ≠ some pe)))
    simp only [UVal.sizeL]
    omega

theorem zsum_l : ∀ (xs : List (GoString × UVal)),
    ((xs.map (fun (x : GoString × UVal) => ((x.1, some x.2, none) : GoString × Option UVal × Option UVal))).map
      (fun x => sizeO x.2.1 + sizeO x.2.2)).sum = UVal.sizeM xs
  | [] => by simp [UVal.sizeM]
  | (k, v) :: xs => by
    have := zsum_l xs
    simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢; omega

theorem zsum_r : ∀ (ys : List (GoString × UVal)),
    ((ys.map (fun (x : GoString × UVal) => ((x.1, none, some x.2) : GoString × Option UVal × Option UVal))).map
      (fun x => sizeO x.2.1 + sizeO x.2.2)).sum = UVal.sizeM ys
  | [] => by simp [UVal.sizeM]
  | (k, v) :: ys => by
    have := zsum_r ys
    simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢; omega

/-- `zipLexical` uses each entry of each side once. -/
theorem zip_sum : ∀ (n : Nat) (xs ys : List (GoString × UVal)),
    ((zipLexical n xs ys).map (fun x => sizeO x.2.1 + sizeO x.2.2)).sum ≤
      UVal.sizeM xs + UVal.sizeM ys
  | 0, xs, ys => by simp [zipLexical]
  | n + 1, [], [] => by simp [zipLexical]
  | n + 1, (k, a) :: xs, [] => by
    have := zsum_l xs
    simp only [zipLexical, List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢; omega
  | n + 1, [], (k, b) :: ys => by
    have := zsum_r ys
    simp only [zipLexical, List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢; omega
  | n + 1, (k, a) :: xs, (k', b) :: ys => by
    simp only [zipLexical]
    split
    · have := zip_sum n xs ys
      simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢; omega
    · split
      · have := zip_sum n xs ((k', b) :: ys)
        simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢; omega
      · have := zip_sum n ((k, a) :: xs) ys
        simp only [List.map_cons, List.sum_cons, UVal.sizeM, sizeO] at this ⊢; omega

/-- A triple of `zipLexical` holds entries of its sides. -/
theorem zip_mem : ∀ (n : Nat) (xs ys : List (GoString × UVal)) (k : GoString)
    (a b : Option UVal), (k, a, b) ∈ zipLexical n xs ys →
      (∀ v, a = some v → (k, v) ∈ xs) ∧ (∀ v, b = some v → (k, v) ∈ ys)
  | 0, xs, ys, k, a, b, h => by simp [zipLexical] at h
  | n + 1, [], [], k, a, b, h => by simp [zipLexical] at h
  | n + 1, (k0, a0) :: xs, [], k, a, b, h => by
    simp only [zipLexical, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨k1, a1⟩, h1, h2⟩
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl, rfl⟩ := h2
      simp [h1]
  | n + 1, [], (k0, b0) :: ys, k, a, b, h => by
    simp only [zipLexical, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨k1, b1⟩, h1, h2⟩
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp
    · simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl, rfl⟩ := h2
      simp [h1]
  | n + 1, (k0, a0) :: xs, (k1, b1) :: ys, k, a, b, h => by
    simp only [zipLexical] at h
    split at h
    · rename_i hk
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; subst hk; simp
      · obtain ⟨h1, h2⟩ := zip_mem n xs ys k a b h
        exact ⟨fun v hv => List.mem_cons_of_mem _ (h1 v hv),
          fun v hv => List.mem_cons_of_mem _ (h2 v hv)⟩
    · split at h
      · rcases List.mem_cons.1 h with h | h
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp
        · obtain ⟨h1, h2⟩ := zip_mem n xs ((k1, b1) :: ys) k a b h
          exact ⟨fun v hv => List.mem_cons_of_mem _ (h1 v hv), h2⟩
      · rcases List.mem_cons.1 h with h | h
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp
        · obtain ⟨h1, h2⟩ := zip_mem n ((k0, a0) :: xs) ys k a b h
          exact ⟨h1, fun v hv => List.mem_cons_of_mem _ (h2 v hv)⟩

theorem conformsL_mem (S : Schema) (e : TypeRef) :
    ∀ (vs : List UVal), conformsL S e vs = true → ∀ v ∈ vs, conforms S e v
  | [], _, v, hv => by simp at hv
  | w :: vs, h, v, hv => by
    simp only [conformsL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hv with rfl | hv
    · exact h.1
    · exact conformsL_mem S e vs h.2 v hv

theorem conformsM_mem (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) :
    ∀ (kvs : List (GoString × UVal)), conformsM S fs e kvs = true → ∀ k v, (k, v) ∈ kvs →
      ∃ t, fieldType fs e k = some t ∧ conforms S t v
  | [], _, k, v, hv => by simp at hv
  | (k', w) :: kvs, h, k, v, hv => by
    simp only [conformsM, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hv with hv | hv
    · simp only [Prod.mk.injEq] at hv; obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨h1, -⟩ := h
      split at h1
      · rename_i t ht; exact ⟨t, ht, h1⟩
      · cases h1
    · exact conformsM_mem S fs e kvs h.2 k v hv

theorem itemOf_conf (S : Schema) (e : TypeRef) (ks : List GoString) (vs : List UVal)
    (h : conformsL S e vs = true) (pe : PE) : confO S e (itemOf ks vs pe) := by
  unfold itemOf
  cases hf : vs.find? (fun v => decide (keyOf ks v = some pe)) with
  | none => trivial
  | some v => exact conformsL_mem S e vs h v (List.mem_of_find?_eq_some hf)

/-- A list's items, from a conforming optional value of a list type. -/
theorem listItems_conf (S : Schema) (t e : TypeRef) (rel : ElemRel) (ks : List GoString)
    (ht : S.find t.name = some (.list e rel ks)) (x : Option UVal) (hx : confO S t x) :
    conformsL S e (listItems x) = true ∧
      (rel = .associative → (keysOf ks (listItems x)).Nodup) ∧
      (listItems x ≠ [] → UVal.sizeL (listItems x) + 1 ≤ sizeO x) ∧
      UVal.sizeL (listItems x) ≤ sizeO x := by
  match x, hx with
  | none, _ => simp [listItems, conformsL, keysOf, UVal.sizeL, sizeO]
  | some (.list vs), hx =>
    simp only [confO, conforms, conformsB, ht, Bool.and_eq_true] at hx
    simp only [listItems, sizeO, UVal.size]
    refine ⟨hx.1, fun hr => ?_, fun _ => Nat.le_refl _, Nat.le_succ _⟩
    rw [hr] at hx
    simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact hx.2.2
  | some .null, _ => simp [listItems, conformsL, keysOf, UVal.sizeL, sizeO]
  | some (.bool _), _ => simp [listItems, conformsL, keysOf, UVal.sizeL, sizeO]
  | some (.int _), _ => simp [listItems, conformsL, keysOf, UVal.sizeL, sizeO]
  | some (.str _), _ => simp [listItems, conformsL, keysOf, UVal.sizeL, sizeO]
  | some (.map _), hx =>
    simp only [confO, conforms, conformsB, ht] at hx; cases hx

/-- A map's entries, from a conforming optional value of a map type. -/
theorem mapItems_conf (S : Schema) (t : TypeRef) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (ht : S.find t.name = some (.map fs e rel))
    (x : Option UVal) (hx : confO S t x) :
    conformsM S fs e (mapItems x) = true ∧
      (mapItems x ≠ [] → UVal.sizeM (mapItems x) + 1 ≤ sizeO x) ∧
      UVal.sizeM (mapItems x) ≤ sizeO x := by
  match x, hx with
  | none, _ => simp [mapItems, conformsM, UVal.sizeM, sizeO]
  | some (.map kvs), hx =>
    simp only [confO, conforms, conformsB, ht] at hx
    simp only [mapItems, sizeO, UVal.size]
    exact ⟨hx, fun _ => Nat.le_refl _, Nat.le_succ _⟩
  | some .null, _ => simp [mapItems, conformsM, UVal.sizeM, sizeO]
  | some (.bool _), _ => simp [mapItems, conformsM, UVal.sizeM, sizeO]
  | some (.int _), _ => simp [mapItems, conformsM, UVal.sizeM, sizeO]
  | some (.str _), _ => simp [mapItems, conformsM, UVal.sizeM, sizeO]
  | some (.list _), hx =>
    simp only [confO, conforms, conformsB, ht] at hx; cases hx

theorem sum_map_add {β : Type} (f g : β → Nat) :
    ∀ (P : List β), (P.map (fun x => f x + g x)).sum = (P.map f).sum + (P.map g).sum
  | [] => by simp
  | x :: P => by have := sum_map_add f g P; simp only [List.map_cons, List.sum_cons]; omega

theorem ne_of_not_both {α : Type} (a b : List α) (h : ¬ (a.isEmpty = true ∧ b.isEmpty = true)) :
    a ≠ [] ∨ b ≠ [] := by
  cases a with
  | nil => cases b with
    | nil => exact absurd ⟨rfl, rfl⟩ h
    | cons _ _ => exact Or.inr (List.cons_ne_nil _ _)
  | cons _ _ => exact Or.inl (List.cons_ne_nil _ _)

theorem leafM_size (l r : Option UVal) : sizeO (leafM l r) ≤ sizeO l + sizeO r := by
  cases l <;> cases r <;> simp [leafM, sizeO]

/-- **`mergeF` adds no node** (conforming sides, a schema in scope). -/
theorem mergeF_size (S : Schema) (hS : S.WF) :
    ∀ (n : Nat) (t : TypeRef) (l r : Option UVal), confO S t l → confO S t r →
      sizeO (mergeF n S t l r) ≤ sizeO l + sizeO r
  | 0, t, l, r, _, _ => by simp [mergeF, sizeO]
  | n + 1, t, l, r, hl, hr => by
    unfold mergeF
    split
    · exact leafM_size l r
    · rename_i e rel ks ht
      split
      · exact leafM_size l r
      · rename_i hne
        obtain ⟨hcl, hkl, hnl, hsl⟩ := listItems_conf S t e rel ks ht l hl
        obtain ⟨hcr, hkr, hnr, hsr⟩ := listItems_conf S t e rel ks ht r hr
        have hrel : rel = .associative := by
          have := LawB.list_wf S hS t e rel ks ht (fun h => hne (Or.inl h))
          exact this.1
        have hP := LawB.mergeKeys_nodup _ _ (hkl hrel) (hkr hrel)
        dsimp only
        generalize mergeKeys (keysOf ks (listItems l)) (keysOf ks (listItems r)) = P at hP ⊢
        have hsum := fm_sizeL (fun pe => sizeO (itemOf ks (listItems l) pe) +
            sizeO (itemOf ks (listItems r) pe))
          (fun pe => mergeF n S e (itemOf ks (listItems l) pe) (itemOf ks (listItems r) pe)) P
          (fun pe _ => mergeF_size S hS n e _ _ (itemOf_conf S e ks _ hcl pe)
            (itemOf_conf S e ks _ hcr pe))
        rw [sum_map_add] at hsum
        have h1 := itemOf_sum ks (listItems l) P hP
        have h2 := itemOf_sum ks (listItems r) P hP
        split
        · simp [sizeO]
        · show UVal.sizeL _ + 1 ≤ sizeO l + sizeO r
          have hne' : listItems l ≠ [] ∨ listItems r ≠ [] :=
            ne_of_not_both _ _ (fun h => hne (Or.inr h))
          rcases hne' with h | h
          · have := hnl h; omega
          · have := hnr h; omega
    · rename_i fs e rel ht
      split
      · exact leafM_size l r
      · rename_i hne
        obtain ⟨hcl, hnl, hsl⟩ := mapItems_conf S t fs e rel ht l hl
        obtain ⟨hcr, hnr, hsr⟩ := mapItems_conf S t fs e rel ht r hr
        dsimp only
        have hTm := zip_mem ((mapItems l).length + (mapItems r).length + 1) (mapItems l) (mapItems r)
        have hz := zip_sum ((mapItems l).length + (mapItems r).length + 1) (mapItems l) (mapItems r)
        generalize zipLexical ((mapItems l).length + (mapItems r).length + 1) (mapItems l)
          (mapItems r) = T at hTm hz ⊢
        have hne' : mapItems l ≠ [] ∨ mapItems r ≠ [] :=
          ne_of_not_both _ _ (fun h => hne (Or.inr h))
        split
        · simp [sizeO]
        · show UVal.sizeM _ + 1 ≤ sizeO l + sizeO r
          refine Nat.le_trans (Nat.succ_le_succ (fm_sizeM (fun x : GoString × Option UVal × Option UVal =>
            sizeO x.2.1 + sizeO x.2.2) _ T ?_)) ?_
          · intro x hx
            obtain ⟨k, a, b⟩ := x
            obtain ⟨ha, hb⟩ := hTm k a b hx
            simp only
            split
            · rename_i t' ht'
              have hca : confO S t' a := by
                cases a with
                | none => trivial
                | some v =>
                  obtain ⟨t'', h1, h2⟩ := conformsM_mem S fs e _ hcl k v (ha v rfl)
                  rw [ht'] at h1; cases h1; exact h2
              have hcb : confO S t' b := by
                cases b with
                | none => trivial
                | some v =>
                  obtain ⟨t'', h1, h2⟩ := conformsM_mem S fs e _ hcr k v (hb v rfl)
                  rw [ht'] at h1; cases h1; exact h2
              have := mergeF_size S hS n t' a b hca hcb
              cases hm : mergeF n S t' a b with
              | none => simp [sizeO]
              | some v => rw [hm] at this; simpa [sizeO] using this
            · simp [sizeO]
          · rcases hne' with h | h
            · have := hnl h; omega
            · have := hnr h; omega
    · simp [sizeO]

end MSize

/-- **`merge` adds no node** (`merge_size`). -/
theorem merge_size_law_holds : merge_size.law := by
  intro S t l r hS hl hr
  unfold merge
  have := MSize.mergeF_size S hS (l.size + r.size + 1) t (some l) (some r) hl hr
  have hl1 := MSize.size_pos l
  cases hm : mergeF (l.size + r.size + 1) S t (some l) (some r) with
  | none => simp [UVal.size]; omega
  | some v => rw [hm] at this; simpa [MSize.sizeO] using this

end smd
end EtcdGrove
end Perennial
