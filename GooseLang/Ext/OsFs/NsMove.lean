/-
Laws of `nsMove` (`Names.lean`), the effect on the namespace of a directory's rename: the keys
under the source moved under the target. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsView

@[expose] public section

noncomputable section

namespace Perennial

theorem lookup_ofList_cons {K V : Type} [DecidableEq K] (k : K) (v : V) (l : List (K × V)) (y : K) :
    GMap.ofList ((k, v) :: l) !! y = if k = y then some v else GMap.ofList l !! y := by
  show (<[k := v]> (GMap.ofList l)) !! y = _
  by_cases h : k = y
  · subst h; rw [GMap.lookup_insert]; simp
  · rw [GMap.lookup_insert_ne _ _ h]; simp [h]

/-- A list's map, looked up: the first binding of the key. -/
theorem lookup_ofList {K V : Type} [DecidableEq K] (l : List (K × V)) (y : K) :
    GMap.ofList l !! y = (l.find? (fun kv => decide (kv.1 = y))).map (·.2) := by
  induction l with
  | nil => rfl
  | cons kv l ih =>
    obtain ⟨k, v⟩ := kv
    rw [lookup_ofList_cons, ih]
    by_cases h : k = y
    · simp [h]
    · simp [h]

open Classical in
/-- A map's bindings with the keys changed by `f`, injective on its keys, looked up. -/
theorem lookup_ofList_rekey {K V : Type} [DecidableEq K] (m : GMap K V) (f : K → K)
    (hinj : ∀ x x', (m !! x).isSome → (m !! x').isSome → f x = f x' → x = x') (y : K) :
    GMap.ofList (m.toList.map (fun kv => (f kv.1, kv.2))) !! y =
      if h : ∃ x, (m !! x).isSome ∧ f x = y then m !! h.choose else none := by
  rw [lookup_ofList]
  split
  · rename_i h
    obtain ⟨hx1, hx2⟩ := h.choose_spec
    generalize hx : h.choose = x at hx1 hx2
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hx1
    rw [hv]
    have hmem : (f x, v) ∈ m.toList.map (fun kv => (f kv.1, kv.2)) :=
      List.mem_map.2 ⟨(x, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
    cases hf : (m.toList.map (fun kv => (f kv.1, kv.2))).find? (fun kv => decide (kv.1 = y)) with
    | none =>
      have := List.find?_eq_none.1 hf (f x, v) hmem
      simp [hx2] at this
    | some kv =>
      obtain ⟨hkv1, hkv2⟩ := List.find?_eq_some_iff_append.1 hf |>.imp id (fun _ => trivial)
      have hmem' := List.mem_of_find?_eq_some hf
      obtain ⟨⟨x', v'⟩, hx', rfl⟩ := List.mem_map.1 hmem'
      have hx'm : m !! x' = some v' := (GMap.mem_toList _ _ _).1 hx'
      simp only [decide_eq_true_eq] at hkv1
      have : x' = x := hinj x' x (by rw [hx'm]; rfl) hx1 (by rw [hkv1, hx2])
      subst this
      rw [hv] at hx'm; cases hx'm
      rfl
  · rename_i h
    cases hf : (m.toList.map (fun kv => (f kv.1, kv.2))).find? (fun kv => decide (kv.1 = y)) with
    | none => rfl
    | some kv =>
      have hmem' := List.mem_of_find?_eq_some hf
      obtain ⟨⟨x', v'⟩, hx', rfl⟩ := List.mem_map.1 hmem'
      have := List.find?_some hf
      simp only [decide_eq_true_eq] at this
      exact absurd ⟨x', by rw [(GMap.mem_toList _ _ _).1 hx']; rfl, this⟩ h

/-! ## Re-keying a tree -/

theorem isUnder_iff (s x : GoString) : IsUnder s x ↔ ∃ r, x = s ++ r ∧ (r = [] ∨ ∃ r', r = slashB :: r') := by
  unfold IsUnder
  constructor
  · rintro (rfl | ⟨r', rfl⟩)
    · exact ⟨[], by simp, .inl rfl⟩
    · exact ⟨slashB :: r', by simp, .inr ⟨r', rfl⟩⟩
  · rintro ⟨r, rfl, rfl | ⟨r', rfl⟩⟩
    · left; simp
    · right; exact ⟨r', by simp⟩

theorem rekey_under {s t x : GoString} (h : IsUnder s x) :
    rekey s t x = t ++ x.drop s.length ∧ IsUnder t (t ++ x.drop s.length) := by
  refine ⟨by simp [rekey, h], ?_⟩
  obtain ⟨r, rfl, hr⟩ := (isUnder_iff s x).1 h
  rw [(isUnder_iff t _)]
  exact ⟨r, by simp, hr⟩

theorem rekey_not_under {s t x : GoString} (h : ¬ IsUnder s x) : rekey s t x = x := by
  simp [rekey, h]

/-- The keys of `m` re-keyed from `s` to `t`, nothing of `m` at or under `t`: injective. -/
theorem rekey_inj {m : NsMap} {s t : GoString} (ht : ∀ x, (m !! x).isSome → ¬ IsUnder t x) :
    ∀ x x', (m !! x).isSome → (m !! x').isSome → rekey s t x = rekey s t x' → x = x' := by
  intro x x' hx hx' he
  by_cases h1 : IsUnder s x <;> by_cases h2 : IsUnder s x'
  · rw [(rekey_under (t := t) h1).1, (rekey_under (t := t) h2).1] at he
    have hd := List.append_cancel_left he
    obtain ⟨r1, rfl, -⟩ := (isUnder_iff s x).1 h1
    obtain ⟨r2, rfl, -⟩ := (isUnder_iff s x').1 h2
    simp at hd; rw [hd]
  · rw [(rekey_under (t := t) h1).1, rekey_not_under h2] at he
    exact absurd (he ▸ (rekey_under (t := t) h1).2) (ht x' hx')
  · rw [rekey_not_under h1, (rekey_under (t := t) h2).1] at he
    exact absurd (he.symm ▸ (rekey_under (t := t) h2).2) (ht x hx)
  · rw [rekey_not_under h1, rekey_not_under h2] at he; exact he

/-- **A tree moved**, looked up under its new place: what was under the old. -/
theorem nsMove_under {m : NsMap} {s t : GoString} (ht : ∀ x, (m !! x).isSome → ¬ IsUnder t x)
    (r : GoString) (hr : r = [] ∨ ∃ r', r = slashB :: r') :
    nsMove m s t !! (t ++ r) = m !! (s ++ r) := by
  unfold nsMove
  rw [lookup_ofList_rekey m (rekey s t) (rekey_inj ht)]
  have hu : IsUnder s (s ++ r) := (isUnder_iff s _).2 ⟨r, rfl, hr⟩
  have hk : rekey s t (s ++ r) = t ++ r := by rw [(rekey_under hu).1]; simp
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h.choose_spec
    by_cases hm : (m !! (s ++ r)).isSome
    · rw [rekey_inj ht _ _ h1 hm (by rw [h2, hk])]
    · exfalso
      by_cases hs : IsUnder s h.choose
      · rw [(rekey_under hs).1] at h2
        obtain ⟨r1, he, -⟩ := (isUnder_iff s _).1 hs
        rw [he] at h1 h2
        simp at h2; rw [h2] at h1; exact hm h1
      · rw [rekey_not_under hs] at h2
        exact ht _ h1 (by rw [h2]; exact (isUnder_iff t _).2 ⟨r, rfl, hr⟩)
  · rename_i h
    cases hm : m !! (s ++ r) with
    | none => rfl
    | some v => exact absurd ⟨s ++ r, by rw [hm]; rfl, hk⟩ h

/-- ... elsewhere than under the old place or the new: as it was. -/
theorem nsMove_other {m : NsMap} {s t : GoString} (ht : ∀ x, (m !! x).isSome → ¬ IsUnder t x)
    (y : GoString) (hs : ¬ IsUnder s y) (hty : ¬ IsUnder t y) : nsMove m s t !! y = m !! y := by
  unfold nsMove
  rw [lookup_ofList_rekey m (rekey s t) (rekey_inj ht)]
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h.choose_spec
    by_cases hc : IsUnder s h.choose
    · exact absurd (h2 ▸ (rekey_under hc).1 ▸ (rekey_under (t := t) hc).2) hty
    · rw [rekey_not_under hc] at h2; rw [h2]
  · rename_i h
    cases hm : m !! y with
    | none => rfl
    | some v => exact absurd ⟨y, by rw [hm]; rfl, rekey_not_under hs⟩ h

/-- ... under the old place but not the new: nothing. -/
theorem nsMove_old {m : NsMap} {s t : GoString} (ht : ∀ x, (m !! x).isSome → ¬ IsUnder t x)
    (y : GoString) (hs : IsUnder s y) (hty : ¬ IsUnder t y) : nsMove m s t !! y = none := by
  unfold nsMove
  rw [lookup_ofList_rekey m (rekey s t) (rekey_inj ht)]
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := h.choose_spec
    by_cases hc : IsUnder s h.choose
    · exact absurd (h2 ▸ (rekey_under hc).1 ▸ (rekey_under (t := t) hc).2) hty
    · rw [rekey_not_under hc] at h2; exact absurd (by rw [h2]; exact hs) hc
  · rfl

/-! ## Nothing under an absent path -/

theorem split_last_slash (r : GoString) :
    slashB ∉ r ∨ ∃ a b, r = a ++ slashB :: b ∧ slashB ∉ b := by
  induction r with
  | nil => left; simp
  | cons c l ih =>
    rcases ih with h | ⟨a, b, rfl, hb⟩
    · by_cases hc : c = slashB
      · subst hc; right; exact ⟨[], l, by simp, h⟩
      · left; simp [h, Ne.symm hc]
    · right; exact ⟨c :: a, b, by simp, hb⟩

/-- In a namespace of the shape `NsShape` (every name's parent a directory), nothing is under a path
that is absent (and has no root under it). -/
theorem shape_no_under {R : List GoString} {m : NsMap} {t : GoString} (hs : NsShape R m)
    (ht : m !! t = none) (hR : ∀ r ∈ R, ¬ IsUnder t r) : ∀ x, (m !! x).isSome → ¬ IsUnder t x := by
  suffices h : ∀ n x, x.length ≤ n → (m !! x).isSome → ¬ IsUnder t x from
    fun x => h x.length x (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro x hl hx hu
    obtain ⟨r, rfl, hr⟩ := (isUnder_iff t x).1 hu
    rcases hr with rfl | ⟨r', rfl⟩
    · rw [List.append_nil, ht] at hx; cases hx
    · simp at hl
  | succ n ih =>
    intro x hl hx hu
    obtain ⟨r, rfl, hr⟩ := (isUnder_iff t x).1 hu
    rcases hr with rfl | ⟨r', rfl⟩
    · rw [List.append_nil, ht] at hx; cases hx
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hx
    rcases hs.2.1 _ v hv with hroot | ⟨-, d, hd, hdir⟩
    · exact hR _ hroot hu
    rcases split_last_slash r' with hns | ⟨a, b, rfl, hb⟩
    · rw [parentOf_child t r' hns] at hd; cases hd
      rw [ht] at hdir; cases hdir
    · have he : t ++ slashB :: (a ++ slashB :: b) = (t ++ slashB :: a) ++ slashB :: b := by simp
      rw [he, parentOf_child _ b hb] at hd; cases hd
      have hlt : (t ++ slashB :: a).length ≤ n := by simp at hl ⊢; omega
      exact ih (t ++ slashB :: a) hlt (by rw [hdir]; rfl)
        ((isUnder_iff t _).2 ⟨slashB :: a, rfl, .inr ⟨a, rfl⟩⟩)

end Perennial

end
