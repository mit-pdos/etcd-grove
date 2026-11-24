/-
Pure facts about the store's abstract contents (`StoreS`, `Iface.lean`): items, `write`,
`commit`, `hasVer`, `maxCommitted`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Iface

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace github_com.despreston.go_craq

namespace StoreS

abbrev Ent := GoString × w64 × GoString × Bool

theorem mem_items (S : StoreS) (k : GoString) (e : w64 × GoString × Bool) :
    e ∈ S.items k ↔ (k, e) ∈ S := by
  unfold items
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, rfl⟩, rfl⟩; exact ha
  · intro h; exact ⟨(k, e), ⟨h, rfl⟩, rfl⟩

theorem hasVer_iff (S : StoreS) (k : GoString) (v : w64) :
    S.hasVer k v = true ↔ ∃ x c, (k, v, x, c) ∈ S := by
  unfold hasVer
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2.1, e.2.2, (mem_items S k e).1 he⟩
  · rintro ⟨x, c, h⟩
    exact ⟨(v, x, c), (mem_items S k _).2 h, rfl⟩

theorem mem_write (S : StoreS) (k x : GoString) (v : w64) (e : Ent) :
    e ∈ S.write k x v ↔ e ∈ S ∨ e = (k, v, x, false) := by
  unfold write; simp

theorem mem_commit (S : StoreS) (k : GoString) (v : w64) (e : Ent) :
    e ∈ S.commit k v ↔
      (e.1 ≠ k ∧ e ∈ S) ∨
      (∃ e0 ∈ S, e0.1 = k ∧ ¬ uint.Z e0.2.1 < uint.Z v ∧
        e = if e0.2.1 = v then (e0.1, e0.2.1, e0.2.2.1, true) else e0) := by
  unfold commit
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨e0, he0, hf⟩
    by_cases hk : e0.1 = k
    · simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte] at hf
      by_cases hv : uint.Z e0.2.1 < uint.Z v
      · simp [hv] at hf
      · simp only [hv, ↓reduceIte] at hf
        right
        refine ⟨e0, he0, hk, hv, ?_⟩
        by_cases he : e0.2.1 = v
        · simp only [he, ↓reduceIte, Option.some.injEq] at hf ⊢
          rw [← hf, hk]
        · simp only [he, ↓reduceIte, Option.some.injEq] at hf ⊢
          exact hf.symm
    · simp only [ne_eq, hk, not_false_eq_true, ↓reduceIte, Option.some.injEq] at hf
      subst hf
      left; exact ⟨hk, he0⟩
  · rintro (⟨hk, he⟩ | ⟨e0, he0, hk, hv, rfl⟩)
    · exact ⟨e, he, by simp [hk]⟩
    · refine ⟨e0, he0, ?_⟩
      simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte, hv]
      by_cases he : e0.2.1 = v
      · simp [he]
      · simp [he]

/-! ### `maxCommitted` -/

private def mcStep (m : w64) (e : w64 × GoString × Bool) : w64 :=
  if e.2.2 = true ∧ uint.Z m < uint.Z e.1 then e.1 else m

private theorem mc_fold (l : List (w64 × GoString × Bool)) (m0 : w64) :
    uint.Z m0 ≤ uint.Z (l.foldl mcStep m0) ∧
    (∀ e ∈ l, e.2.2 = true → uint.Z e.1 ≤ uint.Z (l.foldl mcStep m0)) ∧
    (l.foldl mcStep m0 = m0 ∨ ∃ x, (l.foldl mcStep m0, x, true) ∈ l) := by
  induction l generalizing m0 with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (mcStep m0 e)
    have hstep : uint.Z m0 ≤ uint.Z (mcStep m0 e) := by
      unfold mcStep; split
      · rename_i h; exact Int.le_of_lt h.2
      · exact Int.le_refl _
    refine ⟨Int.le_trans hstep h1, ?_, ?_⟩
    · intro e' he' hc
      rcases List.mem_cons.1 he' with rfl | he'
      · have : uint.Z e'.1 ≤ uint.Z (mcStep m0 e') := by
          unfold mcStep; split
          · exact Int.le_refl _
          · rename_i h
            simp only [hc, true_and] at h
            omega
        exact Int.le_trans this h1
      · exact h2 e' he' hc
    · rcases h3 with h3 | ⟨x, hx⟩
      · rw [h3]
        unfold mcStep; split
        · rename_i h
          right; refine ⟨e.2.1, ?_⟩
          rw [← h.1]; exact List.mem_cons_self
        · left; rfl
      · right; exact ⟨x, List.mem_cons_of_mem _ hx⟩

theorem maxCommitted_ub (S : StoreS) (k x : GoString) (w : w64) (h : (k, w, x, true) ∈ S) :
    uint.Z w ≤ uint.Z (S.maxCommitted k) := by
  have := (mc_fold (S.items k) (W64 0)).2.1 (w, x, true) ((mem_items S k _).2 h) rfl
  exact this

theorem maxCommitted_mem (S : StoreS) (k : GoString) :
    S.maxCommitted k = W64 0 ∨ ∃ x, (k, S.maxCommitted k, x, true) ∈ S := by
  rcases (mc_fold (S.items k) (W64 0)).2.2 with h | ⟨x, hx⟩
  · left; exact h
  · right; exact ⟨x, (mem_items S k _).1 hx⟩

theorem maxCommitted_unique (S : StoreS) (k : GoString) (m : w64)
    (hub : ∀ x w, (k, w, x, true) ∈ S → uint.Z w ≤ uint.Z m)
    (hm : m = W64 0 ∨ ∃ x, (k, m, x, true) ∈ S) : S.maxCommitted k = m := by
  have h1 : uint.Z (S.maxCommitted k) ≤ uint.Z m := by
    rcases maxCommitted_mem S k with h | ⟨x, hx⟩
    · rw [h]; word
    · exact hub x _ hx
  have h2 : uint.Z m ≤ uint.Z (S.maxCommitted k) := by
    rcases hm with h | ⟨x, hx⟩
    · rw [h]; word
    · exact maxCommitted_ub S k x m hx
  word

theorem maxCommitted_nil (k : GoString) : StoreS.maxCommitted [] k = W64 0 := rfl

theorem maxCommitted_write (S : StoreS) (k x : GoString) (v : w64) (k' : GoString) :
    (S.write k x v).maxCommitted k' = S.maxCommitted k' := by
  apply maxCommitted_unique
  · intro x' w h
    rcases (mem_write S k x v _).1 h with h | h
    · exact maxCommitted_ub S k' x' w h
    · simp at h
  · rcases maxCommitted_mem S k' with h | ⟨x', hx⟩
    · left; exact h
    · right; exact ⟨x', (mem_write S k x v _).2 (Or.inl hx)⟩

theorem maxCommitted_commit (S : StoreS) (k : GoString) (v : w64) (hv : S.hasVer k v = true)
    (k' : GoString) :
    (S.commit k v).maxCommitted k' =
      if k' = k ∧ uint.Z (S.maxCommitted k) < uint.Z v then v else S.maxCommitted k' := by
  obtain ⟨xv, cv, hmemv⟩ := (hasVer_iff S k v).1 hv
  by_cases hk : k' = k
  · subst hk
    apply maxCommitted_unique
    · intro x w h
      rcases (mem_commit S k' v _).1 h with ⟨hne, _⟩ | ⟨e0, he0, hk0, hlt, heq⟩
      · exact absurd rfl hne
      · by_cases he : e0.2.1 = v
        · simp only [he, ↓reduceIte, Prod.mk.injEq] at heq
          obtain ⟨-, rfl, -⟩ := heq
          split
          · exact Int.le_refl _
          · rename_i h; simp only [true_and] at h; omega
        · simp only [he, ↓reduceIte] at heq
          subst heq
          have := maxCommitted_ub S k' x w (by simpa using he0)
          split
          · rename_i h; exact Int.le_trans this (Int.le_of_lt h.2)
          · exact this
    · split
      · rename_i h
        right
        refine ⟨xv, (mem_commit S k' v _).2 (Or.inr ⟨(k', v, xv, cv), hmemv, rfl, by simp, ?_⟩)⟩
        simp
      · rename_i h
        simp only [true_and] at h
        rcases maxCommitted_mem S k' with h0 | ⟨x, hx⟩
        · left; exact h0
        · right
          refine ⟨x, (mem_commit S k' v _).2 (Or.inr ⟨_, hx, rfl, by simp only; omega, ?_⟩)⟩
          by_cases he : S.maxCommitted k' = v
          · simp [he]
          · simp [he]
  · simp only [hk, false_and, ↓reduceIte]
    apply maxCommitted_unique
    · intro x w h
      rcases (mem_commit S k v _).1 h with ⟨_, h⟩ | ⟨e0, _, hk0, _, heq⟩
      · exact maxCommitted_ub S k' x w h
      · exfalso
        by_cases he : e0.2.1 = v
        · simp only [he, ↓reduceIte, Prod.mk.injEq] at heq
          exact hk (heq.1.trans hk0)
        · simp only [he, ↓reduceIte] at heq
          subst heq; exact hk hk0
    · rcases maxCommitted_mem S k' with h0 | ⟨x, hx⟩
      · left; exact h0
      · right; exact ⟨x, (mem_commit S k v _).2 (Or.inl ⟨hk, hx⟩)⟩

end StoreS

end github_com.despreston.go_craq

end Perennial
