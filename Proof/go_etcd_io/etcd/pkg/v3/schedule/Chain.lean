/-
The FIFO scheduler's chain of tracked jobs (`chainOk`, `Defs.lean`): how scheduling a job (at the
end) and taking one (at the head) keep it. Lean-first (2026-10-22).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schedule

open Iris

variable [GooseExts] {GF : BundledGFunctors}

/-- An untracked job scheduled. -/
theorem chainOk_append_untracked {L : List GName} {b : Nat} {items : List (JobItem (IProp GF))}
    {it : JobItem (IProp GF)} (h : chainOk L b items) (ht : it.tr = none) :
    chainOk L b (items ++ [it]) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hf : (items ++ [it]).filterMap JobItem.tr = items.filterMap JobItem.tr := by
    simp [List.filterMap_append, ht]
  exact ⟨h1, by rw [hf]; exact h2, by rw [hf]; exact h3⟩

/-- A tracked job scheduled: its `prev` the queue's last name, its `post` appended. -/
theorem chainOk_append_tracked {Ps : List GName} {prev post : GName} {b : Nat}
    {items : List (JobItem (IProp GF))} {it : JobItem (IProp GF)}
    (h : chainOk (Ps ++ [prev]) b items) (ht : it.tr = some (prev, post)) :
    chainOk (Ps ++ [prev, post]) b (items ++ [it]) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hf : (items ++ [it]).filterMap JobItem.tr =
      items.filterMap JobItem.tr ++ [(prev, post)] := by
    simp [List.filterMap_append, ht]
  simp only [List.length_append, List.length_cons, List.length_nil] at h1 h2
  refine ⟨by simp; omega, by rw [hf]; simp; omega, ?_⟩
  intro k p hk
  rw [hf] at hk
  have hL : Ps ++ [prev, post] = (Ps ++ [prev]) ++ [post] := by simp
  rcases Nat.lt_or_ge k (items.filterMap JobItem.tr).length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hk
    obtain ⟨e1, e2⟩ := h3 k p hk
    rw [hL]
    have hb1 : b + k < (Ps ++ [prev]).length := by
      have := (List.getElem?_eq_some_iff.1 e1).1; exact this
    have hb2 : b + k + 1 < (Ps ++ [prev]).length := by
      have := (List.getElem?_eq_some_iff.1 e2).1; exact this
    rw [List.getElem?_append_left hb1, List.getElem?_append_left hb2]
    exact ⟨e1, e2⟩
  · rw [List.getElem?_append_right hge] at hk
    have hk0 : k - (items.filterMap JobItem.tr).length = 0 := by
      rcases Nat.eq_zero_or_pos (k - (items.filterMap JobItem.tr).length) with h0 | hpos
      · exact h0
      · rw [List.getElem?_eq_none (by simp; omega)] at hk; cases hk
    rw [hk0] at hk
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    have hk' : k = (items.filterMap JobItem.tr).length := by omega
    subst hk'
    have hbn : b + (items.filterMap JobItem.tr).length = Ps.length := by omega
    constructor
    · rw [hbn]; simp
    · rw [hbn]; simp

/-- The head job taken, untracked. -/
theorem chainOk_cons_untracked {L : List GName} {b : Nat} {it : JobItem (IProp GF)}
    {items : List (JobItem (IProp GF))} (h : chainOk L b (it :: items)) (ht : it.tr = none) :
    chainOk L b items := by
  obtain ⟨h1, h2, h3⟩ := h
  have hf : (it :: items).filterMap JobItem.tr = items.filterMap JobItem.tr := by
    simp [ht]
  exact ⟨h1, by rw [← hf]; exact h2, by rw [← hf]; exact h3⟩

/-- The head job taken, tracked: its names at `b` and `b + 1`, the chain on from `b + 1`. -/
theorem chainOk_cons_tracked {L : List GName} {b : Nat} {it : JobItem (IProp GF)}
    {items : List (JobItem (IProp GF))} {pv ps : GName} (h : chainOk L b (it :: items))
    (ht : it.tr = some (pv, ps)) :
    L[b]? = some pv ∧ L[b + 1]? = some ps ∧ chainOk L (b + 1) items := by
  obtain ⟨h1, h2, h3⟩ := h
  have hf : (it :: items).filterMap JobItem.tr = (pv, ps) :: items.filterMap JobItem.tr := by
    simp [ht]
  rw [hf] at h2 h3
  obtain ⟨e1, e2⟩ := h3 0 (pv, ps) (by simp)
  refine ⟨by simpa using e1, by simpa using e2, ?_, by simp at h2; omega, ?_⟩
  · have := (List.getElem?_eq_some_iff.1 e2).1; simpa using this
  · intro k p hk
    obtain ⟨f1, f2⟩ := h3 (k + 1) p (by simpa using hk)
    refine ⟨?_, ?_⟩
    · rw [show b + 1 + k = b + (k + 1) by omega]; exact f1
    · rw [show b + 1 + k + 1 = b + (k + 1) + 1 by omega]; exact f2

/-- No pending job: the chain at the queue's last index. -/
theorem chainOk_nil {L : List GName} (h : 0 < L.length) :
    chainOk L (L.length - 1) ([] : List (JobItem (IProp GF))) :=
  ⟨by omega, by simp; omega, by intro k p hk; simp at hk⟩

/-- A job appended to the pending jobs and to the items. -/
theorem pendOk_append {rs : RunSt} {js : List GoInterface} {items : List (JobItem (IProp GF))}
    {it : JobItem (IProp GF)} (h : pendOk rs js items) :
    pendOk rs (js ++ [it.j]) (items ++ [it]) := by
  unfold pendOk at *
  rcases rs with _ | _ | k | _ <;> simp only at h ⊢
  · rw [h]; simp
  · obtain ⟨h1, h2⟩ := h
    refine ⟨?_, by simp⟩
    rw [List.drop_append_of_le_length (by cases js <;> simp_all), h1]; simp
  · obtain ⟨h1, h2⟩ := h
    refine ⟨?_, by simp⟩
    rw [List.drop_append_of_le_length (by cases js <;> simp_all), h1]; simp
  · rw [h]; simp

end schedule
end EtcdGrove
end Perennial
