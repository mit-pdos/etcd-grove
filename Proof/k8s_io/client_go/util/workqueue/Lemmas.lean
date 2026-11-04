/-
Pure facts about the typed queue's abstract state (`Defs.lean`): its invariant `QState.wf` holds
initially and is preserved by `add`, by `get` of the front item, and by `done` of an item being
processed; so is `QState.allP Pk` (every item held satisfies the item predicate), `add` given
`Pk k`, and `get` gives `Pk` of the front item. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.workqueue.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open sets (Elem present)

section state
variable [GooseExts] {K : Type} [DecidableEq K]

theorem QState.init_wf : (QState.init : QState K).wf := by
  refine ⟨List.nodup_nil, fun k => ?_⟩
  simp [QState.init]

/-- `add`'s cases. -/
theorem QState.add_eq (σ : QState K) (k : K) :
    σ.add k =
      if σ.shuttingDown || (σ.dirty !! k).isSome then σ
      else if (σ.processing !! k).isSome then { σ with dirty := <[k := present]> σ.dirty }
      else { σ with dirty := <[k := present]> σ.dirty, queue := σ.queue ++ [k] } := rfl

/-- `wf` of an `add` that marks `k` dirty and queues it (`k` neither dirty nor being
processed). -/
theorem QState.wf_add_queue (σ : QState K) (k : K) (h : σ.wf)
    (hd : (σ.dirty !! k).isSome = false) (hp : (σ.processing !! k).isSome = false) :
    ({ σ with dirty := <[k := present]> σ.dirty, queue := σ.queue ++ [k] } : QState K).wf := by
  obtain ⟨hnd, hmem⟩ := h
  have hk : k ∉ σ.queue := by
    intro hin; have := (hmem k).1 hin; simp_all
  refine ⟨List.nodup_append.2 ⟨hnd, (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩), ?_⟩, fun k' => ?_⟩
  · intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hk ha
  · by_cases e : k = k'
    · subst e
      simp only [List.mem_append, List.mem_singleton, or_true, true_iff,
        GMap.lookup_insert, Option.isSome_some, true_and]
      cases hpk : σ.processing !! k <;> simp_all
    · simp only [List.mem_append, List.mem_singleton, GMap.lookup_insert_ne _ _ e]
      rw [hmem k']
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h.symm e
      · intro h; exact Or.inl h

/-- `wf` of an `add` that only marks `k` dirty (`k` not dirty, being processed). -/
theorem QState.wf_add_dirty (σ : QState K) (k : K) (h : σ.wf)
    (hp : (σ.processing !! k).isSome = true) :
    ({ σ with dirty := <[k := present]> σ.dirty } : QState K).wf := by
  obtain ⟨hnd, hmem⟩ := h
  refine ⟨hnd, fun k' => ?_⟩
  by_cases e : k = k'
  · subst e
    rw [hmem k]
    cases hpk : σ.processing !! k <;> simp_all
  · simp only [GMap.lookup_insert_ne _ _ e]
    exact hmem k'

theorem QState.add_wf (σ : QState K) (k : K) (h : σ.wf) : (σ.add k).wf := by
  rw [QState.add_eq]
  by_cases h1 : (σ.shuttingDown || (σ.dirty !! k).isSome) = true
  · rw [if_pos h1]; exact h
  · rw [if_neg h1]
    have hd : (σ.dirty !! k).isSome = false := by
      simp only [Bool.or_eq_true, not_or] at h1; simpa using h1.2
    by_cases h2 : (σ.processing !! k).isSome = true
    · rw [if_pos h2]; exact σ.wf_add_dirty k h h2
    · rw [if_neg h2]; exact σ.wf_add_queue k h hd (by simpa using h2)

/-- The front item of the queue is not being processed. -/
theorem QState.front_not_processing (σ : QState K) (k : K) (rest : List K) (h : σ.wf)
    (hq : σ.queue = k :: rest) : σ.processing !! k = none :=
  ((h.2 k).1 (by rw [hq]; exact List.mem_cons_self)).2

theorem QState.get_wf (σ : QState K) (k : K) (rest : List K) (h : σ.wf)
    (hq : σ.queue = k :: rest) : (σ.get k rest).wf := by
  obtain ⟨hnd, hmem⟩ := h
  rw [hq] at hnd hmem
  obtain ⟨hkr, hnd'⟩ := List.nodup_cons.1 hnd
  refine ⟨hnd', fun k' => ?_⟩
  simp only [QState.get]
  by_cases e : k = k'
  · subst e
    simp only [hkr, GMap.lookup_delete, Option.isSome_none, Bool.false_eq_true,
      false_and]
  · rw [GMap.lookup_delete_ne _ e, GMap.lookup_insert_ne _ _ e, ← hmem k']
    simp only [List.mem_cons]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact absurd h.symm e
      · exact h

/-- `done`'s cases. -/
theorem QState.done_eq (σ : QState K) (k : K) :
    σ.done k =
      if (σ.dirty !! k).isSome then
        { σ with processing := GMap.delete k σ.processing, queue := σ.queue ++ [k] }
      else { σ with processing := GMap.delete k σ.processing } := rfl

theorem QState.done_wf (σ : QState K) (k : K) (h : σ.wf)
    (hp : (σ.processing !! k).isSome = true) : (σ.done k).wf := by
  obtain ⟨hnd, hmem⟩ := h
  have hk : k ∉ σ.queue := by
    intro hin; have := (hmem k).1 hin; simp_all
  rw [QState.done_eq]
  by_cases hd : (σ.dirty !! k).isSome = true
  · rw [if_pos hd]
    refine ⟨List.nodup_append.2 ⟨hnd, (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩), ?_⟩, fun k' => ?_⟩
    · intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hk ha
    · by_cases e : k = k'
      · subst e
        simp only [List.mem_append, List.mem_singleton, or_true, true_iff, GMap.lookup_delete,
          and_true]
        exact hd
      · simp only [List.mem_append, List.mem_singleton, GMap.lookup_delete_ne _ e]
        rw [hmem k']
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h.symm e
        · intro h; exact Or.inl h
  · rw [if_neg hd]
    refine ⟨hnd, fun k' => ?_⟩
    by_cases e : k = k'
    · subst e
      simp only [hk, false_iff, GMap.lookup_delete, and_true]
      exact hd
    · simp only [GMap.lookup_delete_ne _ e]
      exact hmem k'

/-! ### The item predicate -/

theorem isSome_of_delete {V : Type} {m : GMap K V} {k k' : K}
    (h : (GMap.delete k m !! k').isSome) : (m !! k').isSome := by
  by_cases e : k = k'
  · subst e; simp at h
  · rwa [GMap.lookup_delete_ne _ e] at h

theorem isSome_of_insert {V : Type} {m : GMap K V} {k k' : K} {v : V}
    (h : (<[k := v]> m !! k').isSome) : k = k' ∨ (m !! k').isSome := by
  by_cases e : k = k'
  · exact Or.inl e
  · rw [GMap.lookup_insert_ne _ _ e] at h; exact Or.inr h

theorem QState.init_allP (Pk : K → Prop) : (QState.init : QState K).allP Pk := by
  intro k hk; simp [QState.init] at hk

/-- `allP` of an `add` that marks `k` dirty and queues it. -/
theorem QState.allP_add_queue {Pk : K → Prop} (σ : QState K) (k : K) (h : σ.allP Pk)
    (hk : Pk k) :
    ({ σ with dirty := <[k := present]> σ.dirty, queue := σ.queue ++ [k] } : QState K).allP Pk := by
  intro k' hk'
  rcases hk' with h1 | h1 | h1
  · rcases List.mem_append.1 h1 with h1 | h1
    · exact h k' (Or.inl h1)
    · rw [List.mem_singleton] at h1; exact h1 ▸ hk
  · rcases isSome_of_insert h1 with e | h1
    · exact e ▸ hk
    · exact h k' (Or.inr (Or.inl h1))
  · exact h k' (Or.inr (Or.inr h1))

/-- `allP` of an `add` that marks `k` dirty only. -/
theorem QState.allP_add_dirty {Pk : K → Prop} (σ : QState K) (k : K) (h : σ.allP Pk)
    (hk : Pk k) : ({ σ with dirty := <[k := present]> σ.dirty } : QState K).allP Pk := by
  intro k' hk'
  rcases hk' with h1 | h1 | h1
  · exact h k' (Or.inl h1)
  · rcases isSome_of_insert h1 with e | h1
    · exact e ▸ hk
    · exact h k' (Or.inr (Or.inl h1))
  · exact h k' (Or.inr (Or.inr h1))

/-- `allP` of `get` of the front item, which satisfies `Pk`. -/
theorem QState.get_allP {Pk : K → Prop} (σ : QState K) (k : K) (rest : List K) (h : σ.allP Pk)
    (hq : σ.queue = k :: rest) : (σ.get k rest).allP Pk ∧ Pk k := by
  have hk : Pk k := h k (Or.inl (by rw [hq]; exact List.mem_cons_self))
  refine ⟨fun k' hk' => ?_, hk⟩
  simp only [QState.get] at hk'
  rcases hk' with h1 | h1 | h1
  · exact h k' (Or.inl (by rw [hq]; exact List.mem_cons_of_mem _ h1))
  · exact h k' (Or.inr (Or.inl (isSome_of_delete h1)))
  · rcases isSome_of_insert h1 with e | h1
    · exact e ▸ hk
    · exact h k' (Or.inr (Or.inr h1))

theorem QState.done_allP {Pk : K → Prop} (σ : QState K) (k : K) (h : σ.allP Pk) :
    (σ.done k).allP Pk := by
  intro k' hk'
  rw [QState.done_eq] at hk'
  split at hk'
  · next hd =>
    rcases hk' with h1 | h1 | h1
    · rcases List.mem_append.1 h1 with h1 | h1
      · exact h k' (Or.inl h1)
      · rw [List.mem_singleton] at h1; subst h1; exact h _ (Or.inr (Or.inl hd))
    · exact h k' (Or.inr (Or.inl h1))
    · exact h k' (Or.inr (Or.inr (isSome_of_delete h1)))
  · rcases hk' with h1 | h1 | h1
    · exact h k' (Or.inl h1)
    · exact h k' (Or.inr (Or.inl h1))
    · exact h k' (Or.inr (Or.inr (isSome_of_delete h1)))

end state

end workqueue
end EtcdGrove
end Perennial
