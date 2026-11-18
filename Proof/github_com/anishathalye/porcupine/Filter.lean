/-
Lean-first (no Rocq counterpart).

# Linearizability through a filter and a simulation (k8s 7g step 4, B2)

A history `h` of operations `α`, linearized by `π` for a model `M`, and a partial map `f : α → Option β`
of its operations to another model's (`none`: dropped). If a relation `R` between the two models' states
holds initially and every operation of `h` keeps it (a dropped one leaves the second model's state, a kept
one is a step of the second model), then the kept operations (`fmapH f h`, each with its interval) are
linearized by `π`'s kept indices, renumbered (`π.filterMap (fidx f h)`).

- `fmapH f h`, `fidx f h k` (the index of `h`'s operation `k` in `fmapH f h`, if kept);
- `fidx_get`, `fidx_surj`, `fidx_inj`: `fidx` is a bijection from the kept indices to `fmapH f h`'s;
- **`isLinearization_filter`**.
-/
module

public import Proof.github_com.anishathalye.porcupine.Theory

@[expose] public section

namespace Perennial
namespace github_com.anishathalye.porcupine
namespace Theory

variable {σ σ' α β : Type}

/-- The operations of `h` that `f` keeps, mapped, with their intervals. -/
def fmapH (f : α → Option β) (h : List (Op α)) : List (Op β) :=
  h.filterMap fun o => (f o.val).map fun b => ⟨b, o.call, o.ret⟩

/-- The index in `fmapH f h` of `h`'s operation `k`, if `f` keeps it: the number of kept operations
before it. -/
def fidx (f : α → Option β) (h : List (Op α)) (k : Nat) : Option Nat :=
  match h[k]? with
  | some o => if (f o.val).isSome then some (fmapH f (h.take k)).length else none
  | none => none

theorem fmapH_cons (f : α → Option β) (a : Op α) (t : List (Op α)) :
    fmapH f (a :: t) =
      ((f a.val).map fun b => (⟨b, a.call, a.ret⟩ : Op β)).toList ++ fmapH f t := by
  unfold fmapH; rw [List.filterMap_cons]; cases f a.val <;> rfl

theorem fidx_cons_zero (f : α → Option β) (a : Op α) (t : List (Op α)) :
    fidx f (a :: t) 0 = if (f a.val).isSome then some 0 else none := by
  simp [fidx, fmapH]

theorem fidx_cons_succ (f : α → Option β) (a : Op α) (t : List (Op α)) (k : Nat) :
    fidx f (a :: t) (k + 1) = (fidx f t k).map (· + if (f a.val).isSome then 1 else 0) := by
  unfold fidx
  simp only [List.getElem?_cons_succ, List.take_succ_cons, fmapH_cons]
  cases t[k]? with
  | none => rfl
  | some o =>
    simp only
    split
    · cases f a.val <;> simp [Nat.add_comm]
    · rfl

/-- A kept index's operation is `fmapH`'s at its new index. -/
theorem fidx_get (f : α → Option β) : ∀ (h : List (Op α)) (k n : Nat), fidx f h k = some n →
    ∃ o b, h[k]? = some o ∧ f o.val = some b ∧ (fmapH f h)[n]? = some ⟨b, o.call, o.ret⟩
  | [], k, n, e => by simp [fidx] at e
  | a :: t, 0, n, e => by
    rw [fidx_cons_zero] at e
    split at e
    · rename_i hs
      cases e
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨a, b, rfl, hb, by rw [fmapH_cons, hb]; rfl⟩
    · cases e
  | a :: t, k + 1, n, e => by
    rw [fidx_cons_succ] at e
    cases hm : fidx f t k with
    | none => rw [hm] at e; cases e
    | some m =>
      rw [hm] at e
      simp only [Option.map, Option.some.injEq] at e
      subst e
      obtain ⟨o, b, ho, hb, hg⟩ := fidx_get f t k m hm
      refine ⟨o, b, by simpa using ho, hb, ?_⟩
      rw [fmapH_cons]
      cases hf : f a.val
      · simpa using hg
      · simpa using hg

/-- Every operation of `fmapH f h` is a kept one's. -/
theorem fidx_surj (f : α → Option β) : ∀ (h : List (Op α)) (n : Nat) (ob : Op β),
    (fmapH f h)[n]? = some ob → ∃ k, fidx f h k = some n
  | [], n, ob, e => by simp [fmapH] at e
  | a :: t, n, ob, e => by
    rw [fmapH_cons] at e
    cases hf : f a.val with
    | none =>
      rw [hf] at e
      simp only [Option.map_none, Option.toList_none, List.nil_append] at e
      obtain ⟨k, hk⟩ := fidx_surj f t n ob e
      exact ⟨k + 1, by rw [fidx_cons_succ, hk]; simp [hf]⟩
    | some b =>
      cases n with
      | zero => exact ⟨0, by rw [fidx_cons_zero]; simp [hf]⟩
      | succ n =>
        rw [hf] at e
        simp only [Option.map_some, Option.toList_some, List.singleton_append,
          List.getElem?_cons_succ] at e
        obtain ⟨k, hk⟩ := fidx_surj f t n ob e
        exact ⟨k + 1, by rw [fidx_cons_succ, hk]; simp [hf]⟩

/-- `fidx` is injective on the kept indices. -/
theorem fidx_inj (f : α → Option β) : ∀ (h : List (Op α)) (k k' n : Nat),
    fidx f h k = some n → fidx f h k' = some n → k = k'
  | [], k, _, n, e, _ => by simp [fidx] at e
  | a :: t, k, k', n, e1, e2 => by
    cases k with
    | zero =>
      cases k' with
      | zero => rfl
      | succ k' =>
        rw [fidx_cons_zero] at e1; rw [fidx_cons_succ] at e2
        split at e1
        · rename_i hs
          cases e1
          cases hm : fidx f t k' with
          | none => rw [hm] at e2; cases e2
          | some m =>
            rw [hm] at e2; simp only [Option.map, Option.some.injEq] at e2
            rw [if_pos hs] at e2; omega
        · cases e1
    | succ k =>
      cases k' with
      | zero =>
        rw [fidx_cons_zero] at e2; rw [fidx_cons_succ] at e1
        split at e2
        · rename_i hs
          cases e2
          cases hm : fidx f t k with
          | none => rw [hm] at e1; cases e1
          | some m =>
            rw [hm] at e1; simp only [Option.map, Option.some.injEq] at e1
            rw [if_pos hs] at e1; omega
        · cases e2
      | succ k' =>
        rw [fidx_cons_succ] at e1 e2
        cases hm : fidx f t k with
        | none => rw [hm] at e1; cases e1
        | some m =>
          cases hm' : fidx f t k' with
          | none => rw [hm'] at e2; cases e2
          | some m' =>
            rw [hm] at e1; rw [hm'] at e2
            simp only [Option.map, Option.some.injEq] at e1 e2
            have e : m = m' := by omega
            subst e
            rw [fidx_inj f t k k' m hm hm']

theorem fidx_lt (f : α → Option β) (h : List (Op α)) (k n : Nat) (e : fidx f h k = some n) :
    n < (fmapH f h).length := by
  obtain ⟨_, _, _, _, hg⟩ := fidx_get f h k n e
  exact (List.getElem?_eq_some_iff.1 hg).1

/-- The model runs: the kept operations of a run of `M` from a state related to the second model's
are a run of the second model. -/
theorem run_filter (M : SeqModel σ α) (M' : SeqModel σ' β) (f : α → Option β) (R : σ → σ' → Prop)
    (h : List (Op α))
    (hsimN : ∀ o ∈ h, ∀ s s' t, R s s' → M.step s o.val = some t → f o.val = none → R t s')
    (hsimS : ∀ o ∈ h, ∀ s s' t b, R s s' → M.step s o.val = some t → f o.val = some b →
      ∃ t', M'.step s' b = some t' ∧ R t t') :
    ∀ (l : List Nat) (s : σ) (s' : σ') (t : σ), R s s' → run M s (vals h l) = some t →
      ∃ t', run M' s' (vals (fmapH f h) (l.filterMap (fidx f h))) = some t'
  | [], _, s', _, _, _ => ⟨s', rfl⟩
  | k :: l, s, s', t, hR, hr => by
    cases ho : h[k]? with
    | none =>
      have hv : vals h (k :: l) = vals h l := by simp [vals, ho]
      have hf : fidx f h k = none := by simp [fidx, ho]
      rw [hv] at hr
      rw [List.filterMap_cons, hf]
      exact run_filter M M' f R h hsimN hsimS l s s' t hR hr
    | some o =>
      have hv : vals h (k :: l) = o.val :: vals h l := by simp [vals, ho]
      have hmem : o ∈ h := List.mem_of_getElem? ho
      rw [hv] at hr
      simp only [run] at hr
      cases hst : M.step s o.val with
      | none => rw [hst] at hr; cases hr
      | some s1 =>
        rw [hst] at hr
        simp only at hr
        cases hf : f o.val with
        | none =>
          have hfi : fidx f h k = none := by simp [fidx, ho, hf]
          rw [List.filterMap_cons, hfi]
          exact run_filter M M' f R h hsimN hsimS l s1 s' t (hsimN o hmem s s' s1 hR hst hf) hr
        | some b =>
          obtain ⟨s1', hst', hR'⟩ := hsimS o hmem s s' s1 b hR hst hf
          have hfi : fidx f h k = some (fmapH f (h.take k)).length := by simp [fidx, ho, hf]
          obtain ⟨o2, b2, ho2, hb2, hg⟩ := fidx_get f h k _ hfi
          rw [ho] at ho2; cases ho2
          rw [hf] at hb2; cases hb2
          rw [List.filterMap_cons, hfi]
          have hv' : vals (fmapH f h) ((fmapH f (h.take k)).length :: l.filterMap (fidx f h)) =
              b :: vals (fmapH f h) (l.filterMap (fidx f h)) := by simp [vals, hg]
          rw [hv']
          simp only [run, hst']
          exact run_filter M M' f R h hsimN hsimS l s1 s1' t hR' hr

/-- **Linearizability through a filter and a simulation**: if `R` relates the initial states and every
operation of `h` keeps it (a dropped one, `f = none`, leaves the second model's state; a kept one is a
step of the second model), then `π`'s kept indices, renumbered, linearize the kept operations. -/
theorem isLinearization_filter (M : SeqModel σ α) (M' : SeqModel σ' β) (f : α → Option β)
    (R : σ → σ' → Prop) (h : List (Op α)) (π : List Nat)
    (hinit : R M.init M'.init)
    (hsimN : ∀ o ∈ h, ∀ s s' t, R s s' → M.step s o.val = some t → f o.val = none → R t s')
    (hsimS : ∀ o ∈ h, ∀ s s' t b, R s s' → M.step s o.val = some t → f o.val = some b →
      ∃ t', M'.step s' b = some t' ∧ R t t')
    (hπ : IsLinearization M h π) :
    IsLinearization M' (fmapH f h) (π.filterMap (fidx f h)) := by
  obtain ⟨hnd, hmem, hrun, hpw⟩ := hπ
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold List.Nodup at hnd ⊢
    rw [List.pairwise_filterMap]
    refine hnd.imp ?_
    intro a a' hne b hb b' hb' e
    subst e
    exact hne (fidx_inj f h a a' b hb hb')
  · intro n
    constructor
    · intro hn
      obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 hn
      exact ⟨fidx_lt f h k n hk, fun e => e⟩
    · rintro ⟨hn, -⟩
      obtain ⟨k, hk⟩ := fidx_surj f h n _ (List.getElem?_eq_getElem hn)
      obtain ⟨o, -, ho, -, -⟩ := fidx_get f h k n hk
      have hkl : k < h.length := (List.getElem?_eq_some_iff.1 ho).1
      exact List.mem_filterMap.2 ⟨k, (hmem k).2 ⟨hkl, fun e => e⟩, hk⟩
  · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hrun
    obtain ⟨t', ht'⟩ := run_filter M M' f R h hsimN hsimS π M.init M'.init t hinit ht
    rw [ht']; rfl
  · rw [List.pairwise_filterMap]
    refine hpw.imp ?_
    intro a a' hna b hb b' hb' hprec
    apply hna
    obtain ⟨x, y, h1, h2, hlt⟩ := hprec
    obtain ⟨o, c, ho, -, hg⟩ := fidx_get f h a b hb
    obtain ⟨o', c', ho', -, hg'⟩ := fidx_get f h a' b' hb'
    rw [hg'] at h1; rw [hg] at h2
    cases h1; cases h2
    exact ⟨o', o, ho', ho, hlt⟩

/-- The kept operations' values, in the order of `l`'s kept indices. -/
theorem vals_fmapH (f : α → Option β) (h : List (Op α)) :
    ∀ l : List Nat, vals (fmapH f h) (l.filterMap (fidx f h)) = (vals h l).filterMap f
  | [] => rfl
  | k :: l => by
    have ih := vals_fmapH f h l
    cases ho : h[k]? with
    | none =>
      have hf : fidx f h k = none := by simp [fidx, ho]
      rw [List.filterMap_cons, hf]
      simpa [vals, ho] using ih
    | some o =>
      cases hfo : f o.val with
      | none =>
        have hf : fidx f h k = none := by simp [fidx, ho, hfo]
        rw [List.filterMap_cons, hf]
        simpa [vals, ho, hfo] using ih
      | some b =>
        have hfi : fidx f h k = some (fmapH f (h.take k)).length := by simp [fidx, ho, hfo]
        obtain ⟨o2, b2, ho2, hb2, hg⟩ := fidx_get f h k _ hfi
        rw [ho] at ho2; cases ho2
        rw [hfo] at hb2; cases hb2
        rw [List.filterMap_cons, hfi]
        have e1 : vals (fmapH f h) ((fmapH f (h.take k)).length :: l.filterMap (fidx f h)) =
            b :: vals (fmapH f h) (l.filterMap (fidx f h)) := by simp [vals, hg]
        have e2 : vals h (k :: l) = o.val :: vals h l := by simp [vals, ho]
        rw [e1, e2, List.filterMap_cons, hfo, ih]

theorem vals_range (h : List (Op α)) : vals h (List.range h.length) = h.map Op.val := by
  induction h with
  | nil => rfl
  | cons a t ih =>
    unfold vals at ih ⊢
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    simp only [List.getElem?_cons_zero, Option.map_some, List.map_cons]
    congr 1

/-- A linearization's values are a permutation of the history's. -/
theorem isLinearization_perm {M : SeqModel σ α} {h : List (Op α)} {π : List Nat}
    (hπ : IsLinearization M h π) : (vals h π).Perm (h.map Op.val) := by
  obtain ⟨hnd, hmem, -, -⟩ := hπ
  have hp : π.Perm (List.range h.length) := by
    rw [List.perm_ext_iff_of_nodup hnd List.nodup_range]
    intro k
    rw [hmem k, List.mem_range]
    exact ⟨fun e => e.1, fun e => ⟨e, fun x => x⟩⟩
  rw [← vals_range h]
  exact hp.filterMap _

theorem fmapH_map_val (f : α → Option β) (h : List (Op α)) :
    (fmapH f h).map Op.val = (h.map Op.val).filterMap f := by
  induction h with
  | nil => rfl
  | cons a t ih =>
    rw [fmapH_cons, List.map_append, ih, List.map_cons, List.filterMap_cons]
    cases f a.val <;> rfl

end Theory
end github_com.anishathalye.porcupine
end Perennial
