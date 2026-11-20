/-
**Helpers of the merging and compare walkers' `visitListItems`** (and `indexListPathElements`):
the keys of a list's prefix, its items by key, a `PEMap`'s count bound from the keys it holds,
and the merged order (`mergeOrderF`) one step of `mergingWalker.visitListItems`'s loop at a time.

Prove phase, round 2 (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace LawBL2

/-- A map whose keys are in a list shorter than `b` has fewer than `b` keys. -/
theorem peMap_cardLt {α : Type} (M : PEMap α) (l : List PE) (b : Nat)
    (h : ∀ k, (M k).isSome → k ∈ l) (hl : l.length < b) : M.CardLt b := by
  intro n ⟨l', hnd, hmem, hlen⟩
  have := hnd.length_le_of_subset (l₂ := l) (fun k hk => h k ((hmem k).1 hk))
  omega

/-- The item with key `k` among the first `i + 1` items: the `i`-th if it has key `k`, else the
one before. -/
theorem itemOf_take_succ (ks : List GoString) (vs : List UVal) (i : Nat) (x : UVal) (k : PE)
    (hx : vs[i]? = some x) :
    itemOf ks (vs.take (i + 1)) k =
      match itemOf ks (vs.take i) k with
      | some y => some y
      | none => if keyOf ks x = some k then some x else none := by
  unfold itemOf
  rw [List.take_add_one, hx]
  simp only [Option.toList_some, List.find?_append]
  cases h : List.find? (fun v => decide (keyOf ks v = some k)) (vs.take i) with
  | some y => rfl
  | none =>
    simp only [Option.none_or, List.find?_cons, List.find?_nil]
    by_cases hk : keyOf ks x = some k <;> simp [hk]

/-- No item has a key the list's keys do not hold. -/
theorem itemOf_none (ks : List GoString) (vs : List UVal) (k : PE) (h : k ∉ keysOf ks vs) :
    itemOf ks vs k = none := by
  cases hi : itemOf ks vs k with
  | none => rfl
  | some y =>
    exfalso; apply h
    unfold itemOf at hi
    have hm := List.mem_of_find?_eq_some hi
    have hk := List.find?_some hi
    simp only [decide_eq_true_eq] at hk
    exact List.mem_filterMap.2 ⟨y, hm, hk⟩

/-- A list's item by key is the item if its key is the key. -/
theorem itemOf_isSome (ks : List GoString) (vs : List UVal) (k : PE) :
    (itemOf ks vs k).isSome ↔ k ∈ keysOf ks vs := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    rw [itemOf_none ks vs k hn] at h; cases h
  · intro h
    obtain ⟨y, hy, hk⟩ := List.mem_filterMap.1 h
    unfold itemOf
    cases hf : vs.find? (fun v => decide (keyOf ks v = some k)) with
    | some _ => rfl
    | none =>
      exfalso
      have := List.find?_eq_none.1 hf y hy
      simp [hk] at this

/-- The `i`-th item, of a fresh key `k`, is the prefix's item of key `k`. -/
theorem itemOf_take_succ_eq (ks : List GoString) (vs : List UVal) (i : Nat) (x : UVal) (k : PE)
    (hx : vs[i]? = some x) (hk : keyOf ks x = some k) (hf : k ∉ keysOf ks (vs.take i)) :
    itemOf ks (vs.take (i + 1)) k = some x := by
  rw [itemOf_take_succ ks vs i x k hx, itemOf_none ks _ k hf, if_pos hk]

/-- The other keys' items are the shorter prefix's. -/
theorem itemOf_take_succ_ne (ks : List GoString) (vs : List UVal) (i : Nat) (x : UVal) (k k' : PE)
    (hx : vs[i]? = some x) (hk : keyOf ks x = some k) (hne : k' ≠ k) :
    itemOf ks (vs.take (i + 1)) k' = itemOf ks (vs.take i) k' := by
  rw [itemOf_take_succ ks vs i x k' hx]
  cases itemOf ks (vs.take i) k' with
  | some y => rfl
  | none => rw [if_neg (by rw [hk]; intro h; exact hne (Option.some.inj h).symm)]

/-- The item with key `k` of the whole list, from a prefix with all the keys. -/
theorem itemOf_take_length (ks : List GoString) (vs : List UVal) (k : PE) :
    itemOf ks (vs.take vs.length) k = itemOf ks vs k := by
  rw [List.take_length]

/-! ## The merged order, one loop step at a time -/

/-- `mergingWalker.visitListItems`'s skip test: a shared key the left side reaches out of the
right side's order. -/
def skipC (inR : PE → Bool) (sh : List PE) (l : PE) : Bool :=
  inR l && (match sh.head? with
    | some s => decide (s ≠ l)
    | none => false)

/-- **The loop's invariant on the order**: the keys emitted so far (`done`), then what
`mergeOrderF` emits from the loop's state (`L`, `R`: the keys left on each side; `sh`: the shared
keys not merged yet; `mg`: the keys merged) with fuel enough, are the merged order `target`. -/
def MInv (inR : PE → Bool) (target done L R sh mg : List PE) : Prop :=
  ∃ f, L.length + R.length < f ∧ done ++ mergeOrderF f inR L R sh mg = target

theorem MInv_init (L R : List PE) :
    MInv (fun x => decide (x ∈ R)) (mergeKeys L R) [] L R (R.filter (fun x => decide (x ∈ L))) [] :=
  ⟨L.length + R.length + 1, by omega, by simp [mergeKeys]⟩

theorem mergeOrderF_nil (f : Nat) (inR : PE → Bool) (sh mg : List PE) :
    mergeOrderF f inR [] [] sh mg = [] := by
  cases f <;> simp [mergeOrderF]

theorem MInv_done {inR : PE → Bool} {target done sh mg : List PE}
    (h : MInv inR target done [] [] sh mg) : done = target := by
  obtain ⟨f, -, h⟩ := h
  rw [mergeOrderF_nil, List.append_nil] at h; exact h

/-- Both heads equal: merged. -/
theorem MInv_eq {inR : PE → Bool} {target done L' R' sh mg : List PE} {l : PE}
    (h : MInv inR target done (l :: L') (l :: R') sh mg) :
    MInv inR target (done ++ [l]) L' R' sh.tail (l :: mg) := by
  obtain ⟨f, hf, h⟩ := h
  cases f with
  | zero => simp at hf
  | succ f =>
    refine ⟨f, by simp at hf; omega, ?_⟩
    rw [← h]; simp [mergeOrderF]

/-- A shared key out of order on the left: skipped. -/
theorem MInv_skip {inR : PE → Bool} {target done L' R' sh mg : List PE} {l r : PE}
    (hlr : l ≠ r) (hs : skipC inR sh l = true)
    (h : MInv inR target done (l :: L') (r :: R') sh mg) :
    MInv inR target done L' (r :: R') sh mg := by
  obtain ⟨f, hf, h⟩ := h
  cases f with
  | zero => simp at hf
  | succ f =>
    refine ⟨f, by simp at hf ⊢; omega, ?_⟩
    rw [← h]
    unfold skipC at hs
    rcases hsh : sh.head? with _ | s
    · simp [hsh] at hs
    · simp only [hsh, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp [mergeOrderF, hlr, hsh, hs]

/-- A left-only key: emitted. -/
theorem MInv_left {inR : PE → Bool} {target done L' R sh mg : List PE} {l : PE}
    (hin : inR l = false) (hR : R.head? ≠ some l)
    (h : MInv inR target done (l :: L') R sh mg) :
    MInv inR target (done ++ [l]) L' R sh mg := by
  obtain ⟨f, hf, h⟩ := h
  cases f with
  | zero => simp at hf
  | succ f =>
    refine ⟨f, by simp at hf ⊢; omega, ?_⟩
    rw [← h]
    rcases R with _ | ⟨r, R'⟩
    · simp [mergeOrderF, hin]
    · have hlr : l ≠ r := fun e => hR (by simp [e])
      simp [mergeOrderF, hlr, hin]

/-- The left side's next key after a step on the right (`L2`): skipped if merged already. -/
def nextL (L mg : List PE) : List PE :=
  match L with
  | l :: L' => if l ∈ mg then L' else L
  | [] => []

/-- A right key: emitted (merged with the left item of its key, if any). -/
theorem MInv_right {inR : PE → Bool} {target done L R' sh mg : List PE} {r : PE}
    (hL : ∀ l L', L = l :: L' → inR l = true ∧ l ≠ r ∧ skipC inR sh l = false)
    (h : MInv inR target done L (r :: R') sh mg) :
    MInv inR target (done ++ [r]) (nextL L mg) R' (if sh.head? = some r then sh.tail else sh)
      (r :: mg) := by
  obtain ⟨f, hf, h⟩ := h
  cases f with
  | zero => simp at hf
  | succ f =>
    rcases L with _ | ⟨l, L'⟩
    · refine ⟨f, by simp [nextL] at hf ⊢; omega, ?_⟩
      rw [← h]; simp [mergeOrderF, nextL]
    · obtain ⟨hin, hlr, hs⟩ := hL l L' rfl
      have hs' : (inR l && (match sh.head? with
          | some s => decide (s ≠ l)
          | none => false)) = false := hs
      refine ⟨f, ?_, ?_⟩
      · simp only [nextL]; split <;> simp at hf ⊢ <;> omega
      · rw [← h]
        unfold skipC at hs
        rcases hsh : sh.head? with _ | s
        · simp [mergeOrderF, hlr, hin, hsh, nextL]
        · simp only [hsh, hin, Bool.true_and, decide_eq_false_iff_not, Decidable.not_not] at hs
          subst hs
          simp [mergeOrderF, hlr, hin, hsh, nextL]

/-- The right side done, a shared left key already merged: skipped. -/
theorem MInv_rdone {inR : PE → Bool} {target done L' sh mg : List PE} {l : PE}
    (hin : inR l = true) (hmg : l ∈ mg)
    (h : MInv inR target done (l :: L') [] sh mg) :
    MInv inR target done L' [] sh mg := by
  obtain ⟨f, hf, h⟩ := h
  cases f with
  | zero => simp at hf
  | succ f =>
    refine ⟨f, by simp at hf ⊢; omega, ?_⟩
    rw [← h]
    simp [mergeOrderF, hin, hmg]

end LawBL2

end smd
end EtcdGrove
end Perennial
