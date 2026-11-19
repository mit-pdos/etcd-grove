/-
**The root laws' pure part, proved** (`v7/Laws.lean`, "Pure laws"): extensionality of sets of
paths and of sorted managed fields, with the facts about `gsLt` (a strict total order) and sorted
association lists they rest on.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

namespace LawProofs

/-! ## `gsCompare`, `gsLt` -/

theorem gsCompare_self : ∀ a : GoString, gsCompare a a = 0
  | [] => rfl
  | x :: xs => by simp [gsCompare, gsCompare_self xs]

theorem gsCompare_swap : ∀ a b : GoString, gsCompare b a = - gsCompare a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [gsCompare]
      by_cases h1 : x.toNat < y.toNat
      · have : ¬ y.toNat < x.toNat := by omega
        simp [h1, this]
      · by_cases h2 : y.toNat < x.toNat
        · simp [h1, h2]
        · simp [h1, h2, gsCompare_swap xs ys]

theorem gsCompare_range : ∀ a b : GoString, gsCompare a b = -1 ∨ gsCompare a b = 0 ∨ gsCompare a b = 1
  | [], [] => by simp [gsCompare]
  | [], _ :: _ => by simp [gsCompare]
  | _ :: _, [] => by simp [gsCompare]
  | x :: xs, y :: ys => by
      simp only [gsCompare]
      split
      · simp
      · split
        · simp
        · exact gsCompare_range xs ys

theorem w8_eq_of_toNat {x y : w8} (h1 : ¬ x.toNat < y.toNat) (h2 : ¬ y.toNat < x.toNat) : x = y := by
  apply BitVec.eq_of_toNat_eq; omega

theorem gsCompare_eq_zero : ∀ a b : GoString, gsCompare a b = 0 → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [gsCompare] at h
  | _ :: _, [], h => by simp [gsCompare] at h
  | x :: xs, y :: ys, h => by
      simp only [gsCompare] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i h1 h2
          rw [w8_eq_of_toNat h1 h2, gsCompare_eq_zero xs ys h]

theorem gsCompare_trans : ∀ a b c : GoString, gsCompare a b = -1 → gsCompare b c = -1 →
    gsCompare a c = -1
  | [], [], _, h, _ => by simp [gsCompare] at h
  | _ :: _, [], _, h, _ => by simp [gsCompare] at h
  | [], _ :: _, [], _, h => by simp [gsCompare] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, _ :: _, [], _, h => by simp [gsCompare] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
      simp only [gsCompare] at h1 h2 ⊢
      by_cases a1 : x.toNat < y.toNat
      · by_cases b1 : y.toNat < z.toNat
        · have : x.toNat < z.toNat := by omega
          simp [this]
        · by_cases b2 : z.toNat < y.toNat
          · simp [b1, b2] at h2
          · have : x.toNat < z.toNat := by omega
            simp [this]
      · by_cases a2 : y.toNat < x.toNat
        · simp [a1, a2] at h1
        · simp only [a1, a2, ite_false] at h1
          have hxy : x.toNat = y.toNat := by omega
          by_cases b1 : y.toNat < z.toNat
          · have : x.toNat < z.toNat := by omega
            simp [this]
          · by_cases b2 : z.toNat < y.toNat
            · simp [b1, b2] at h2
            · simp only [b1, b2, ite_false] at h2
              have c1 : ¬ x.toNat < z.toNat := by omega
              have c2 : ¬ z.toNat < x.toNat := by omega
              simp only [c1, c2, ite_false]
              exact gsCompare_trans xs ys zs h1 h2

theorem gsLt_iff (a b : GoString) : gsLt a b = true ↔ gsCompare a b = -1 := by
  simp [gsLt]

theorem gsLt_irrefl (a : GoString) : gsLt a a = false := by
  simp [gsLt, gsCompare_self]

theorem gsLt_trans {a b c : GoString} (h1 : gsLt a b = true) (h2 : gsLt b c = true) :
    gsLt a c = true := by
  rw [gsLt_iff] at *; exact gsCompare_trans a b c h1 h2

theorem gsLt_total {a b : GoString} (h1 : gsLt a b = false) (h2 : gsLt b a = false) : a = b := by
  simp only [gsLt, beq_eq_false_iff_ne, ne_eq] at h1 h2
  rw [gsCompare_swap] at h2
  rcases gsCompare_range a b with h | h | h
  · exact absurd h h1
  · exact gsCompare_eq_zero a b h
  · rw [h] at h2; exact absurd rfl h2

/-! ## Sorted association lists -/

theorem keysSorted_tail {α : Type} {k : GoString} {v : α} {rest : List (GoString × α)}
    (h : keysSorted ((k, v) :: rest) = true) : keysSorted rest = true := by
  match rest, h with
  | [], _ => rfl
  | (k', v') :: rest', h =>
    simp only [keysSorted, Bool.and_eq_true] at h
    exact h.2

theorem keysSorted_head_lt {α : Type} {k : GoString} {v : α} :
    ∀ {rest : List (GoString × α)}, keysSorted ((k, v) :: rest) = true →
    ∀ k' v', (k', v') ∈ rest → gsLt k k' = true
  | [], _, _, _, hm => by simp at hm
  | (k1, v1) :: rest', h, k', v', hm => by
      simp only [keysSorted, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hm with he | hm'
      · cases he; exact h.1
      · have := keysSorted_head_lt (k := k1) (v := v1) h.2 k' v' hm'
        exact gsLt_trans h.1 this

theorem lookupKV_mem' {α : Type} {k : GoString} : ∀ {xs : List (GoString × α)} {v : α},
    lookupKV k xs = some v → (k, v) ∈ xs
  | [], _, h => by simp [lookupKV] at h
  | (k', v') :: rest, v, h => by
      unfold lookupKV at h
      split at h
      · cases h; subst_vars; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookupKV_mem' h)

theorem lookupKV_head_none {α : Type} {k : GoString} {v : α} {rest : List (GoString × α)}
    (h : keysSorted ((k, v) :: rest) = true) : lookupKV k rest = none := by
  cases hl : lookupKV k rest with
  | none => rfl
  | some w =>
    have := keysSorted_head_lt h k w (lookupKV_mem' hl)
    rw [gsLt_irrefl] at this; cases this

theorem lookupKV_below {α : Type} {k k0 : GoString} {v : α} {rest : List (GoString × α)}
    (h : keysSorted ((k, v) :: rest) = true) (hlt : gsLt k0 k = true) :
    lookupKV k0 ((k, v) :: rest) = none := by
  unfold lookupKV
  have hne : k ≠ k0 := by rintro rfl; rw [gsLt_irrefl] at hlt; cases hlt
  simp only [hne, ite_false]
  cases hl : lookupKV k0 rest with
  | none => rfl
  | some w =>
    have h1 := keysSorted_head_lt h k0 w (lookupKV_mem' hl)
    have := gsLt_trans hlt h1
    rw [gsLt_irrefl] at this; cases this

theorem sorted_ext {α : Type} : ∀ (a b : List (GoString × α)), keysSorted a = true →
    keysSorted b = true → (∀ m, lookupKV m a = lookupKV m b) → a = b
  | [], [], _, _, _ => rfl
  | [], (k, v) :: _, _, _, h => by have := h k; simp [lookupKV] at this
  | (k, v) :: _, [], _, _, h => by have := h k; simp [lookupKV] at this
  | (k, v) :: a', (k', v') :: b', ha, hb, h => by
      have hk : k = k' := by
        cases h1 : gsLt k k' with
        | true =>
          have := h k
          rw [lookupKV_below hb h1] at this
          simp [lookupKV] at this
        | false =>
          cases h2 : gsLt k' k with
          | true =>
            have := h k'
            rw [lookupKV_below ha h2] at this
            simp [lookupKV] at this
          | false => exact gsLt_total h1 h2
      subst hk
      have hv : v = v' := by
        have := h k; simp [lookupKV] at this; exact this
      subst hv
      congr 1
      apply sorted_ext a' b' (keysSorted_tail ha) (keysSorted_tail hb)
      intro m
      by_cases hm : m = k
      · subst hm; rw [lookupKV_head_none ha, lookupKV_head_none hb]
      · have := h m
        simp only [lookupKV, Ne.symm hm, ite_false] at this
        exact this

end LawProofs

open LawProofs

theorem PathSet_ext_law_holds : PathSet_ext.law := by
  intro a b h
  induction a using Quotient.inductionOn with
  | h la =>
    induction b using Quotient.inductionOn with
    | h lb =>
      apply Quotient.sound
      intro q
      have := h q
      change FSet.mem (Quotient.mk _ la) q = true ↔ FSet.mem (Quotient.mk _ lb) q = true at this
      simpa [FSet.mem] using this

theorem MF_ext_law_holds : MF_ext.law := fun a b ha hb h =>
  sorted_ext a b ha hb h

end smd
end EtcdGrove
end Perennial
