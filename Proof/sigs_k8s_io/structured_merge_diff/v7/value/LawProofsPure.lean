/-
**`value`'s pure facts** (structured-merge-diff v7.0.0): `gsLt` a strict total order, sorted
association lists (their keys distinct, lookups), as `value`'s proofs need them. The order facts are
the root laws' (`v7/LawProofs/Pure.lean`, copied here: `value` is below the root `Laws`). A
defs-tier module. Prove phase (2026-11-19).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

namespace ValuePure

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


/-! ## Sorted keys are distinct; lookups -/

theorem lookupKV_isSome_iff {α : Type} (k : GoString) :
    ∀ (kvs : List (GoString × α)), (lookupKV k kvs).isSome = true ↔ k ∈ kvKeys kvs
  | [] => by simp [lookupKV, kvKeys]
  | (k', v') :: rest => by
    unfold lookupKV
    by_cases h : k' = k
    · subst h; simp [kvKeys]
    · simp only [h, ite_false, lookupKV_isSome_iff k rest]
      simp [kvKeys, Ne.symm h]

theorem keysSorted_nodup {α : Type} : ∀ (kvs : List (GoString × α)), keysSorted kvs = true →
    (kvKeys kvs).Nodup
  | [], _ => by simp [kvKeys]
  | (k, v) :: rest, h => by
    simp only [kvKeys, List.map_cons, List.nodup_cons]
    refine ⟨?_, keysSorted_nodup rest (keysSorted_tail h)⟩
    intro hm
    obtain ⟨⟨k', v'⟩, hm', he⟩ := List.mem_map.1 hm
    simp only at he; subst he
    have := keysSorted_head_lt h k' v' hm'
    rw [gsLt_irrefl] at this; cases this

/-! ## Iterating a list of distinct keys -/

theorem nodup_not_mem_take {α : Type} : ∀ (l : List α), l.Nodup → ∀ (j : Nat) (a : α),
    l[j]? = some a → a ∉ l.take j
  | [], _, j, a, h => by simp at h
  | b :: l, hl, 0, a, h => by simp
  | b :: l, hl, j + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.mem_cons, not_or]
    rw [List.nodup_cons] at hl
    constructor
    · rintro rfl; exact hl.1 (List.mem_of_getElem? h)
    · exact nodup_not_mem_take l hl.2 j a h

theorem take_succ_of_getElem? {α : Type} (l : List α) (j : Nat) (a : α) (h : l[j]? = some a) :
    l.take (j + 1) = l.take j ++ [a] := by
  rw [List.take_add_one, h]; rfl

theorem perm_of_nodup_mem {α : Type} [DecidableEq α] (l l' : List α) (h1 : l.Nodup) (h2 : l'.Nodup)
    (h : ∀ a, a ∈ l ↔ a ∈ l') : l.Perm l' :=
  (List.perm_ext_iff_of_nodup h1 h2).2 h

/-! ## Zips with a nil side -/

theorem zipKeys_none_none : zipKeys none none = [] := by
  simp [zipKeys, kvsOrEmpty, zipLexical]

theorem zipLexical_left (n : Nat) (xs : List (GoString × UVal)) :
    (zipLexical (n + 1) xs []).map (·.1) = kvKeys xs := by
  cases xs <;> simp [zipLexical, kvKeys]

theorem zipLexical_right (n : Nat) (ys : List (GoString × UVal)) :
    (zipLexical (n + 1) [] ys).map (·.1) = kvKeys ys := by
  cases ys <;> simp [zipLexical, kvKeys]

theorem zipKeys_swap_none (kvs : List (GoString × UVal)) :
    zipKeys (some kvs) none = zipKeys none (some kvs) := by
  simp only [zipKeys, kvsOrEmpty, Option.getD_some, Option.getD_none, List.length_nil]
  rw [zipLexical_left, zipLexical_right]

/-! ## Equal sorted maps from their lookups -/

theorem kvs_eq_of_lookups {α : Type} (kvs kvs' : List (GoString × α))
    (hs : keysSorted kvs = true) (hs' : keysSorted kvs' = true) (hlen : kvs.length = kvs'.length)
    (h : ∀ k ∈ kvKeys kvs', lookupKV k kvs = lookupKV k kvs') : kvs = kvs' := by
  have hsub : kvKeys kvs' ⊆ kvKeys kvs := by
    intro k hk
    rw [← lookupKV_isSome_iff, h k hk, lookupKV_isSome_iff]; exact hk
  have hperm : (kvKeys kvs').Perm (kvKeys kvs) :=
    (List.subperm_of_subset (keysSorted_nodup kvs' hs') hsub).perm_of_length_le (by simp [kvKeys, hlen])
  apply sorted_ext kvs kvs' hs hs'
  intro k
  by_cases hk : k ∈ kvKeys kvs'
  · exact h k hk
  · have hk2 : k ∉ kvKeys kvs := fun hm => hk (hperm.mem_iff.2 hm)
    have e1 : (lookupKV k kvs).isSome = false := by
      rw [Bool.eq_false_iff]; intro hh; exact hk2 ((lookupKV_isSome_iff k kvs).1 hh)
    have e2 : (lookupKV k kvs').isSome = false := by
      rw [Bool.eq_false_iff]; intro hh; exact hk ((lookupKV_isSome_iff k kvs').1 hh)
    rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at e1 e2
    rw [e1, e2]

/-! ## The constructor tests -/

theorem isIntB_true {x : UVal} (h : true = x.isIntB) : ∃ n, x = .int n := by
  cases x <;> simp [UVal.isIntB] at h ⊢
theorem isStrB_true {x : UVal} (h : true = x.isStrB) : ∃ s, x = .str s := by
  cases x <;> simp [UVal.isStrB] at h ⊢
theorem isBoolB_true {x : UVal} (h : true = x.isBoolB) : ∃ b, x = .bool b := by
  cases x <;> simp [UVal.isBoolB] at h ⊢
theorem isListB_true {x : UVal} (h : true = x.isListB) : ∃ vs, x = .list vs := by
  cases x <;> simp [UVal.isListB] at h ⊢
theorem isMapB_true {x : UVal} (h : true = x.isMapB) : ∃ kvs, x = .map kvs := by
  cases x <;> simp [UVal.isMapB] at h ⊢
theorem isNullB_true {x : UVal} (h : true = x.isNullB) : x = .null := by
  cases x <;> simp [UVal.isNullB] at h ⊢

end ValuePure

end smd
end EtcdGrove
end Perennial
