/-
**The model's resource versions are well formed, of their value** (pure): `rvStr n`, the decimal
form `strconv.FormatUint(n, 10)` the model API server issues, is a well-formed resource version
(`resourceversion.wellFormed`) for `n ≥ 1`, whose value (`decVal`) is `n`. So the consistency
store records a created pod's version (`WroteAt` ignores malformed ones) and compares it by value.
Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.resourceversion.Defs
public import Proof.strconv.FormatUintDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open resourceversion

theorem digitChar_toNat {d : Nat} (h : d < 10) : (digitChar d).toNat = 48 + d := by
  unfold digitChar
  simp only [h, ↓reduceIte, W8, BitVec.toNat_ofInt]
  omega

theorem foldl_digits (b a : Nat) (ds : List Nat) :
    ds.foldl (fun a d => b * a + d) a = a * b ^ ds.length + ds.foldl (fun a d => b * a + d) 0 := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (b * a + d), ih (b * 0 + d), Nat.pow_succ]
    have : ∀ x y z : Nat, x * (y * z) = z * x * y := fun x y z => by
      rw [Nat.mul_comm y z, ← Nat.mul_assoc, Nat.mul_comm x z]
    rw [Nat.mul_zero, Nat.zero_add, Nat.add_mul, this a (b ^ ds.length) b]
    omega

theorem digitsVal_cons (b d : Nat) (ds : List Nat) :
    digitsVal b (d :: ds) = d * b ^ ds.length + digitsVal b ds := by
  unfold digitsVal
  rw [List.foldl_cons, foldl_digits]
  simp

theorem decVal_digits (ds : List Nat) (h : ∀ d ∈ ds, d < 10) :
    decVal (ds.map digitChar) = digitsVal 10 ds := by
  induction ds with
  | nil => simp [decVal, digitsVal]
  | cons d ds ih =>
    have hd := h d (by simp)
    rw [List.map_cons, decVal, digitsVal_cons, List.length_map, digitChar_toNat hd,
      ih (fun x hx => h x (by simp [hx]))]
    rw [Nat.add_sub_cancel_left]


theorem all_digitB_digits (ds : List Nat) (h : ∀ d ∈ ds, d < 10) :
    (ds.map digitChar).all digitB = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  have := digitChar_toNat (h d hd)
  simp only [digitB, this, decide_eq_true_eq]
  have := h d hd
  omega

/-- The leading digit of a positive number is not `0`. -/
theorem baseDigits_head_pos (n : Nat) (hn : 1 ≤ n) :
    ∃ d ds, baseDigits 10 (by omega) n = d :: ds ∧ d ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [baseDigits]
    split
    · exact ⟨n, [], rfl, by omega⟩
    · rename_i h
      obtain ⟨d, ds, he, hd⟩ := ih (n / 10) (Nat.div_lt_self (by omega) (by omega))
        (by omega)
      exact ⟨d, ds ++ [n % 10], by rw [he]; rfl, hd⟩

/-- **The model's versions are well formed** (`n ≥ 1`). -/
theorem wellFormed_rvStr (n : w64) (hn : 1 ≤ n.toNat) : wellFormed (decStr n) = true := by
  rw [decStr_eq]
  obtain ⟨d, ds, he, hd⟩ := baseDigits_head_pos n.toNat hn
  have hlt := baseDigits_lt 10 (by omega) n.toNat
  have hall := all_digitB_digits _ hlt
  rw [he] at hall hlt ⊢
  simp only [List.map_cons, wellFormed, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hall⟩
  intro h
  have := digitChar_toNat (hlt d (by simp))
  rw [h] at this
  simp [W8] at this
  omega

/-- **The model's versions' values** are their numbers. -/
theorem decVal_rvStr (n : w64) : decVal (decStr n) = n.toNat := by
  rw [decStr_eq, decVal_digits _ (baseDigits_lt 10 (by omega) n.toNat), digitsVal_baseDigits]

end dsctl
end EtcdGrove
end Perennial
