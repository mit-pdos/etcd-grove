/-
**`strconv.FormatUint`'s result** (pure): `fmtUint n b`, the digits of `n` in base `b`, most
significant first, without leading zeros (`"0"` for `0`), the digits `0-9` then `a-z` (Go's
`strconv.FormatUint`, `internal/strconv/itoa.go`). Lean-first (no Rocq counterpart).

`decStr n = fmtUint n 10`, the decimal form, is injective (`decStr_inj`): the model API server's
resource versions (`examples/k8sdaemonset/apimodel`, `rvString`) are looked up by it.
-/
module

public import Perennial.Golang.Defn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- The digits of `n` in base `b ≥ 2`, most significant first (`[0]` for `0`). -/
def baseDigits (b : Nat) (hb : 2 ≤ b) (n : Nat) : List Nat :=
  if n < b then [n] else baseDigits b hb (n / b) ++ [n % b]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The number a list of digits (most significant first) denotes in base `b`. -/
def digitsVal (b : Nat) (ds : List Nat) : Nat := ds.foldl (fun a d => b * a + d) 0

theorem digitsVal_append (b : Nat) (ds : List Nat) (d : Nat) :
    digitsVal b (ds ++ [d]) = b * digitsVal b ds + d := by
  simp [digitsVal, List.foldl_append]

theorem digitsVal_baseDigits (b : Nat) (hb : 2 ≤ b) (n : Nat) :
    digitsVal b (baseDigits b hb n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [baseDigits]
    split
    · simp [digitsVal]
    · rw [digitsVal_append, ih (n / b) (Nat.div_lt_self (by omega) (by omega))]
      exact Nat.div_add_mod n b

theorem baseDigits_lt (b : Nat) (hb : 2 ≤ b) (n : Nat) : ∀ d ∈ baseDigits b hb n, d < b := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [baseDigits]
    split
    · intro d hd; simp at hd; omega
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact ih (n / b) (Nat.div_lt_self (by omega) (by omega)) d hd
      · subst hd; exact Nat.mod_lt n (by omega)

/-- A digit's character (`0-9`, then `a-z`). -/
def digitChar (d : Nat) : w8 := if d < 10 then W8 (48 + d) else W8 (87 + d)

theorem digitChar_inj {d e : Nat} (hd : d < 36) (he : e < 36) (h : digitChar d = digitChar e) :
    d = e := by
  unfold digitChar at h
  split at h <;> split at h <;>
    · have := congrArg BitVec.toNat h
      simp [W8] at this
      omega

/-- **`strconv.FormatUint(n, b)`** of a base `2 ≤ b ≤ 36`. -/
def fmtUint (n : w64) (b : w64) : GoString :=
  if h : 2 ≤ b.toNat then (baseDigits b.toNat h n.toNat).map digitChar else []

/-- The decimal form of `n` (`strconv.FormatUint(n, 10)`). -/
def decStr (n : w64) : GoString := fmtUint n (W64 10)

theorem decStr_eq (n : w64) :
    decStr n = (baseDigits 10 (by omega) n.toNat).map digitChar := by
  unfold decStr fmtUint
  rfl

theorem map_digitChar_inj (b : Nat) (hb : b ≤ 36) (ds es : List Nat) (hd : ∀ d ∈ ds, d < b)
    (he : ∀ e ∈ es, e < b) (h : ds.map digitChar = es.map digitChar) : ds = es := by
  induction ds generalizing es with
  | nil => cases es with
    | nil => rfl
    | cons _ _ => simp at h
  | cons d ds ih => cases es with
    | nil => simp at h
    | cons e es =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hd0 := hd d (by simp)
      have he0 := he e (by simp)
      rw [digitChar_inj (by omega) (by omega) h.1,
        ih es (fun x hx => hd x (by simp [hx])) (fun x hx => he x (by simp [hx])) h.2]

/-- **The decimal form is injective.** -/
theorem decStr_inj {m n : w64} (h : decStr m = decStr n) : m = n := by
  rw [decStr_eq, decStr_eq] at h
  have h' := map_digitChar_inj 10 (by omega) _ _ (baseDigits_lt 10 _ m.toNat)
    (baseDigits_lt 10 _ n.toNat) h
  have := congrArg (digitsVal 10) h'
  rw [digitsVal_baseDigits, digitsVal_baseDigits] at this
  exact BitVec.eq_of_toNat_eq this

/-- The decimal form is never empty. -/
theorem decStr_ne_nil (n : w64) : decStr n ≠ [] := by
  rw [decStr_eq, baseDigits]
  split <;> simp

end EtcdGrove
end Perennial
