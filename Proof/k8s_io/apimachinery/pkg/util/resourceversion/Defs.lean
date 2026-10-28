/-
The resource versions of apimachinery's `util/resourceversion` (`resourceversion.go`), as pure
functions. Lean-first; for client-go's consistency store (`Proof/k8s_io/client_go/util/consistency/`).

A resource version is **well formed** (`wellFormed`) when it is a non-empty string of ASCII
digits with no leading `0` (so `"0"` is not: Go's comment, "Zero is also considered an invalid
value as it is used as a special value in list/watch events and will never be a live resource
version"). Its value is the decimal number it spells (`decVal`). `CompareResourceVersion`
compares well-formed versions by length, then byte-wise (`lexCmp`); `lexCmp_eq_cmpNat` proves
that this is the comparison of their values (`cmpNat (decVal a) (decVal b)`), which is how its
spec states the result.
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.resourceversion
public import Proof.k8s_io.apimachinery.pkg.util.resourceversion.Init
public import Perennial.Proof.strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

/-- `isDigit(b)`: `'0' ≤ b ≤ '9'`. -/
def digitB (b : w8) : Bool := decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- A well-formed resource version: non-empty, all digits, no leading `0`. -/
def wellFormed : GoString → Bool
  | [] => false
  | c :: s => decide (c ≠ W8 48) && (c :: s).all digitB

/-- The value of a digit string (most significant digit first). -/
def decVal : GoString → Nat
  | [] => 0
  | c :: s => (c.toNat - 48) * 10 ^ s.length + decVal s

/-- A three-way comparison as Go's `int`: `-1`, `0` or `1`. -/
def cmpNat (x y : Nat) : w64 := if x < y then W64 (-1) else if x = y then W64 0 else W64 1

/-- What `CompareResourceVersion` computes of two well-formed versions: shorter is less; equal
lengths compare byte-wise (`strings.Compare`). -/
def lexCmp (a b : GoString) : w64 :=
  if a.length < b.length then W64 (-1) else if a.length > b.length then W64 1
  else strings.compareResult a b

/-! ## Lemmas -/

/-- A length below `2^63` as an `int`. -/
theorem sintZ_len {k : Nat} (h : k < 2 ^ 63) : sint.Z (W64 (k : Int)) = k := by
  word

theorem digit_toNat {c : w8} (h : digitB c = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simpa [digitB] using h

theorem decVal_lt (s : GoString) (h : s.all digitB = true) : decVal s < 10 ^ s.length := by
  induction s with
  | nil => simp [decVal]
  | cons c s ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hc := digit_toNat h.1
    have ih := ih h.2
    simp only [decVal, List.length_cons, Nat.pow_succ]
    have : (c.toNat - 48) * 10 ^ s.length ≤ 9 * 10 ^ s.length := Nat.mul_le_mul_right _ (by omega)
    have : 10 ^ s.length * 10 = 9 * 10 ^ s.length + 10 ^ s.length := by omega
    omega

theorem decVal_ge (c : w8) (s : GoString) (h : wellFormed (c :: s) = true) :
    10 ^ s.length ≤ decVal (c :: s) := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_cons] at h
  obtain ⟨hne, hd, -⟩ := h
  have hc := digit_toNat hd
  have h48 : c.toNat ≠ 48 := by
    intro e; apply hne; apply BitVec.eq_of_toNat_eq; simp [e]
  simp only [decVal]
  have : 1 * 10 ^ s.length ≤ (c.toNat - 48) * 10 ^ s.length := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Equal-length digit strings: byte-wise order is the order of the values. -/
theorem lex_iff_decVal (a b : GoString) (ha : a.all digitB = true) (hb : b.all digitB = true)
    (hl : a.length = b.length) :
    (go.GoStringLt a b ↔ decVal a < decVal b) ∧ (a = b ↔ decVal a = decVal b) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [go.GoStringLt, decVal]
    | cons _ _ => simp at hl
  | cons c a ih =>
    cases b with
    | nil => simp at hl
    | cons d b =>
      simp only [List.all_cons, Bool.and_eq_true] at ha hb
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hc := digit_toNat ha.1
      have hd := digit_toNat hb.1
      have ⟨ihlt, iheq⟩ := ih b ha.2 hb.2 hl
      have hva := decVal_lt a ha.2
      have hvb := decVal_lt b hb.2
      simp only [decVal, hl]
      rw [hl] at hva
      have hlex : go.GoStringLt (c :: a) (d :: b) ↔ (c.toNat < d.toNat ∨ (c = d ∧ go.GoStringLt a b)) := by
        unfold go.GoStringLt
        constructor
        · intro h
          cases h with
          | rel h => left; simpa [uint.Z] using h
          | cons h => right; exact ⟨rfl, h⟩
        · rintro (h | ⟨rfl, h⟩)
          · exact List.Lex.rel (by simpa [uint.Z] using h)
          · exact List.Lex.cons h
      rw [hlex]
      have key : ∀ x y : Nat, x < y → ∀ u v : Nat, u < 10 ^ b.length → v < 10 ^ b.length →
          x * 10 ^ b.length + u < y * 10 ^ b.length + v := by
        intro x y hxy u v hu _
        have : (x + 1) * 10 ^ b.length ≤ y * 10 ^ b.length := Nat.mul_le_mul_right _ hxy
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      have hcd : c = d ↔ c.toNat = d.toNat :=
        ⟨fun e => by rw [e], fun e => BitVec.eq_of_toNat_eq e⟩
      constructor
      · constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact key _ _ (by omega) _ _ hva hvb
          · rw [h1]; exact Nat.add_lt_add_left (ihlt.1 h2) _
        · intro h
          rcases Nat.lt_trichotomy c.toNat d.toNat with h' | h' | h'
          · left; exact h'
          · right
            refine ⟨hcd.2 h', ihlt.2 ?_⟩
            rw [show c.toNat - 48 = d.toNat - 48 by omega] at h
            omega
          · exfalso
            have := key _ _ (show d.toNat - 48 < c.toNat - 48 by omega) _ _ hvb hva
            omega
      · constructor
        · intro e; cases e; rfl
        · intro h
          rcases Nat.lt_trichotomy c.toNat d.toNat with h' | h' | h'
          · exfalso; have := key _ _ (show c.toNat - 48 < d.toNat - 48 by omega) _ _ hva hvb; omega
          · have e1 := hcd.2 h'
            rw [show c.toNat - 48 = d.toNat - 48 by omega] at h
            have e2 := iheq.2 (by omega)
            rw [e1, e2]
          · exfalso; have := key _ _ (show d.toNat - 48 < c.toNat - 48 by omega) _ _ hvb hva; omega

theorem wellFormed_all {s : GoString} (h : wellFormed s = true) : s.all digitB = true := by
  cases s with
  | nil => simp [wellFormed] at h
  | cons c s => simp only [wellFormed, Bool.and_eq_true] at h; exact h.2

/-- **`CompareResourceVersion` compares the values** of well-formed versions. -/
theorem lexCmp_eq_cmpNat (a b : GoString) (ha : wellFormed a = true) (hb : wellFormed b = true) :
    lexCmp a b = cmpNat (decVal a) (decVal b) := by
  have hva := decVal_lt a (wellFormed_all ha)
  have hvb := decVal_lt b (wellFormed_all hb)
  have hga : 10 ^ (a.length - 1) ≤ decVal a := by
    cases a with
    | nil => simp [wellFormed] at ha
    | cons c s => simpa using decVal_ge c s ha
  have hgb : 10 ^ (b.length - 1) ≤ decVal b := by
    cases b with
    | nil => simp [wellFormed] at hb
    | cons c s => simpa using decVal_ge c s hb
  have hpa : 0 < a.length := by cases a <;> simp_all [wellFormed]
  have hpb : 0 < b.length := by cases b <;> simp_all [wellFormed]
  unfold lexCmp cmpNat
  by_cases hlt : a.length < b.length
  · have : 10 ^ a.length ≤ 10 ^ (b.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [hlt, ↓reduceIte, show decVal a < decVal b by omega]
  by_cases hgt : a.length > b.length
  · have : 10 ^ b.length ≤ 10 ^ (a.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [hlt, hgt, ↓reduceIte, show ¬ decVal a < decVal b by omega,
      show decVal a ≠ decVal b by omega]
  have hl : a.length = b.length := by omega
  have ⟨hlex, heq⟩ := lex_iff_decVal a b (wellFormed_all ha) (wellFormed_all hb) hl
  simp only [hlt, hgt, ↓reduceIte, strings.compareResult]
  by_cases h1 : go.GoStringLt a b
  · simp [h1, hlex.1 h1]
  · have h1' : ¬ decVal a < decVal b := fun h => h1 (hlex.2 h)
    simp only [h1, h1', ↓reduceIte]
    by_cases h2 : a = b
    · simp [h2]
    · simp [h2, show decVal a ≠ decVal b from fun h => h2 (heq.2 h)]

end resourceversion
end EtcdGrove
end Perennial
