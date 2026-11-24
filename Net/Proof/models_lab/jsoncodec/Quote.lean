/-
What `jsoncodec`'s encoders write, as Lean functions of their inputs (#24 J2): `jsonQuote s`, the
JSON string `AppendString` writes for `s` (real encoding/json's escaping: `appendEscapedASCII` per
ASCII byte, `U+FFFD` per byte starting no valid UTF-8 sequence, `\u2028`/`\u2029`, every other
valid sequence as it is), and `decU64 x`, the decimal digits `AppendUint` writes. Mirrors of the Go
code (`models/jsoncodec/jsoncodec.go`), so that the specs over them say which bytes are written;
the claim that these are real encoding/json's bytes is the Go code's (tested there), not these
definitions'. Pure.
-/
module

public import Net.Proof.models_lab.jsoncodec.Base

@[expose] public section

namespace Perennial

namespace models_lab.jsoncodec

/-- The lower-case hexadecimal digit of `n < 16` (`hexDigits[n]`). -/
def hexDigit (n : Nat) : w8 := (go!"0123456789abcdef" : List w8).getD n (W8 0)

/-- `hexDigits[n]`, `n < 16`, as `Index go.untypedString` reduces it. -/
theorem hexIdx (n : Nat) (h : n < 16) :
    (if 0 ≤ sint.Z (W64 (n : Int)) then (go!"0123456789abcdef" : List w8)[sint.nat (W64 (n : Int))]?
      else none) = some (hexDigit n) := by
  have h0 : 0 ≤ sint.Z (W64 (n : Int)) := by word
  have he : sint.nat (W64 (n : Int)) = n := by word
  simp only [h0, ↓reduceIte, he]
  unfold hexDigit
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  rfl

theorem uintZ_w8 (x : w8) : uint.Z x = ((x.toNat : Nat) : Int) := rfl

theorem shr4_toNat (x : w8) : (x >>> W64 4).toNat = x.toNat / 16 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem and15_toNat (x : w8) : (x &&& W8 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and]
  have : (W8 15 : w8).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- `htmlByte c`: `<`, `>` or `&`. -/
def htmlB (c : w8) : Bool := decide (c = W8 60 ∨ c = W8 62 ∨ c = W8 38)

/-- The bytes `appendEscapedASCII` writes for the ASCII byte `c`. -/
def escASCII (c : w8) : List w8 :=
  if c = W8 34 ∨ c = W8 92 then [W8 92, c]
  else if c = W8 8 then [W8 92, W8 98]
  else if c = W8 12 then [W8 92, W8 102]
  else if c = W8 10 then [W8 92, W8 110]
  else if c = W8 13 then [W8 92, W8 114]
  else if c = W8 9 then [W8 92, W8 116]
  else if c.toNat < 0x20 ∨ htmlB c = true then
    [W8 92, W8 117, W8 48, W8 48, hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
  else [c]

/-- The low end of the second byte's range after the lead byte `c` (`seqLenOf`'s `lo`). -/
def loB (c : w8) : w8 := if c = W8 224 then W8 160 else if c = W8 240 then W8 144 else W8 128

/-- The high end of the second byte's range after the lead byte `c` (`seqLenOf`'s `hi`). -/
def hiB (c : w8) : w8 := if c = W8 224 then W8 191 else if c = W8 237 then W8 159
  else if c = W8 240 then W8 191 else if c = W8 244 then W8 143 else W8 191

/-- `seqLenOf(c, c1, c2, c3)`, stated over the same comparisons as the Go code: the length of the
valid UTF-8 sequence starting with these bytes (`2`, `3`, `4`), or `1`. -/
def seqLenB (c c1 c2 c3 : w8) : Nat :=
  if uint.Z c < uint.Z (W8 194) ∨ uint.Z (W8 244) < uint.Z c then 1 else
  if uint.Z c1 < uint.Z (loB c) ∨ uint.Z (hiB c) < uint.Z c1 then 1 else
  if uint.Z c < uint.Z (W8 224) then 2 else
  if uint.Z c2 < uint.Z (W8 128) ∨ uint.Z (W8 191) < uint.Z c2 then 1 else
  if uint.Z c < uint.Z (W8 240) then 3 else
  if uint.Z c3 < uint.Z (W8 128) ∨ uint.Z (W8 191) < uint.Z c3 then 1 else 4

/-- `seqLen(s, i)`: `seqLenOf` of `s[i]` and the three bytes after it (`0` past the end). -/
def seqLenAt (s : List w8) (i : Nat) : Nat :=
  seqLenB (s.getD i (W8 0)) (s.getD (i + 1) (W8 0)) (s.getD (i + 2) (W8 0)) (s.getD (i + 3) (W8 0))

theorem seqLenB_pos (c c1 c2 c3 : w8) : 1 ≤ seqLenB c c1 c2 c3 := by
  unfold seqLenB
  repeat' split
  all_goals omega

theorem seqLenAt_pos (s : List w8) (i : Nat) : 1 ≤ seqLenAt s i := seqLenB_pos _ _ _ _

theorem loB_ge (c : w8) : 128 ≤ uint.Z (loB c) := by
  unfold loB; repeat' split
  all_goals decide

theorem seqLenB_le4 (c c1 c2 c3 : w8) : seqLenB c c1 c2 c3 ≤ 4 := by
  unfold seqLenB
  repeat' split
  all_goals omega

theorem seqLenB_zero1 (c c2 c3 : w8) : seqLenB c (W8 0) c2 c3 = 1 := by
  unfold seqLenB
  have h : uint.Z (W8 0) < uint.Z (loB c) := by
    have := loB_ge c; rw [show uint.Z (W8 0) = 0 from rfl]; omega
  simp only [h, true_or, ↓reduceIte, ite_self]

theorem seqLenB_zero2 (c c1 c3 : w8) : seqLenB c c1 (W8 0) c3 ≤ 2 := by
  unfold seqLenB
  have h : uint.Z (W8 0) < uint.Z (W8 128) := by decide
  simp only [h, true_or, ↓reduceIte]
  repeat' split
  all_goals omega

theorem seqLenB_zero3 (c c1 c2 : w8) : seqLenB c c1 c2 (W8 0) ≤ 3 := by
  unfold seqLenB
  have h : uint.Z (W8 0) < uint.Z (W8 128) := by decide
  simp only [h, true_or, ↓reduceIte]
  repeat' split
  all_goals omega

/-- A byte past the end is `0`, below every continuation byte: the sequence ends within `s`. -/
theorem seqLenAt_le (s : List w8) (i : Nat) (h : i < s.length) : i + seqLenAt s i ≤ s.length := by
  have hz : ∀ k, s.length ≤ k → s.getD k (W8 0) = W8 0 := fun k hk => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl
  unfold seqLenAt
  rcases Nat.lt_or_ge (i + 1) s.length with h1 | h1
  · rcases Nat.lt_or_ge (i + 2) s.length with h2 | h2
    · rcases Nat.lt_or_ge (i + 3) s.length with h3 | h3
      · have := seqLenB_le4 (s.getD i (W8 0)) (s.getD (i + 1) (W8 0)) (s.getD (i + 2) (W8 0))
          (s.getD (i + 3) (W8 0))
        omega
      · rw [hz (i + 3) h3]
        have := seqLenB_zero3 (s.getD i (W8 0)) (s.getD (i + 1) (W8 0)) (s.getD (i + 2) (W8 0))
        omega
    · rw [hz (i + 2) h2]
      have := seqLenB_zero2 (s.getD i (W8 0)) (s.getD (i + 1) (W8 0)) (s.getD (i + 3) (W8 0))
      omega
  · rw [hz (i + 1) h1, seqLenB_zero1]
    omega

/-- What `AppendString` writes for the sequence of length `k` (`seqLenAt`) at `s[i]`, a byte of
`0x80` or above. -/
def nonASCIIPiece (s : List w8) (i k : Nat) : List w8 :=
  if k = 1 then go!"\uFFFD"
  else if k = 3 ∧ s.getD i (W8 0) = W8 0xe2 ∧ s.getD (i + 1) (W8 0) = W8 0x80 ∧
      s.getD (i + 2) (W8 0) = W8 0xa8 then go!"\\u2028"
  else if k = 3 ∧ s.getD i (W8 0) = W8 0xe2 ∧ s.getD (i + 1) (W8 0) = W8 0x80 ∧
      s.getD (i + 2) (W8 0) = W8 0xa9 then go!"\\u2029"
  else (s.drop i).take k

/-- What `AppendString` writes for `s[i:]`, between the quotes. -/
def quoteFrom (s : List w8) (i : Nat) : List w8 :=
  if _h : i < s.length then
    if (s.getD i (W8 0)).toNat < 0x80 then escASCII (s.getD i (W8 0)) ++ quoteFrom s (i + 1)
    else nonASCIIPiece s i (seqLenAt s i) ++ quoteFrom s (i + seqLenAt s i)
  else []
termination_by s.length - i
decreasing_by
  · omega
  · have := seqLenAt_pos s i; omega

/-- **The JSON string `AppendString` writes for `s`** (real encoding/json's, `jsonwire.AppendQuote`
with v1's flags). -/
def jsonQuote (s : List w8) : List w8 := [W8 34] ++ quoteFrom s 0 ++ [W8 34]

theorem quoteFrom_ascii (s : List w8) (i : Nat) (h : i < s.length)
    (hc : (s.getD i (W8 0)).toNat < 0x80) :
    quoteFrom s i = escASCII (s.getD i (W8 0)) ++ quoteFrom s (i + 1) := by
  rw [quoteFrom]; simp only [h, hc, ↓reduceDIte, ↓reduceIte]

theorem quoteFrom_nonascii (s : List w8) (i : Nat) (h : i < s.length)
    (hc : ¬ (s.getD i (W8 0)).toNat < 0x80) :
    quoteFrom s i = nonASCIIPiece s i (seqLenAt s i) ++ quoteFrom s (i + seqLenAt s i) := by
  rw [quoteFrom]; simp only [h, hc, ↓reduceDIte, ↓reduceIte]

theorem quoteFrom_end (s : List w8) (i : Nat) (h : s.length ≤ i) : quoteFrom s i = [] := by
  rw [quoteFrom]; simp only [show ¬ i < s.length by omega, ↓reduceDIte]

/-- A string index in range, as `Index go.string` reduces it. -/
theorem strIdx_some (s : List w8) (j : w64) (h : uint.nat j < s.length) (h2 : s.length < 2 ^ 63) :
    (if 0 ≤ sint.Z j then s[sint.nat j]? else none) = some (s.getD (uint.nat j) (W8 0)) := by
  have h0 : 0 ≤ sint.Z j := by
    have : uint.nat j < 2 ^ 63 := by omega
    simp only [uint.nat, sint.Z] at *
    rw [BitVec.toInt_eq_toNat_of_lt (by omega)]; omega
  have he : sint.nat j = uint.nat j := by
    simp only [uint.nat, sint.nat, sint.Z] at *
    rw [BitVec.toInt_eq_toNat_of_lt (by omega)]; simp
  simp only [h0, ↓reduceIte]
  rw [he, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The decimal digits of `n` (`AppendUint`'s, `strconv.AppendUint(b, n, 10)`'s). -/
def decNat (n : Nat) : List w8 :=
  if n < 10 then [W8 ((48 + n : Nat) : Int)] else decNat (n / 10) ++ [W8 ((48 + n % 10 : Nat) : Int)]
termination_by n
decreasing_by omega

/-- The last `n` decimal digits of `m`, leading zeros included (`AppendUint`'s buffer after `n` turns
of its loop). -/
def digitsN (m : Nat) : Nat → List w8
  | 0 => []
  | n + 1 => W8 ((48 + m / 10 ^ n % 10 : Nat) : Int) :: digitsN m n

theorem digitsN_length (m n : Nat) : (digitsN m n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [digitsN, ih]

/-- `digitsN` of `m` drops the last digit: the digits of `m / 10`, then `m`'s last. -/
theorem digitsN_succ_snoc (m n : Nat) :
    digitsN m (n + 1) = digitsN (m / 10) n ++ [W8 ((48 + m % 10 : Nat) : Int)] := by
  induction n with
  | zero => simp [digitsN]
  | succ n ih =>
    have h : m / 10 ^ (n + 1) = m / 10 / 10 ^ n := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [digitsN, ih, digitsN, h]
    rfl

/-- Once the loop stops (`m / 10 ^ n = 0`, after at least one digit, the last one taken non-zero
unless `m < 10`), its digits are `decNat m`. -/
theorem digitsN_decNat (m n : Nat) (hn : 1 ≤ n) (hlt : m < 10 ^ n)
    (hge : n = 1 ∨ 10 ^ (n - 1) ≤ m) : digitsN m n = decNat m := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    rw [decNat]
    by_cases h10 : m < 10
    · simp only [h10, ↓reduceIte]
      cases n with
      | zero => simp [digitsN, Nat.mod_eq_of_lt h10]
      | succ k =>
        rcases hge with h | h
        · omega
        · have : 10 ≤ 10 ^ (k + 1) := by
            calc 10 = 10 ^ 1 := rfl
              _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          simp at h; omega
    · simp only [h10, ↓reduceIte]; rw [digitsN_succ_snoc]
      have hn1 : 1 ≤ n := by
        rcases hge with h | h
        · have h0 : n = 0 := by omega
          subst h0; simp at hlt; omega
        · rcases n with _ | n
          · simp at hlt; omega
          · omega
      rw [ih (m / 10) hn1 (by
            rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]; exact hlt)
          (by
            rcases hge with h | h
            · omega
            · right
              rw [Nat.le_div_iff_mul_le (by omega)]
              have : 10 ^ (n - 1) * 10 = 10 ^ (n + 1 - 1) := by
                rw [← Nat.pow_succ]; congr 1; omega
              omega)]

/-- `AppendUint`'s digits for `x`. -/
def decU64 (x : w64) : List w8 := decNat x.toNat

section leaves
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- A leaf of a proof whose result `b` is the one its postcondition names, `a`. -/
theorem val_leaf (Φ : val → IProp GF) (a b : val) (h : b = a) :
    (True -∗ Φ a) ⊢ Φ b := by
  rw [h]; iintro H; iapply H; itrivial

/-- A slice's points-to at equal contents. -/
theorem slice_pts_eq (sl : GoSlice) (l1 l2 : List w8) (h : l1 = l2) :
    (sl ↦* l1 : IProp GF) ⊢ sl ↦* l2 := by
  rw [h]

end leaves

end models_lab.jsoncodec
end Perennial
