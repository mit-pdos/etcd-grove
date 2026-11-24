/-
Literals in the scanner (`JsonScan`): plain string bytes (`okB`) and plain strings (`strL_full`,
`strL_part`), the decimal digits of a natural number (`decN`, `jsoncodec.AppendUint`'s output),
numbers in the scanner (`numEnd`, `numL_full`, `numL_part`), and the value of decimal digits
(`valD`, `jsoncodec.Digits`). Generic; ported from dsverify-lab's
`examples/vr/proof/VsrProof/Proof/jsoncodec/{Enc,ScanLemmas,DigVal}.lean` (lab master 915f964),
namespace `VsrJson` there.
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.NumSteps
public import Net.Proof.models_lab.jsoncodec.Scan.Steps

@[expose] public section

set_option linter.unusedSimpArgs false

namespace JsonScan

open Perennial

/-- The decimal digits of `n` (`jsoncodec.AppendUint`). -/
def decN (n : Nat) : List w8 :=
  if n < 10 then [BitVec.ofNat 8 (48 + n)] else decN (n / 10) ++ [BitVec.ofNat 8 (48 + n % 10)]
termination_by n
decreasing_by omega

/-- A byte of a plain string's contents as the scanner and the decoders need it (PlainStr's
bytes are). -/
def okB (c : w8) : Prop := 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ 34#8 ∧ c ≠ 92#8

instance okB_dec (c : w8) : Decidable (okB c) := by unfold okB; infer_instance

/-! ## Bytes -/

theorem okB_ne_q {c : w8} (h : okB c) : c ≠ 34#8 := h.2.2.1
theorem okB_ne_bs {c : w8} (h : okB c) : c ≠ 92#8 := h.2.2.2
theorem okB_not_lt {c : w8} (h : okB c) : ¬ c < 32#8 := by
  intro hc; have := h.1; rw [BitVec.lt_def] at hc; simp at hc; omega

/-! ## Strings -/

theorem strL_q_cons (cs : List w8) (j : Nat) : strL (34#8 :: cs) j = (0, j + 1) := by
  rw [strL.eq_def]; simp

theorem strL_ok (c : w8) (cs : List w8) (hc : okB c) (j : Nat) :
    strL (c :: cs) j = strL cs (j + 1) := by
  rw [strL.eq_def]; simp [okB_ne_q hc, okB_not_lt hc, okB_ne_bs hc]

theorem strL_full (s rest : List w8) (hs : ∀ c ∈ s, okB c) (j : Nat) :
    strL (s ++ 34#8 :: rest) j = (0, j + s.length + 1) := by
  induction s generalizing j with
  | nil => simp [strL_q_cons]
  | cons c s ih =>
    have hc := hs c (by simp)
    simp only [List.cons_append, strL_ok c _ hc]
    rw [ih (fun x hx => hs x (by simp [hx]))]
    simp; omega

theorem strL_part (s : List w8) (hs : ∀ c ∈ s, okB c) (j : Nat) :
    strL s j = (1, j + s.length) := by
  induction s generalizing j with
  | nil => rw [strL.eq_def]; simp
  | cons c s ih =>
    have hc := hs c (by simp)
    rw [strL_ok c _ hc]
    rw [ih (fun x hx => hs x (by simp [hx]))]
    simp; omega

/-! ## Numbers -/

theorem decN_eq (n : Nat) :
    decN n = if n < 10 then [BitVec.ofNat 8 (48 + n)]
      else decN (n / 10) ++ [BitVec.ofNat 8 (48 + n % 10)] := by
  rw [decN]

theorem isDig_ofNat (d : Nat) (h : d < 10) : isDig (BitVec.ofNat 8 (48 + d)) = true := by
  have : ∀ d, d < 10 → isDig (BitVec.ofNat 8 (48 + d)) = true := by decide
  exact this d h

theorem decN_digits (n : Nat) : ∀ c ∈ decN n, isDig c = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decN_eq]
    split
    · simp; exact isDig_ofNat n (by omega)
    · intro c hc
      simp at hc
      rcases hc with hc | rfl
      · exact ih (n / 10) (by omega) c hc
      · exact isDig_ofNat _ (by omega)

theorem decN_ne_nil (n : Nat) : decN n ≠ [] := by
  rw [decN_eq]; split <;> simp

theorem decN_head (n : Nat) (h : n ≠ 0) : ∃ c r, decN n = c :: r ∧ c ≠ 48#8 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decN_eq]
    split
    · refine ⟨_, [], rfl, ?_⟩
      intro hc
      have : (BitVec.ofNat 8 (48 + n)).toNat = (48#8 : w8).toNat := by rw [hc]
      simp at this; omega
    · obtain ⟨c, r, h1, h2⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨c, r ++ _, by rw [h1]; rfl, h2⟩

theorem decN_zero : decN 0 = [48#8] := by rw [decN_eq]; rfl

theorem digitsL_digits (ds rest : List w8) (hd : ∀ c ∈ ds, isDig c = true)
    (hr : ∀ c ∈ rest.head?, isDig c = false) (j : Nat) :
    digitsL (ds ++ rest) j = (j + ds.length, rest) := by
  induction ds generalizing j with
  | nil =>
    cases rest with
    | nil => simp [digitsL]
    | cons c r => simp at hr; simp [digitsL, hr]
  | cons c ds ih =>
    simp only [List.cons_append, digitsL, hd c (by simp), if_true]
    rw [ih (fun x hx => hd x (by simp [hx]))]
    simp; omega

/-- A byte that ends a number (after its digits). -/
def numEnd (c : w8) : Prop := isDig c = false ∧ c ≠ 46#8 ∧ c ≠ 101#8 ∧ c ≠ 69#8

theorem numL_full (n : Nat) (c : w8) (r : List w8) (hc : numEnd c) (i : Nat) (eof : Bool) :
    numL (decN n ++ c :: r) i eof = (0, i + (decN n).length) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  by_cases hn : n = 0
  · subst hn
    rw [decN_zero]
    simp [numL, intL, fracL, expL, hc2, hc3, hc4]
  · obtain ⟨d, ds, hdn, hd⟩ := decN_head n hn
    have hdig := decN_digits n
    rw [hdn] at hdig ⊢
    have hd45 : d ≠ 45#8 := by
      intro h; have := hdig d (by simp); rw [h] at this; exact absurd this (by decide)
    have hdl := digitsL_digits (d :: ds) (c :: r) hdig (by simpa using hc1) i
    simp only [List.cons_append] at hdl
    simp only [List.cons_append, numL, hd45, if_false, intL, hd, hdl]
    simp [fracL, expL, hc2, hc3, hc4]

theorem numL_part (p : List w8) (hp : p ≠ []) (hd : ∀ c ∈ p, isDig c = true)
    (h0 : p.head? = some 48#8 → p.length = 1) (i : Nat) :
    numL p i false = (1, i + p.length) := by
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hp
  have hd45 : d ≠ 45#8 := by
    intro h; have := hd d (by simp); rw [h] at this; exact absurd this (by decide)
  by_cases h48 : d = 48#8
  · have := h0 (by simp [h48]); simp at this; subst this; subst h48
    simp [numL, intL, endS]
  · have hdl := digitsL_digits (d :: ds) [] hd (by simp) i
    simp only [List.append_nil] at hdl
    simp only [numL, hd45, if_false, intL, h48, hdl]
    simp [endS]

theorem numEnd_comma : numEnd 44#8 := by unfold numEnd; decide
theorem numEnd_rb : numEnd 125#8 := by unfold numEnd; decide
theorem numEnd_rs : numEnd 93#8 := by unfold numEnd; decide

theorem isDig_ne (c : w8) (h : isDig c = true) :
    spB c = false ∧ c ≠ 91#8 ∧ c ≠ 123#8 ∧ c ≠ 93#8 ∧ c ≠ 34#8 ∧ c ≠ 45#8 := by
  simp only [isDig, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [spB, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq]
  obtain ⟨h1, h2⟩ := h
  and_intros <;> bv_omega

/-! ## Values of digits -/

/-- The value of decimal digits. -/
def valD (ds : List w8) : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

theorem valD_foldl (ds : List w8) (a : Nat) :
    ds.foldl (fun a c => a * 10 + (c.toNat - 48)) a = a * 10 ^ ds.length + valD ds := by
  induction ds generalizing a with
  | nil => simp [valD]
  | cons c ds ih =>
    simp only [List.foldl_cons, valD] at *
    rw [ih, ih (0 * 10 + (c.toNat - 48))]
    simp only [Nat.pow_succ, List.length_cons, Nat.zero_mul, Nat.zero_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm 10 (10 ^ _), Nat.add_assoc]

theorem valD_append (a b : List w8) : valD (a ++ b) = valD a * 10 ^ b.length + valD b := by
  unfold valD; rw [List.foldl_append]; exact valD_foldl b _

theorem valD_single (c : w8) : valD [c] = c.toNat - 48 := by simp [valD]

theorem valD_decN (n : Nat) : valD (decN n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [decN_eq]
    split
    · rw [valD_single]; simp; omega
    · rw [valD_append, ih (n / 10) (by omega), valD_single]; simp; omega

theorem valD_le_append (a b : List w8) : valD a ≤ valD (a ++ b) := by
  rw [valD_append]
  have : 1 ≤ 10 ^ b.length := Nat.one_le_pow _ _ (by omega)
  have := Nat.mul_le_mul_left (valD a) this
  omega

/-! ## A number or a plain string alone in the scanner -/

theorem goL_num_top (n : Nat) (c : w8) (r : List w8) (hc : numEnd c) (i : Nat) (eOK eof : Bool) :
    goL (decN n ++ c :: r) i [] 0 eOK eof = (0, i + (decN n).length) := by
  obtain ⟨d, ds, hdn⟩ : ∃ d ds, decN n = d :: ds := by
    cases h : decN n with
    | nil => exact absurd h (decN_ne_nil n)
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hdd : isDig d = true := decN_digits n d (by rw [hdn]; simp)
  obtain ⟨hsp, h1, h2, h3, h34, -⟩ := isDig_ne d hdd
  have hnum := numL_full n c r hc i (eof && ([] : List w8).isEmpty)
  rw [hdn] at *
  simp only [List.cons_append]
  rw [goL_scalar (hs := hsp) (hc1 := h1) (hc2 := h2) (hc3 := h3)]
  simp only [scalarL, h34, hdd, or_true, if_true, if_false, ite_false, ite_true]
  simp only [List.cons_append] at hnum
  rw [hnum]
  simp

theorem goL_str_top (s rest : List w8) (hs : ∀ c ∈ s, okB c) (i : Nat) (eOK eof : Bool) :
    goL (34#8 :: (s ++ 34#8 :: rest)) i [] 0 eOK eof = (0, i + s.length + 2) := by
  rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
  simp only [scalarL, if_true, ite_true, strL_full s _ hs]
  simp; omega

/-- A number (its digits, then a byte that ends it) is one value to the scanner. -/
theorem scanL_num (n : Nat) (c : w8) (rest : List w8) (hc : numEnd c) :
    scanL (decN n ++ c :: rest) true = (0, (decN n).length) := by
  have := goL_num_top n c rest hc 0 false true
  simpa [scanL] using this

/-- A plain string is one value to the scanner. -/
theorem scanL_str (s rest : List w8) (hs : ∀ c ∈ s, okB c) :
    scanL (34#8 :: (s ++ 34#8 :: rest)) true = (0, s.length + 2) := by
  have := goL_str_top s rest hs 0 false true
  simpa [scanL] using this

end JsonScan
