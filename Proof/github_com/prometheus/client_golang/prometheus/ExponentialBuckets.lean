/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/ExponentialBuckets.lean` over the
translated `ExponentialBuckets` (client_golang v1.24.1, `histogram.go:315`): the three panic guards
are false under `expBucketsArgsOk` and `factor = 2.0`, and each `start *= factor` doubles a positive
normal float64 exactly (`float64Mul_two_normal`), except the one after the last bucket, whose
result is never read. Until 2026-11-23 a trust-boundary axiom.

The float facts (`pow2`, `floorLog2`, the doubling law) are about Perennial's IEEE 754 model
(`Perennial/Golang/Defn/Float.lean`) and belong in Perennial's `Theory/Float.lean`; private here
until they move there (`notes/perennial-changes.md`, "`ExponentialBuckets` and `math.Ceil` after the
IEEE 754 floats").
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.ExponentialBuckets

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI ieee754

namespace ExponentialBucketsFloat

private theorem pow2_nat (n : Nat) : pow2 (n : Int) = ((2 ^ n : Nat) : Rat) := by
  simp [pow2]

private theorem pow2_neg_succ (n : Nat) : pow2 (-((n : Int) + 1)) = (((2 ^ (n + 1) : Nat) : Rat))⁻¹ := by
  unfold pow2
  simp only [show ¬ (0 ≤ -((n : Int) + 1)) by omega, ↓reduceIte]
  congr

private theorem pow2_pos (k : Int) : 0 < pow2 k := by
  unfold pow2
  have h : ∀ n : Nat, (0 : Rat) < ((2 ^ n : Nat) : Rat) := fun n => by
    have : (0 : Nat) < 2 ^ n := Nat.two_pow_pos _
    exact_mod_cast this
  split
  · exact h _
  · exact Rat.inv_pos.mpr (h _)

private theorem pow2_succ (k : Int) : pow2 (k + 1) = 2 * pow2 k := by
  rcases Int.lt_or_le k 0 with hk | hk
  · obtain ⟨n, hn⟩ : ∃ n : Nat, k = -((n : Int) + 1) := ⟨(-k - 1).toNat, by omega⟩
    subst hn
    rw [pow2_neg_succ]
    cases n with
    | zero =>
      rw [show -(((0 : Nat) : Int) + 1) + 1 = ((0 : Nat) : Int) by omega, pow2_nat]
      decide +kernel
    | succ n =>
      rw [show -(((n + 1 : Nat) : Int) + 1) + 1 = -((n : Int) + 1) by omega, pow2_neg_succ]
      have h2 : ((2 ^ (n + 1 + 1) : Nat) : Rat) = 2 * ((2 ^ (n + 1) : Nat) : Rat) := by
        push_cast [Nat.pow_succ]; grind
      rw [h2, Rat.inv_mul_rev, ← Rat.mul_assoc, Rat.mul_comm 2, Rat.mul_assoc,
        Rat.mul_inv_cancel 2 (by decide), Rat.mul_one]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega, pow2_nat, pow2_nat]
    push_cast [Nat.pow_succ]
    grind

private theorem pow2_add_nat (a : Int) (n : Nat) : pow2 (a + n) = pow2 a * pow2 n := by
  induction n with
  | zero => simp [pow2]
  | succ n ih =>
    rw [show a + ((n + 1 : Nat) : Int) = (a + n) + 1 by omega, pow2_succ, ih,
      show ((n + 1 : Nat) : Int) = (n : Int) + 1 by omega, pow2_succ]
    grind

private theorem pow2_sub_nat (a : Int) (n : Nat) : pow2 (a - n) = pow2 a * pow2 (-(n : Int)) := by
  have h := pow2_add_nat (a - n) n
  rw [show a - n + n = a by omega] at h
  have h2 := pow2_add_nat (-(n : Int)) n
  rw [show -(n : Int) + n = 0 by omega, show pow2 0 = 1 by simp [pow2]] at h2
  -- h : pow2 a = pow2 (a - n) * pow2 n ; h2 : 1 = pow2 (-n) * pow2 n
  rw [h, Rat.mul_assoc, Rat.mul_comm (pow2 n), ← h2, Rat.mul_one]

private theorem pow2_add (a b : Int) : pow2 (a + b) = pow2 a * pow2 b := by
  rcases Int.lt_or_le b 0 with hb | hb
  · obtain ⟨n, hn⟩ : ∃ n : Nat, b = -(n : Int) := ⟨(-b).toNat, by omega⟩
    subst hn
    rw [show a + -(n : Int) = a - n by omega, pow2_sub_nat]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    exact pow2_add_nat a n

private theorem pow2_lt {a b : Int} (h : a < b) : pow2 a < pow2 b := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, b = a + ((n + 1 : Nat) : Int) := ⟨(b - a - 1).toNat, by omega⟩
  subst hn
  rw [pow2_add, pow2_nat]
  have h1 : (1 : Rat) < ((2 ^ (n + 1) : Nat) : Rat) := by
    have : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    exact_mod_cast this
  have := (Rat.mul_lt_mul_left (pow2_pos a)).mpr h1
  rwa [Rat.mul_one] at this

private theorem pow2_le {a b : Int} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  rcases Int.lt_or_le a b with h' | h'
  · exact Rat.le_of_lt (pow2_lt h')
  · rw [show a = b by omega]; exact Rat.le_refl

private theorem lt_of_pow2_lt {a b : Int} (h : pow2 a < pow2 b) : a < b := by
  rcases Int.lt_or_le a b with h' | h'
  · exact h'
  · exact absurd h (Rat.not_lt.mpr (pow2_le h'))

private theorem cross_lt {X Y Z W : Rat} (hY : 0 < Y) (hW : 0 < W) (h : X * W < Z * Y) :
    X * Y⁻¹ < Z * W⁻¹ := by
  have hp : 0 < Y⁻¹ * W⁻¹ := by
    have := (Rat.mul_lt_mul_left (Rat.inv_pos.mpr hY)).mpr (Rat.inv_pos.mpr hW)
    rwa [Rat.mul_zero] at this
  have hY0 : Y ≠ 0 := (Rat.ne_of_lt hY).symm
  have hW0 : W ≠ 0 := (Rat.ne_of_lt hW).symm
  have e1 : X * Y⁻¹ = (X * W) * (Y⁻¹ * W⁻¹) := by
    rw [Rat.mul_comm Y⁻¹, ← Rat.mul_assoc, Rat.mul_assoc X, Rat.mul_inv_cancel W hW0, Rat.mul_one]
  have e2 : Z * W⁻¹ = (Z * Y) * (Y⁻¹ * W⁻¹) := by
    rw [← Rat.mul_assoc, Rat.mul_assoc Z, Rat.mul_inv_cancel Y hY0, Rat.mul_one]
  rw [e1, e2]
  exact Rat.mul_lt_mul_of_pos_right h hp

private theorem natCast_pos {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) := by exact_mod_cast h

/-- `floorLog2 a` is the `e` with `2 ^ e ≤ a < 2 ^ (e + 1)`. -/
private theorem floorLog2_eq {a : Rat} {e : Int} (h1 : pow2 e ≤ a) (h2 : a < pow2 (e + 1)) :
    floorLog2 a = e := by
  have ha : 0 < a := by have := pow2_pos e; grind
  have hnum : 0 < a.num := by
    have := (Rat.lt_iff 0 a).mp ha
    simpa using this
  generalize hn : a.num.toNat = n
  generalize hd : a.den = d
  have hn0 : n ≠ 0 := by omega
  have hd0 : d ≠ 0 := by rw [← hd]; exact a.den_nz
  have hadef : a = (n : Rat) * (d : Rat)⁻¹ := by
    rw [← Rat.div_def]
    have := Rat.num_divInt_den a
    rw [Rat.divInt_eq_div] at this
    have hnn : (a.num : Rat) = ((n : Int) : Rat) := by rw [← hn, Int.toNat_of_nonneg (by omega)]
    rw [hnn, hd] at this
    rw [← this]
    norm_cast
  generalize hi : n.log2 = i
  generalize hj : d.log2 = j
  have hi1 : 2 ^ i ≤ n := hi ▸ Nat.log2_self_le hn0
  have hi2 : n < 2 ^ (i + 1) := hi ▸ Nat.lt_log2_self
  have hj1 : 2 ^ j ≤ d := hj ▸ Nat.log2_self_le hd0
  have hj2 : d < 2 ^ (j + 1) := hj ▸ Nat.lt_log2_self
  have hlow : pow2 ((i : Int) - j - 1) < a := by
    rw [show (i : Int) - j - 1 = (i : Int) + -((j : Int) + 1) by omega, pow2_add, pow2_nat,
      pow2_neg_succ, hadef]
    apply cross_lt (natCast_pos (Nat.two_pow_pos _)) (natCast_pos (by omega))
    have : 2 ^ i * d < n * 2 ^ (j + 1) :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hj2 (Nat.two_pow_pos _))
        (Nat.mul_le_mul_right _ hi1)
    exact_mod_cast this
  have hhigh : a < pow2 ((i : Int) - j + 1) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, show (i : Int) - ((0 : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) by omega, pow2_nat,
        hadef]
      have hd1 : d = 1 := by have := hj2; rw [hj0] at this; omega
      rw [hd1]
      have : (n : Rat) < ((2 ^ (i + 1) : Nat) : Rat) := by exact_mod_cast hi2
      rw [show ((1 : Nat) : Rat)⁻¹ = 1 by decide +kernel, Rat.mul_one]
      exact this
    · obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [show (i : Int) - j + 1 = ((i + 1 : Nat) : Int) + -((j' : Int) + 1) by omega, pow2_add,
        pow2_nat, pow2_neg_succ, hadef, ← hj']
      apply cross_lt (natCast_pos (by omega)) (natCast_pos (Nat.two_pow_pos _))
      have : n * 2 ^ j < 2 ^ (i + 1) * d :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hi2 (Nat.two_pow_pos _))
          (Nat.mul_le_mul_left _ hj1)
      exact_mod_cast this
  unfold floorLog2
  simp only
  rw [hn, hd, hi, hj]
  split
  · rename_i hc
    have := lt_of_pow2_lt (show pow2 e < pow2 ((i : Int) - j + 1) by grind)
    have := lt_of_pow2_lt (show pow2 ((i : Int) - j) < pow2 (e + 1) by grind)
    omega
  · rename_i hc
    have hc' := Rat.not_le.mp hc
    have := lt_of_pow2_lt (show pow2 e < pow2 ((i : Int) - j) by grind)
    have := lt_of_pow2_lt (show pow2 ((i : Int) - j - 1) < pow2 (e + 1) by grind)
    omega

private theorem floor_natCast' (n : Nat) : (n : Rat).floor = n := by
  rw [Rat.floor_def]; simp

private theorem roundHalfEven_nat (n : Nat) : roundHalfEven (n : Rat) = n := by
  unfold roundHalfEven
  simp only [floor_natCast']
  rw [if_pos (Or.inl (by
    have : ((n : Int) : Rat) = (n : Rat) := by norm_cast
    rw [this, Rat.sub_self]; decide +kernel))]
  simp

private theorem b64_t : binary64.t = 52 := rfl
private theorem b64_w : binary64.w = 11 := rfl
private theorem b64_bias : binary64.bias = 1023 := by decide +kernel
private theorem b64_emax : binary64.emax = 1023 := by decide +kernel
private theorem b64_emin : binary64.emin = -1022 := by decide +kernel

/-- The value of a positive normal `float64` (biased exponent `E` in `[1, 2046]`, trailing
significand `T`): `(2^52 + T) * 2^(E - 1075)`. -/
private theorem decode_normal64 (x : w64) (E T : Nat) (hx : x.toNat = E * 2 ^ 52 + T) (hT : T < 2 ^ 52)
    (hE1 : 1 ≤ E) (hE2 : E ≤ 2046) :
    binary64.decode x = .finite false (((2 ^ 52 + T : Nat) : Rat) * pow2 ((E : Int) - 1075)) := by
  have hmsb : x.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  have hE : x.toNat / 2 ^ 52 % 2 ^ 11 = E := by omega
  have hTT : x.toNat % 2 ^ 52 = T := by omega
  unfold Format.decode
  simp only [b64_t, b64_w, b64_bias, hmsb, hE, hTT]
  rw [if_neg (by omega), if_neg (by omega), Lean.Grind.Semiring.natCast_add,
    Lean.Grind.Semiring.natCast_pow, show (E : Int) - 1023 - ((52 : Nat) : Int) = (E : Int) - 1075 by omega]
  rfl

private theorem decode_two64 : binary64.decode (W64 0x4000000000000000) = .finite false 2 := by
  decide +kernel

private theorem decode_one64 : binary64.decode (W64 0x3FF0000000000000) = .finite false 1 := by
  decide +kernel

private theorem decode_zero64' : binary64.decode (W64 0) = .finite false 0 := by
  decide +kernel

private theorem pack64_toNat (E T : Nat) (hE : E < 2 ^ 11) (hT : T < 2 ^ 52) :
    (binary64.pack false E T).toNat = E * 2 ^ 52 + T := by
  change (BitVec.ofBool false ++ BitVec.ofNat 11 E ++ BitVec.ofNat 52 T).toNat = _
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hE, Nat.mod_eq_of_lt hT, ← Nat.shiftLeft_add_eq_or_of_lt hT,
    ← Nat.shiftLeft_add_eq_or_of_lt hE, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  simp

private theorem floorLog2_normal (N : Nat) (k : Int) (h1 : 2 ^ 52 ≤ N) (h2 : N < 2 ^ 53) :
    floorLog2 ((N : Rat) * pow2 k) = 52 + k := by
  apply floorLog2_eq
  · have h52 : pow2 52 = ((2 ^ 52 : Nat) : Rat) := pow2_nat 52
    rw [pow2_add, h52]
    apply Rat.mul_le_mul_of_nonneg_right _ (Rat.le_of_lt (pow2_pos k))
    exact_mod_cast h1
  · rw [show 52 + k + 1 = ((53 : Nat) : Int) + k by omega, pow2_add, pow2_nat]
    apply Rat.mul_lt_mul_of_pos_right _ (pow2_pos k)
    exact_mod_cast h2

private theorem pow2_mul_neg (k : Int) : pow2 k * pow2 (-k) = 1 := by
  rw [← pow2_add, show k + -k = 0 by omega]; simp [pow2]

/-- Doubling a positive normal `float64` whose double is normal: exact, `2^52` added to the
bits. -/
private theorem float64Mul_two_normal (x f : w64) (h1 : 2 ^ 52 ≤ x.toNat)
    (h2 : x.toNat + 2 ^ 52 < 0x7FF0000000000000)
    (hf : float64Encodes (float64Mul x (W64 0x4000000000000000)) f) :
    f.toNat = x.toNat + 2 ^ 52 := by
  generalize hE : x.toNat / 2 ^ 52 = E
  generalize hT : x.toNat % 2 ^ 52 = T
  have hx : x.toNat = E * 2 ^ 52 + T := by omega
  have hT' : T < 2 ^ 52 := by omega
  have hE1 : 1 ≤ E := by omega
  have hE2 : E ≤ 2045 := by omega
  generalize hN : 2 ^ 52 + T = N
  have hN1 : 2 ^ 52 ≤ N := by omega
  have hN2 : N < 2 ^ 53 := by omega
  have hmax : max (52 + ((E : Int) - 1074)) (-1022) = 52 + ((E : Int) - 1074) := by omega
  have hr : (N : Rat) * pow2 ((E : Int) - 1074) * pow2 (((52 : Nat) : Int) - (52 + ((E : Int) - 1074))) =
      (N : Rat) := by
    rw [Rat.mul_assoc, ← pow2_add,
      show (E : Int) - 1074 + (((52 : Nat) : Int) - (52 + ((E : Int) - 1074))) = 0 by omega,
      show pow2 0 = 1 by simp [pow2], Rat.mul_one]
  have hm : float64Mul x (W64 0x4000000000000000) =
      .finite false ((N : Rat) * pow2 ((E : Int) - 1074)) := by
    simp only [float64Mul, Format.mul_unseal, Format.mulDef]
    rw [decode_normal64 x E T hx hT' hE1 (by omega), decode_two64]
    simp only [Bool.xor_false]
    rw [hN, Rat.mul_assoc, Rat.mul_comm (pow2 _), ← pow2_succ, show (E : Int) - 1075 + 1 = (E : Int) - 1074 by omega]
    unfold Format.round
    simp only [b64_t, b64_emin, b64_emax, floorLog2_normal N _ hN1 hN2]
    have he : 52 + ((E : Int) - 1074) - ((52 : Nat) : Int) = (E : Int) - 1074 := by omega
    simp only [hmax, hr, roundHalfEven_nat, he]
    have hp := pow2_pos ((E : Int) - 1074)
    have hlt : (N : Rat) * pow2 ((E : Int) - 1074) < pow2 (1023 + 1) := by
      rw [show (1023 + 1 : Int) = ((53 : Nat) : Int) + (((E : Int) - 1074) + (971 - ((E : Int) - 1074))) by omega,
        pow2_add, pow2_add, ← Rat.mul_assoc, pow2_nat]
      have hq : 1 ≤ pow2 (971 - ((E : Int) - 1074)) := by
        have := pow2_le (show (0 : Int) ≤ 971 - ((E : Int) - 1074) by omega)
        simpa [pow2] using this
      have hN' : (N : Rat) < ((2 ^ 53 : Nat) : Rat) := by exact_mod_cast hN2
      have := Rat.mul_lt_mul_of_pos_right hN' hp
      have h0 : 0 ≤ ((2 ^ 53 : Nat) : Rat) * pow2 ((E : Int) - 1074) :=
        Rat.le_of_lt (Rat.mul_pos (by decide +kernel) hp)
      have h3 := Rat.mul_le_mul_of_nonneg_left hq h0
      rw [Rat.mul_one] at h3
      grind
    rw [if_pos hlt]
  rw [hm] at hf
  simp only [float64Encodes, Format.encodes, Format.encode] at hf
  simp only [b64_t, b64_emin, b64_bias, floorLog2_normal N _ hN1 hN2] at hf
  simp only [hmax, hr, floor_natCast', Int.toNat_natCast] at hf
  rw [if_neg (by omega)] at hf
  simp only at hf
  subst hf
  rw [show (52 + ((E : Int) - 1074) + 1023).toNat = E + 1 by omega, show N - 2 ^ 52 = T by omega]
  rw [show BitVec.toNat x + 2 ^ 52 = (E + 1) * 2 ^ 52 + T by omega]
  exact pack64_toNat _ _ (by omega) hT'

private theorem float64Leb_normal_zero (x : w64) (h1 : 2 ^ 52 ≤ x.toNat) (h2 : x.toNat < 0x7FF0000000000000) :
    float64Leb x (W64 0) = false := by
  have hd := decode_normal64 x (x.toNat / 2 ^ 52) (x.toNat % 2 ^ 52) (by omega) (by omega) (by omega)
    (by omega)
  simp only [float64Leb, Format.leb_unseal, Format.lebDef, hd, decode_zero64', signed]
  have hp := pow2_pos (((x.toNat / 2 ^ 52 : Nat) : Int) - 1075)
  have hn : (0 : Rat) < ((2 ^ 52 + x.toNat % 2 ^ 52 : Nat) : Rat) := natCast_pos (by omega)
  have := Rat.mul_pos hn hp
  simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, Rat.not_le]
  exact this

private theorem float64Leb_two_one : float64Leb (W64 0x4000000000000000) (W64 0x3FF0000000000000) = false := by
  simp only [float64Leb, Format.leb_unseal, Format.lebDef, decode_two64, decode_one64]
  decide +kernel

end ExponentialBucketsFloat

open ExponentialBucketsFloat

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

theorem prometheus.ExponentialBuckets.wp_proof :
    prometheus.ExponentialBuckets.spec (GF := GF) (hG := hG) := by
  intro start factor count hf hok
  subst hf
  obtain ⟨hs1, hc1, hlast⟩ := hok
  have hsn : uint.nat start < 0x7FF0000000000000 := by omega
  wp_start
  wp_auto
  wp_if_destruct
  · exfalso; rename_i h; have : sint.Z (W64 1) = 1 := rfl; omega
  try wp_auto
  rw [float64Leb_normal_zero start (by word) (by word)]
  try wp_auto
  rw [show float64Two = W64 0x4000000000000000 from rfl, float64Leb_two_one]
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) count $$ [] as %sl ⟨Hsl, -⟩
  · ipureintro; omega
  try wp_auto
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  rename_i ik_ptr
  irename : (ik_ptr ↦ zero_val w64 : IProp GF) => ik
  ihave IH : iprop(∃ (j k cur : w64),
      "i" ∷ i_ptr ↦ j ∗ "ik" ∷ ik_ptr ↦ k ∗ "start" ∷ start_ptr ↦ cur ∗
      "Hsl" ∷ sl ↦* (expBuckets start (sint.nat j) ++
        List.replicate (sint.nat count - sint.nat j) (zero_val w64)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z count ∧
        (sint.Z j < sint.Z count → cur = W64 (uint.Z start + sint.Z j * 2 ^ 52))⌝)
    $$ [i ik start Hsl]
  · iexists W64 0, W64 0, start
    simp only [show sint.nat (W64 0) = 0 from rfl, show sint.Z (W64 0) = 0 from rfl, Nat.sub_zero]
    iframe
    ipureintro
    refine ⟨by decide, by omega, fun _ => by word⟩
  have Hlen : sint.Z sl.len = sint.Z count := by
    rw [List.length_replicate] at Hsll; word
  have Hexp : ∀ m : Nat, (expBuckets start m).length = m := fun m => by
    simp [expBuckets]
  wp_for IH
  wp_if_destruct
  · rw [if_pos ⟨Hj.1, Hif⟩]
    have Hjn : sint.nat j < sint.nat count := by word
    have Hget : (expBuckets start (sint.nat j) ++
        List.replicate (sint.nat count - sint.nat j) (zero_val w64))[(sint.Z j).toNat]? =
        some (zero_val w64) := by
      rw [show (sint.Z j).toNat = sint.nat j by word, List.getElem?_append_right (Nat.le_of_eq (Hexp _)),
        Hexp, Nat.sub_self, List.getElem?_replicate]
      rw [if_pos (by omega)]
    wp_apply wp_load_slice_index sl (sint.Z j) _ (DFrac.own 1) (zero_val w64) Hj.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hget
    try wp_auto
    rw [if_pos ⟨Hj.1, Hif⟩]
    wp_apply wp_store_slice_index sl (sint.Z j) _ cur $$ [$Hsl] as Hsl
    · ipureintro; refine ⟨Hj.1, ?_⟩
      rw [List.length_append, Hexp, List.length_replicate]; word
    try wp_auto
    wp_apply wp_float64_mul as %f %Hf
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, j, f
    have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have Hcur : cur = W64 (uint.Z start + ((sint.nat j : Nat) : Int) * 2 ^ 52) := by
      rw [Hj.2.2 (by word), show ((sint.nat j : Nat) : Int) = sint.Z j by word]
    have Hset : (expBuckets start (sint.nat j) ++
        List.replicate (sint.nat count - sint.nat j) (zero_val w64)).set (sint.Z j).toNat cur =
        expBuckets start (sint.nat j + 1) ++
          List.replicate (sint.nat count - (sint.nat j + 1)) (zero_val w64) := by
      rw [show (sint.Z j).toNat = sint.nat j by word]
      rw [List.set_append_right _ _ (Nat.le_of_eq (Hexp _))]
      rw [Hexp, Nat.sub_self]
      rw [show sint.nat count - sint.nat j = (sint.nat count - (sint.nat j + 1)) + 1 by omega]
      rw [List.replicate_succ, List.set_cons_zero]
      simp only [expBuckets, List.range_succ, List.map_append, List.map_singleton, List.append_assoc,
        List.singleton_append, Hcur]
    rw [Hj1, Hset]
    iframe
    ipureintro
    refine ⟨by word, by word, fun hlt => ?_⟩
    -- the double of the current bucket, still normal
    have hlast' : uint.nat start + (sint.nat j + 1) * 2 ^ 52 < 0x7FF0000000000000 := by
      have h1 : sint.Z j + 1 < sint.Z count := by word
      have h2 : ((sint.nat j : Nat) : Int) = sint.Z j := by word
      have : sint.nat j + 1 ≤ (sint.Z count).toNat.pred := by rw [Nat.pred_eq_sub_one]; omega
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right (2 ^ 52) this) _) hlast
    have hcn : uint.nat cur = uint.nat start + sint.nat j * 2 ^ 52 := by
      rw [Hcur]; word
    have hf := float64Mul_two_normal cur f (by word) (by word) Hf
    have hf' : uint.nat f = uint.nat start + (sint.nat j + 1) * 2 ^ 52 := by
      have : uint.nat f = uint.nat cur + 2 ^ 52 := hf
      rw [this, hcn, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    word
  · have Hjc : sint.nat j = (sint.Z count).toNat := by word
    rw [Hjc, Nat.sub_self, List.replicate_zero, List.append_nil]
    try wp_auto
    iapply HΦ $$ Hsl

end proof

end EtcdGrove
end Perennial
