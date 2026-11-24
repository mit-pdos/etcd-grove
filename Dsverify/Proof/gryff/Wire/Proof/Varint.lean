/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Varint.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1: the base-128 varint, pure facts

`uvarintEnc` (Go's `PutUvarint`, `Wire/Enc.lean`) and its decoding `uvarintDec`; what
`ReadUvarint`'s loop needs: the encoding is terminated (every byte but the last has the high
bit), two comparable terminated byte lists are equal, the encoding of a `uint64` has at most 10
bytes (the tenth at most `1`), and decoding inverts encoding.
-/
module

public import Dsverify.Proof.gryff.Wire.Enc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff.wire

/-- The value of a little-endian base-128 byte list (each byte's low 7 bits). -/
def uvarintDec : List w8 → Nat
  | [] => 0
  | b :: bs => b.toNat % 128 + 128 * uvarintDec bs

/-- Every byte has the continuation bit. -/
def contBytes (V : List w8) : Prop := ∀ b ∈ V, 128 ≤ b.toNat

/-- Terminated: the continuation bit on every byte but the last. -/
def terminated (V : List w8) : Prop := ∃ V' c, V = V' ++ [c] ∧ contBytes V' ∧ c.toNat < 128

/-- `D` and `V` are comparable: one is a prefix of the other. -/
def comparable (D V : List w8) : Prop := D <+: V ∨ V <+: D

theorem uvarintDec_append (V W : List w8) :
    uvarintDec (V ++ W) = uvarintDec V + 128 ^ V.length * uvarintDec W := by
  induction V with
  | nil => simp [uvarintDec]
  | cons b bs ih =>
    simp only [List.cons_append, uvarintDec, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 128 (128 ^ bs.length)]
    omega

theorem uvarintDec_lt (V : List w8) : uvarintDec V < 128 ^ V.length := by
  induction V with
  | nil => simp [uvarintDec]
  | cons b bs ih =>
    simp only [uvarintDec, List.length_cons, Nat.pow_succ]
    have : b.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
    have h2 : 128 * uvarintDec bs + 128 ≤ 128 * 128 ^ bs.length := by
      have := Nat.mul_le_mul_left 128 (show uvarintDec bs + 1 ≤ 128 ^ bs.length by omega)
      rw [Nat.mul_add] at this; omega
    rw [Nat.mul_comm (128 ^ bs.length)]
    omega

/-- The shape of `uvarintEnc n`: continuation bytes holding `n`'s low groups, then the top
group. -/
theorem uvarintEnc_spec (n : Nat) : ∃ V' c, uvarintEnc n = V' ++ [c] ∧ contBytes V' ∧
    c.toNat < 128 ∧ c.toNat = n / 128 ^ V'.length ∧ (0 < V'.length → 128 ^ V'.length ≤ n) ∧
    uvarintDec V' = n % 128 ^ V'.length := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [uvarintEnc]
    by_cases h : n < 128
    · simp only [h, ↓reduceIte]
      refine ⟨[], BitVec.ofNat 8 n, rfl, by simp [contBytes], ?_, ?_, by simp, by simp [uvarintDec, Nat.mod_one]⟩
      · simp; omega
      · simp; omega
    · simp only [h, ↓reduceIte]
      obtain ⟨V', c, he, hc, hc1, hc2, hc3, hc4⟩ := ih (n / 128) (by omega)
      refine ⟨BitVec.ofNat 8 (n % 128 + 128) :: V', c, by rw [he]; rfl, ?_, hc1, ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · simp; omega
        · exact hc _ hb
      · rw [hc2, List.length_cons, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      · intro _
        simp only [List.length_cons, Nat.pow_succ]
        rcases Nat.eq_zero_or_pos V'.length with h0 | h0
        · rw [h0]; simp only [Nat.pow_zero, Nat.one_mul]; omega
        · have h3 := hc3 h0
          have h4 := Nat.div_mul_le_self n 128
          have h5 : 128 ^ V'.length * 128 ≤ n / 128 * 128 := Nat.mul_le_mul_right 128 h3
          omega
      · simp only [uvarintDec, List.length_cons, hc4]
        have h1 : (BitVec.ofNat 8 (n % 128 + 128)).toNat % 128 = n % 128 := by
          simp
        rw [h1, Nat.pow_succ, Nat.mul_comm (128 ^ V'.length) 128, Nat.mod_mul]

theorem uvarintEnc_terminated (n : Nat) : terminated (uvarintEnc n) := by
  obtain ⟨V', c, he, hc, hc1, -⟩ := uvarintEnc_spec n
  exact ⟨V', c, he, hc, hc1⟩

theorem uvarintDec_enc (n : Nat) : uvarintDec (uvarintEnc n) = n := by
  obtain ⟨V', c, he, -, hc1, hc2, -, hc4⟩ := uvarintEnc_spec n
  rw [he, uvarintDec_append, hc4]
  simp only [uvarintDec, Nat.mod_eq_of_lt hc1, Nat.mul_zero, Nat.add_zero]
  rw [hc2]
  exact Nat.mod_add_div n _

theorem uvarintEnc_inj {a b : Nat} (h : uvarintEnc a = uvarintEnc b) : a = b := by
  rw [← uvarintDec_enc a, ← uvarintDec_enc b, h]

/-- The encoding of a `uint64`: at most 10 bytes, the tenth at most `1`. -/
theorem uvarintEnc_u64 (n : Nat) (hn : n < 2 ^ 64) : ∃ V' c, uvarintEnc n = V' ++ [c] ∧
    contBytes V' ∧ c.toNat < 128 ∧ V'.length ≤ 9 ∧ (V'.length = 9 → c.toNat ≤ 1) := by
  obtain ⟨V', c, he, hc, hc1, hc2, hc3, -⟩ := uvarintEnc_spec n
  have hl : V'.length ≤ 9 := by
    rcases Nat.lt_or_ge 9 V'.length with hlt | hlt
    · have h1 := hc3 (by omega)
      have h2 : 128 ^ 10 ≤ 128 ^ V'.length := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hlt
  refine ⟨V', c, he, hc, hc1, hl, fun h9 => ?_⟩
  rw [hc2, h9]
  have : n / 128 ^ 9 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
  omega

theorem comparable_of_append {A B C : List w8} (h : A <+: B ++ C ∨ B ++ C <+: A) :
    comparable A B := by
  rcases h with h | h
  · have hB : B <+: B ++ C := List.prefix_append _ _
    rcases Nat.le_total A.length B.length with hl | hl
    · left; exact List.prefix_of_prefix_length_le h hB hl
    · right; exact List.prefix_of_prefix_length_le hB h hl
  · right; exact (List.prefix_append _ _).trans h

theorem comparable_mono {A A' B : List w8} (hA : A' <+: A) (h : comparable A B) :
    comparable A' B := by
  rcases h with h | h
  · left; exact hA.trans h
  · rcases Nat.le_total A'.length B.length with hl | hl
    · left; exact List.prefix_of_prefix_length_le hA h hl
    · right; exact List.prefix_of_prefix_length_le h hA hl

/-- Comparable terminated lists are equal. -/
theorem terminated_eq {A B : List w8} (hA : terminated A) (hB : terminated B)
    (h : comparable A B) : A = B := by
  suffices ∀ {A B : List w8}, terminated A → terminated B → A <+: B → A = B by
    rcases h with h | h
    · exact this hA hB h
    · exact (this hB hA h).symm
  intro A B hA hB h
  obtain ⟨C, rfl⟩ := h
  obtain ⟨A', a, rfl, -, ha⟩ := hA
  obtain ⟨B', b, he, hB', -⟩ := hB
  by_cases hC : C = []
  · simp [hC]
  · exfalso
    have h1 : (A' ++ [a] ++ C).dropLast = B' := by
      rw [he]; exact List.dropLast_concat
    rw [List.dropLast_append_of_ne_nil hC] at h1
    have h2 : a ∈ B' := by rw [← h1]; simp
    have := hB' a h2
    omega

/-- One byte `c` of `ReadUvarint` after the continuation bytes `V`, the stream comparable with
the encoding of a `uint64`: a last byte ends the encoding (at most the tenth, at most `1` if the
tenth); a continuation byte is at most the ninth. -/
theorem varint_step (V : List w8) (c : w8) (hV : contBytes V)
    (hcmp : ∃ n0, n0 < 2 ^ 64 ∧ comparable (V ++ [c]) (uvarintEnc n0)) :
    (c.toNat < 128 → ∃ n0, n0 < 2 ^ 64 ∧ V ++ [c] = uvarintEnc n0 ∧ V.length ≤ 9 ∧
      (V.length = 9 → c.toNat ≤ 1)) ∧
    (128 ≤ c.toNat → V.length + 1 ≤ 9) := by
  obtain ⟨n0, hn0, hcmp⟩ := hcmp
  obtain ⟨V0, c0, he, hc0, hc01, hl, hl9⟩ := uvarintEnc_u64 n0 hn0
  constructor
  · intro hc
    have heq := terminated_eq ⟨V, c, rfl, hV, hc⟩ (uvarintEnc_terminated n0) hcmp
    rw [he] at heq
    obtain ⟨rfl, h2⟩ := List.append_inj heq (by
      have := congrArg List.length heq; simp at this; omega)
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    exact ⟨n0, hn0, by rw [he], hl, hl9⟩
  · intro hc
    rw [he] at hcmp
    rcases hcmp with h | h
    · -- `V ++ [c]` is a prefix of `V0 ++ [c0]`
      have hlen := h.length_le
      simp only [List.length_append, List.length_singleton] at hlen
      rcases Nat.lt_or_ge V.length V0.length with hlt | hge
      · omega
      · exfalso
        have heq : V ++ [c] = V0 ++ [c0] := List.IsPrefix.eq_of_length h (by simp; omega)
        obtain ⟨-, h2⟩ := List.append_inj heq (by
          have := congrArg List.length heq; simp at this; omega)
        simp only [List.cons.injEq, and_true] at h2
        subst h2; omega
    · -- `V0 ++ [c0]` is a prefix of `V ++ [c]`
      exfalso
      obtain ⟨t, ht⟩ := h
      by_cases htn : t = []
      · subst htn
        simp only [List.append_nil] at ht
        obtain ⟨-, h2⟩ := List.append_inj ht (by
          have := congrArg List.length ht; simp at this; omega)
        simp only [List.cons.injEq, and_true] at h2
        subst h2; omega
      · have h1 : (V0 ++ [c0] ++ t).dropLast = V := by
          rw [ht]; exact List.dropLast_concat
        rw [List.dropLast_append_of_ne_nil htn] at h1
        have h2 : c0 ∈ V := by rw [← h1]; simp
        have := hV c0 h2
        omega

theorem w64_or_shl (d b k : Nat) (hd : d < 2 ^ k) (hk : k < 64) (hs : d + b * 2 ^ k < 2 ^ 64) :
    W64 (d : Int) ||| W64 (b : Int) <<< W64 (k : Int) = W64 ((d + b * 2 ^ k : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hb : b ≤ b * 2 ^ k := Nat.le_mul_of_pos_right b h1
  simp only [W64, BitVec.ofInt_natCast, BitVec.toNat_or, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have hk' : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [hk', Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : b * 2 ^ k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : d + b * 2 ^ k < 2 ^ 64), Nat.mul_comm b, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt hd, Nat.add_comm]

theorem uvarintDec_snoc (V : List w8) (c : w8) :
    uvarintDec (V ++ [c]) = uvarintDec V + c.toNat % 128 * 2 ^ (7 * V.length) := by
  rw [uvarintDec_append]
  simp only [uvarintDec, Nat.mul_zero, Nat.add_zero, Nat.pow_mul]
  rw [Nat.mul_comm]

theorem pow128 (n : Nat) : 128 ^ n = 2 ^ (7 * n) := by
  rw [Nat.pow_mul]

/-- `ReadUvarint`'s step on a continuation byte: `x |= uint64(b&0x7f) << s`. -/
theorem varint_acc (V : List w8) (c : w8) (hl : V.length + 1 ≤ 9) :
    W64 (uvarintDec V : Int) ||| W64 (uint.Z (c &&& W8 127)) <<< W64 (7 * (V.length : Int)) =
      W64 (uvarintDec (V ++ [c]) : Int) := by
  have h1 : uint.Z (c &&& W8 127) = ((c.toNat % 128 : Nat) : Int) := by
    simp only [uint.Z, W8]
    congr 1
    have : (c &&& BitVec.ofInt 8 127) = c &&& 127#8 := rfl
    rw [this, BitVec.toNat_and]
    show c.toNat &&& 127 = c.toNat % 128
    exact Nat.and_two_pow_sub_one_eq_mod c.toNat 7
  have h2 : 7 * (V.length : Int) = ((7 * V.length : Nat) : Int) := by push_cast; rfl
  rw [h1, h2, uvarintDec_snoc]
  have hd := uvarintDec_lt V
  rw [pow128] at hd
  have hc : c.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  have h3 : 2 ^ (7 * V.length) * 128 ≤ 2 ^ 63 := by
    rw [show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply w64_or_shl _ _ _ hd (by omega)
  have : c.toNat % 128 * 2 ^ (7 * V.length) ≤ 127 * 2 ^ (7 * V.length) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- `ReadUvarint`'s last byte: `x | uint64(b) << s`. -/
theorem varint_last (V : List w8) (c : w8) (n0 : Nat) (hn0 : n0 < 2 ^ 64)
    (he : V ++ [c] = uvarintEnc n0) (hc : c.toNat < 128) (hl : V.length ≤ 9) :
    W64 (uvarintDec V : Int) ||| W64 (uint.Z c) <<< W64 (7 * (V.length : Int)) = W64 (n0 : Int) := by
  have h2 : 7 * (V.length : Int) = ((7 * V.length : Nat) : Int) := by push_cast; rfl
  have hdec : uvarintDec V + c.toNat * 2 ^ (7 * V.length) = n0 := by
    have := uvarintDec_snoc V c
    rw [he, uvarintDec_enc, Nat.mod_eq_of_lt hc] at this
    omega
  rw [h2, show uint.Z c = ((c.toNat : Nat) : Int) from rfl, ← hdec]
  have hd := uvarintDec_lt V
  rw [pow128] at hd
  exact w64_or_shl _ _ _ hd (by omega) (by omega)

theorem comparable_append_eq {A B X Y : List w8} (hl : A.length = B.length)
    (h : comparable (A ++ X) (B ++ Y)) : A = B ∧ comparable X Y := by
  rcases h with h | h
  · obtain ⟨t, ht⟩ := h
    rw [List.append_assoc] at ht
    obtain ⟨h1, h2⟩ := List.append_inj ht hl
    exact ⟨h1, Or.inl ⟨t, h2⟩⟩
  · obtain ⟨t, ht⟩ := h
    rw [List.append_assoc] at ht
    obtain ⟨h1, h2⟩ := List.append_inj ht hl.symm
    exact ⟨h1.symm, Or.inr ⟨t, h2⟩⟩

theorem comparable_symm {A B : List w8} (h : comparable A B) : comparable B A := h.symm

/-- The zigzag of a slice length: twice it. -/
theorem varintEnc_len (len : Nat) (h : len < 2 ^ 63) :
    varintEnc (sint.Z (W64 (len : Int))) = uvarintEnc (2 * len) := by
  have : sint.Z (W64 (len : Int)) = len := by
    simp only [sint.Z, W64, BitVec.toInt_ofInt]
    apply Int.bmod_eq_of_le <;> omega
  rw [varintEnc, this, zigzag]
  simp only [Int.natCast_nonneg, ↓reduceIte]
  congr 1

/-- The bytes after a slice type's fixed fields (as long as its encoding's, `E1`), comparable
with an encoding: they begin a (prefix of a) `uint64` varint. -/
theorem varint_vok {F D E1 E2 : List w8} {len : Nat} (hlen : len < 2 ^ 63)
    (hF : F.length = E1.length)
    (h : comparable (F ++ D) (E1 ++ varintEnc (sint.Z (W64 (len : Int))) ++ E2)) :
    ∃ n : Nat, n < 2 ^ 64 ∧ comparable D (uvarintEnc n) := by
  rw [List.append_assoc] at h
  obtain ⟨-, h2⟩ := comparable_append_eq hF h
  rw [varintEnc_len len hlen] at h2
  refine ⟨2 * len, by omega, ?_⟩
  rcases h2 with h2 | h2
  · exact comparable_of_append (Or.inl h2)
  · exact comparable_of_append (Or.inr h2)

/-- The varint read after the fixed fields is the encoding's. -/
theorem varint_pin {F V P E1 E2 : List w8} {len : Nat} (hlen : len < 2 ^ 63)
    (hF : F.length = E1.length) (hV : terminated V)
    (h : comparable (F ++ (V ++ P)) (E1 ++ varintEnc (sint.Z (W64 (len : Int))) ++ E2)) :
    V = uvarintEnc (2 * len) := by
  rw [List.append_assoc] at h
  obtain ⟨-, h2⟩ := comparable_append_eq hF h
  rw [varintEnc_len len hlen] at h2
  have h3 : comparable (V ++ P) (uvarintEnc (2 * len)) := by
    rcases h2 with h2 | h2
    · exact comparable_of_append (Or.inl h2)
    · exact comparable_of_append (Or.inr h2)
  exact terminated_eq hV (uvarintEnc_terminated _) (comparable_mono (List.prefix_append _ _) h3)

theorem or128 (a : Nat) (h : a < 256) : a ||| 128 = a % 128 + 128 := by
  have hr : a % 128 < 2 ^ 7 := Nat.mod_lt _ (by decide)
  have e : 2 ^ 7 * 1 + a % 128 = 2 ^ 7 * 1 ||| a % 128 := Nat.two_pow_add_eq_or_of_lt hr 1
  rw [show (2 : Nat) ^ 7 * 1 = 128 from rfl] at e
  rcases Nat.lt_or_ge a 128 with h1 | h1
  · have ha : a % 128 = a := Nat.mod_eq_of_lt h1
    rw [ha] at e ⊢
    rw [Nat.or_comm]; omega
  · have ha : a = 128 + a % 128 := by omega
    conv => lhs; rw [ha]
    rw [e, Nat.or_comm (128 ||| _), ← Nat.or_assoc, Nat.or_self, ← e]
    omega

theorem byte_or_128 (xv : w64) :
    (W8 (uint.Z xv) ||| W8 128) = BitVec.ofNat 8 (xv.toNat % 128 + 128) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (W8 (uint.Z xv)).toNat = xv.toNat % 256 := by
    simp [W8, uint.Z]
  have h2 : (W8 128).toNat = 128 := rfl
  rw [BitVec.toNat_or, h1, h2, or128 _ (by omega), BitVec.toNat_ofNat]
  omega

theorem uvarintEnc_step (xv : w64) (h : 128 ≤ uint.nat xv) :
    uvarintEnc (uint.nat xv) =
      BitVec.ofNat 8 (xv.toNat % 128 + 128) :: uvarintEnc (uint.nat (xv >>> W64 7)) := by
  rw [uvarintEnc]
  simp only [show ¬ uint.nat xv < 128 by omega, ↓reduceIte]
  congr 2
  simp [uint.nat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem uvarintEnc_last (xv : w64) (h : uint.nat xv < 128) :
    uvarintEnc (uint.nat xv) = [W8 (uint.Z xv)] := by
  rw [uvarintEnc]
  simp only [h, ↓reduceIte]
  simp [W8, uint.Z, uint.nat]

end Perennial.gryff.wire
