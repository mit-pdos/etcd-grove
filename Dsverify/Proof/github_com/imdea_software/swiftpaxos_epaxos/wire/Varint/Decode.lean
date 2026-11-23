/-
Decoding facts for `readUvarint`: the low seven bits of continuation bytes (`low7`), and what a
prefix of `uvarintEnc n ++ _` made of continuation bytes says about `n`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.PutUvarint

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

/-- The value of the low seven bits of `d`'s bytes, least significant first. -/
def low7 : List w8 → Nat
  | [] => 0
  | c :: d => c.toNat % 128 + 128 * low7 d

theorem low7_append (d : List w8) (c : w8) :
    low7 (d ++ [c]) = low7 d + c.toNat % 128 * 128 ^ d.length := by
  induction d with
  | nil => simp [low7]
  | cons a d ih =>
    simp only [List.cons_append, low7, ih, List.length_cons, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

theorem low7_lt (d : List w8) : low7 d < 128 ^ d.length := by
  induction d with
  | nil => simp [low7]
  | cons a d ih =>
    simp only [low7, List.length_cons, Nat.pow_succ]
    have : a.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
    omega

theorem w8_toNat_W8_nat (n : Nat) : (W8 (n : Int)).toNat = n % 256 := by
  simp [W8]

theorem w8_toNat_W8_cont (n : Nat) : (W8 ((n : Int) % 128 + 128)).toNat = n % 128 + 128 := by
  simp [W8]; omega

/-- A prefix of continuation bytes of `uvarintEnc n ++ ext`. -/
theorem uvarintEnc_cont (d : List w8) (hd : ∀ c ∈ d, 128 ≤ c.toNat) :
    ∀ (n : Nat) (ext : List w8), d <+: uvarintEnc n ++ ext →
      uvarintEnc n = d ++ uvarintEnc (n / 128 ^ d.length) ∧ n % 128 ^ d.length = low7 d := by
  induction d with
  | nil => intro n ext _; simp [low7, Nat.mod_one]
  | cons c d ih =>
    intro n ext h
    have hc := hd c (by simp)
    by_cases hn : n < 128
    · rw [uvarintEnc_lt _ hn] at h
      obtain ⟨t, ht⟩ := h
      simp only [List.cons_append, List.cons.injEq] at ht
      rw [ht.1, w8_toNat_W8_nat] at hc
      omega
    · rw [uvarintEnc_ge _ (by omega)] at h ⊢
      obtain ⟨t, ht⟩ := h
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨h1, h2⟩ := ht
      obtain ⟨e1, e2⟩ := ih (fun c hc => hd c (by simp [hc])) (n / 128) ext ⟨t, h2⟩
      have hcn : c.toNat = n % 128 + 128 := by rw [h1, w8_toNat_W8_cont]
      refine ⟨?_, ?_⟩
      · rw [h1, e1, List.length_cons, Nat.pow_succ', ← Nat.div_div_eq_div_mul]; rfl
      · simp only [low7, List.length_cons, Nat.pow_succ', hcn, ← e2]
        rw [Nat.mod_mul]; omega

theorem uvarintEnc_length_le (n k : Nat) (hk : 1 ≤ k) (h : n < 128 ^ k) :
    (uvarintEnc n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    by_cases hn : n < 128
    · rw [uvarintEnc_lt _ hn]; simp
    · rw [uvarintEnc_ge _ (by omega)]
      simp only [List.length_cons]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp at h; omega
      · have := ih (n / 128) hk0 (by rw [Nat.pow_succ] at h; omega)
        omega

theorem uvarintEnc_length_le_10 (n : Nat) (h : n < 2 ^ 64) : (uvarintEnc n).length ≤ 10 :=
  uvarintEnc_length_le n 10 (by decide) (by omega)

/-- A continuation byte read: at most nine of them. -/
theorem cont_length (d : List w8) (hd : ∀ c ∈ d, 128 ≤ c.toNat) (n : Nat) (ext : List w8)
    (hn : n < 2 ^ 64) (h : d <+: uvarintEnc n ++ ext) : d.length ≤ 9 := by
  have e := (uvarintEnc_cont d hd n ext h).1
  have h1 := uvarintEnc_length_le_10 n hn
  have h2 := uvarintEnc_length_pos (n / 128 ^ d.length)
  rw [e, List.length_append] at h1
  omega

/-- The last byte read: the encoding is complete. -/
theorem final_byte (d : List w8) (hd : ∀ c ∈ d, 128 ≤ c.toNat) (b : w8) (hb : b.toNat < 128)
    (n : Nat) (ext : List w8) (hn : n < 2 ^ 64) (h : d ++ [b] <+: uvarintEnc n ++ ext) :
    uvarintEnc n = d ++ [b] ∧ n = low7 d + b.toNat * 128 ^ d.length ∧
      (d.length = 9 → b.toNat ≤ 1) := by
  obtain ⟨e1, e2⟩ := uvarintEnc_cont d hd n ext ((List.prefix_append _ _).trans h)
  rw [e1, List.append_assoc] at h
  have h' := (List.prefix_append_right_inj d).mp h
  obtain ⟨m, hm⟩ : ∃ m, m = n / 128 ^ d.length := ⟨_, rfl⟩
  rw [← hm] at e1 h'
  have hm128 : m < 128 := by
    refine Classical.byContradiction fun hc => ?_
    rw [uvarintEnc_ge _ (by omega)] at h'
    obtain ⟨t, ht⟩ := h'
    simp only [List.cons_append, List.cons.injEq] at ht
    rw [ht.1, w8_toNat_W8_cont] at hb
    omega
  rw [uvarintEnc_lt _ hm128] at h' e1
  obtain ⟨t, ht⟩ := h'
  simp only [List.cons_append, List.cons.injEq] at ht
  have hbm : b.toNat = m := by rw [ht.1, w8_toNat_W8_nat]; omega
  refine ⟨by rw [e1, ht.1], ?_, ?_⟩
  · rw [← e2, hbm, hm, Nat.mul_comm]; exact (Nat.mod_add_div n _).symm
  · intro h9
    rw [h9] at hm
    have : m < 2 := by
      rw [hm]; apply Nat.div_lt_of_lt_mul; omega
    omega

/-- `x | uint64(c) << s` when `x`'s bits are below `s`. -/
theorem or_shl_toNat (xv : w64) (c : w64) (k : Nat) (hk : k < 64)
    (hx : xv.toNat < 2 ^ k) (hsum : xv.toNat + c.toNat * 2 ^ k < 2 ^ 64) :
    (xv ||| (c <<< (W64 (k : Int)))).toNat = xv.toNat + c.toNat * 2 ^ k := by
  have hW : (W64 (k : Int)).toNat = k := by simp [W64]; omega
  rw [BitVec.toNat_or, BitVec.shiftLeft_eq', hW, BitVec.toNat_shiftLeft]
  have hc : c.toNat * 2 ^ k < 2 ^ 64 := by omega
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hc, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
