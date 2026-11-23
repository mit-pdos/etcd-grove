/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Varint.lean`, run `rabia-r1wake-1`.)

Pure lemmas about protobuf varints (`model.varint`) for the decoders and encoders of
`message.pb.go` (prover C1).
-/
module

public import Dsverify.Proof.rabia.Core.Model

@[expose] public section

namespace Perennial.rabia.model

theorem varint_lt (n : Nat) (h : n < 128) : varint n = [BitVec.ofNat 8 n] := by
  rw [varint]; simp [h]

theorem varint_ge (n : Nat) (h : ¬ n < 128) :
    varint n = BitVec.ofNat 8 (n % 128 + 128) :: varint (n / 128) := by
  rw [varint]; simp [h]

theorem varint_ne_nil (n : Nat) : varint n ≠ [] := by
  by_cases h : n < 128
  · rw [varint_lt n h]; simp
  · rw [varint_ge n h]; simp

theorem varint_length_pos (n : Nat) : 0 < (varint n).length := by
  have := varint_ne_nil n
  cases h : varint n <;> simp_all

/-- One decoding step: the bits of `n` below `7 * j` or-ed with the next group give the bits
below `7 * j + 7`, in any width. -/
theorem or_shift_step (w n j : Nat) :
    BitVec.ofNat w (n % 2 ^ (7 * j)) |||
      (BitVec.ofNat w ((n / 2 ^ (7 * j)) % 128) <<< (7 * j)) =
    BitVec.ofNat w (n % 2 ^ (7 * j + 7)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h128 : (128 : Nat) = 2 ^ 7 := rfl
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, h128]
  by_cases h1 : i < 7 * j
  · simp [h1, hi]; omega
  · by_cases h2 : i < 7 * j + 7
    · have h3 : i - 7 * j < 7 := by omega
      have h4 : i - 7 * j + 7 * j = i := by omega
      simp [h1, h2, h3, h4, hi]
      omega
    · have h3 : ¬ i - 7 * j < 7 := by omega
      simp [h1, h2, h3, hi]

theorem byte_and127 (b : w8) : (b &&& 127).toNat = b.toNat % 128 := by
  rw [BitVec.toNat_and]
  have : (127 : w8).toNat = 2 ^ 7 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem varint_step (n j p : Nat) (rest ds : List w8)
    (h : ds.drop (p + j) = varint (n / 2 ^ (7 * j)) ++ rest) :
    ∃ b, ds[p + j]? = some b ∧ b &&& 127 = BitVec.ofNat 8 ((n / 2 ^ (7 * j)) % 128) ∧
      (b.toNat < 128 ↔ n / 2 ^ (7 * j) < 128) ∧
      (¬ n / 2 ^ (7 * j) < 128 →
        ds.drop (p + j + 1) = varint (n / 2 ^ (7 * (j + 1))) ++ rest) ∧
      (n / 2 ^ (7 * j) < 128 → ds.drop (p + j + 1) = rest) := by
  have hget : ∀ (b : w8) (t : List w8), ds.drop (p + j) = b :: t →
      ds[p + j]? = some b ∧ ds.drop (p + j + 1) = t := by
    intro b t ht
    constructor
    · have := congrArg List.head? ht
      simpa [List.head?_drop] using this
    · have := congrArg List.tail ht
      simpa [List.tail_drop] using this
  by_cases hlt : n / 2 ^ (7 * j) < 128
  · rw [varint_lt _ hlt] at h
    obtain ⟨h1, h2⟩ := hget _ _ h
    refine ⟨_, h1, ?_, ?_, fun h => absurd hlt h, fun _ => h2⟩
    · rw [Nat.mod_eq_of_lt hlt]; apply BitVec.eq_of_toNat_eq; rw [byte_and127]
      generalize n / 2 ^ (7 * j) = x at hlt ⊢; simp; omega
    · generalize n / 2 ^ (7 * j) = x at hlt ⊢; simp; omega
  · rw [varint_ge _ hlt] at h
    obtain ⟨h1, h2⟩ := hget _ _ h
    refine ⟨_, h1, ?_, ?_, fun _ => ?_, fun h => absurd h hlt⟩
    · apply BitVec.eq_of_toNat_eq; rw [byte_and127]
      generalize n / 2 ^ (7 * j) = x at hlt ⊢; simp; omega
    · generalize n / 2 ^ (7 * j) = x at hlt ⊢; simp; omega
    · rw [h2]; congr 2
      rw [Nat.mul_add, Nat.pow_add, ← Nat.div_div_eq_div_mul]

theorem varint_done (n j : Nat) (h : n / 2 ^ (7 * j) < 128) : n % 2 ^ (7 * j + 7) = n := by
  apply Nat.mod_eq_of_lt
  have : n < 128 * 2 ^ (7 * j) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)] at h; omega
  rw [Nat.pow_add]; simpa [Nat.mul_comm] using this

theorem varint_shift_bound (n j : Nat) (hn : n < 2 ^ 64) (h : j = 0 ∨ 2 ^ (7 * j) ≤ n) :
    7 * j < 64 := by
  rcases h with h | h
  · omega
  · have : 2 ^ (7 * j) < 2 ^ 64 := by omega
    have := (Nat.pow_lt_pow_iff_right (by omega)).mp this
    omega

theorem varint_next_bound (n j : Nat) (h : ¬ n / 2 ^ (7 * j) < 128) : 2 ^ (7 * (j + 1)) ≤ n := by
  have : 128 * 2 ^ (7 * j) ≤ n := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)] at h; omega
  rw [Nat.mul_add, Nat.pow_add]; simpa [Nat.mul_comm] using this

theorem acc_step (w N k : Nat) (b : w8) (sh : w64) (hsh : uint.nat sh = 7 * k)
    (hb : b &&& 127 = BitVec.ofNat 8 ((N / 2 ^ (7 * k)) % 128)) :
    BitVec.ofNat w (N % 2 ^ (7 * k)) ||| (BitVec.ofInt w (uint.Z (b &&& W8 127)) <<< sh) =
    BitVec.ofNat w (N % 2 ^ (7 * (k + 1))) := by
  rw [Nat.mul_succ]
  have h127 : (W8 127) = 127 := rfl
  rw [h127, hb, ← or_shift_step]
  congr 1
  have hlt : (N / 2 ^ (7 * k)) % 128 < 256 := by omega
  have : uint.Z (BitVec.ofNat 8 ((N / 2 ^ (7 * k)) % 128)) = (((N / 2 ^ (7 * k)) % 128 : Nat) : Int) := by
    simp only [uint.Z, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hlt]
  rw [this, BitVec.ofInt_natCast, BitVec.shiftLeft_eq', ← hsh]


/-! ## Lists of segments -/

theorem flatten_take_len_mono {α} (L : List (List α)) {a b : Nat} (h : a ≤ b) :
    (L.take a).flatten.length ≤ (L.take b).flatten.length := by
  induction L generalizing a b with
  | nil => simp
  | cons x L ih =>
    cases a with
    | zero => simp
    | succ a => cases b with
      | zero => omega
      | succ b => simp only [List.take_succ_cons, List.flatten_cons, List.length_append]; have := ih (a := a) (b := b) (by omega); omega

theorem flatten_take_len_le {α} (L : List (List α)) (s : Nat) :
    (L.take s).flatten.length ≤ L.flatten.length := by
  have := flatten_take_len_mono L (a := s) (b := L.length + s) (by omega)
  rw [List.take_of_length_le (Nat.le_add_right _ _)] at this; exact this

theorem next_nonempty {α} (L : List (List α)) (s : Nat)
    (h : (L.take s).flatten.length < L.flatten.length) :
    ∃ j, s ≤ j ∧ j < L.length ∧ (∀ i, s ≤ i → i < j → L[i]? = some []) ∧
      L[j]? ≠ some [] ∧ (L.take j).flatten = (L.take s).flatten := by
  induction L generalizing s with
  | nil => simp at h
  | cons x L ih =>
    cases s with
    | zero =>
      cases x with
      | nil =>
        obtain ⟨j, h1, h2, h3, h4, h5⟩ := ih 0 (by simpa using h)
        refine ⟨j + 1, by omega, by simp; omega, ?_, by simpa using h4, by simpa using h5⟩
        intro i _ hi
        cases i with
        | zero => rfl
        | succ i => simpa using h3 i (by omega) (by omega)
      | cons y ys =>
        exact ⟨0, Nat.le_refl _, by simp, fun i h1 h2 => by omega, by simp, rfl⟩
    | succ s =>
      obtain ⟨j, h1, h2, h3, h4, h5⟩ := ih s (by
        simp only [List.take_succ_cons, List.flatten_cons, List.length_append] at h; omega)
      refine ⟨j + 1, by omega, by simp; omega, ?_, by simpa using h4, by simp [h5]⟩
      intro i hi1 hi2
      cases i with
      | zero => omega
      | succ i => simpa using h3 i (by omega) (by omega)

theorem rest_empty {α} (L : List (List α)) (s : Nat)
    (h : L.flatten.length ≤ (L.take s).flatten.length) :
    ∀ i, s ≤ i → i < L.length → L[i]? = some [] := by
  induction L generalizing s with
  | nil => simp
  | cons x L ih =>
    intro i hi1 hi2
    cases s with
    | zero =>
      cases i with
      | zero =>
        cases x with
        | nil => rfl
        | cons y ys => simp at h
      | succ i =>
        simp at h
        have hx : x = [] := by cases x <;> simp_all
        subst hx
        simpa using ih 0 (by simpa using h) i (by omega) (by simp at hi2; omega)
    | succ s =>
      cases i with
      | zero => omega
      | succ i =>
        simpa using ih s (by
          simp only [List.take_succ_cons, List.flatten_cons, List.length_append] at h; omega)
          i (by omega) (by simp at hi2; omega)

theorem flatten_drop_take {α} (L : List (List α)) (j : Nat) (hj : j < L.length) :
    L.flatten.drop (L.take j).flatten.length = L[j] ++ (L.drop (j + 1)).flatten := by
  have e := List.take_append_drop j L
  conv => lhs; arg 2; rw [← e]
  rw [List.flatten_append, List.drop_left, List.drop_eq_getElem_cons hj, List.flatten_cons]

theorem varint_step1 (x p : Nat) (R ds : List w8) (h : ds.drop p = varint x ++ R) :
    ∃ b, ds[p]? = some b ∧ b &&& 127 = BitVec.ofNat 8 (x % 128) ∧
      (b.toNat < 128 ↔ x < 128) ∧
      (¬ x < 128 → ds.drop (p + 1) = varint (x / 128) ++ R) ∧
      (x < 128 → ds.drop (p + 1) = R) := by
  have := varint_step x 0 p R ds (by simpa using h)
  simpa using this

theorem div_pow_succ (N k : Nat) : N / 2 ^ (7 * (k + 1)) = N / 2 ^ (7 * k) / 128 := by
  rw [Nat.mul_add, Nat.pow_add, ← Nat.div_div_eq_div_mul]

theorem next_seg {α} (L : List (List α)) (s : Nat) (h : (L.drop s).flatten ≠ []) :
    ∃ j seg, s ≤ j ∧ j < L.length ∧ (∀ i, s ≤ i → i < j → L[i]? = some []) ∧
      L[j]? = some seg ∧ seg ≠ [] ∧ (L.drop s).flatten = seg ++ (L.drop (j + 1)).flatten := by
  induction L generalizing s with
  | nil => simp at h
  | cons x L ih =>
    cases s with
    | zero =>
      cases x with
      | nil =>
        obtain ⟨j, seg, h1, h2, h3, h4, h5, h6⟩ := ih 0 (by simpa using h)
        refine ⟨j + 1, seg, by omega, by simp; omega, ?_, by simpa using h4, h5, by simpa using h6⟩
        intro i _ hi
        cases i with
        | zero => rfl
        | succ i => simpa using h3 i (by omega) (by omega)
      | cons y ys =>
        exact ⟨0, y :: ys, Nat.le_refl _, by simp, fun i h1 h2 => by omega, rfl, by simp, by simp⟩
    | succ s =>
      obtain ⟨j, seg, h1, h2, h3, h4, h5, h6⟩ := ih s (by simpa using h)
      refine ⟨j + 1, seg, by omega, by simp; omega, ?_, by simpa using h4, h5, by simpa using h6⟩
      intro i hi1 hi2
      cases i with
      | zero => omega
      | succ i => simpa using h3 i (by omega) (by omega)

theorem rest_nil {α} (L : List (List α)) (s : Nat) (h : (L.drop s).flatten = []) :
    ∀ i, s ≤ i → i < L.length → L[i]? = some [] := by
  intro i h1 h2
  have : L[i] ∈ L.drop s := by
    rw [List.mem_iff_getElem]; exact ⟨i - s, by simp; omega, by simp; congr 1; omega⟩
  rw [List.flatten_eq_nil_iff] at h
  rw [List.getElem?_eq_getElem h2, h _ this]

/-! ## Varint lengths (`sovMessage`) -/

theorem varint_len_bound (n : Nat) : n < 2 ^ (7 * (varint n).length) ∧
    ((varint n).length = 1 ∨ 2 ^ (7 * ((varint n).length - 1)) ≤ n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 128
    · rw [varint_lt n h]; simp only [List.length_cons, List.length_nil]
      exact ⟨by simpa using h, by simp⟩
    · rw [varint_ge n h]
      obtain ⟨h1, h2⟩ := ih (n / 128) (by omega)
      simp only [List.length_cons]
      generalize (varint (n / 128)).length = k at h1 h2
      have hp : 2 ^ (7 * (k + 1)) = 128 * 2 ^ (7 * k) := by
        rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
      constructor
      · rw [hp]; omega
      · right
        rw [show k + 1 - 1 = k by omega]
        rcases h2 with h2 | h2
        · subst h2; simpa using (by omega : 128 ≤ n)
        · have hp' : 2 ^ (7 * k) = 128 * 2 ^ (7 * (k - 1)) := by
            rw [show 7 * k = 7 + 7 * (k - 1) by
              have : 1 ≤ k := by
                rcases Nat.eq_zero_or_pos k with hk | hk
                · subst hk; simp at h1; omega
                · exact hk
              omega, Nat.pow_add]
          rw [hp']; omega

theorem varint_length_le (n e : Nat) (h : n < 2 ^ (7 * e)) (he : 1 ≤ e) :
    (varint n).length ≤ e := by
  obtain ⟨_, h2⟩ := varint_len_bound n
  rcases h2 with h2 | h2
  · omega
  · have : 2 ^ (7 * ((varint n).length - 1)) < 2 ^ (7 * e) := by omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
    omega

theorem sov_eq (n l : Nat) (h1 : n ||| 1 < 2 ^ l) (h2 : 2 ^ l ≤ 2 * (n ||| 1)) :
    (l + 6) / 7 = (varint n).length := by
  obtain ⟨b1, b2⟩ := varint_len_bound n
  have hk := varint_length_pos n
  generalize (varint n).length = k at b1 b2 hk ⊢
  have hn1 : n ≤ n ||| 1 := Nat.left_le_or
  have hone : 1 ≤ n ||| 1 := Nat.right_le_or
  have hor : n ||| 1 < 2 ^ (7 * k) := Nat.or_lt_two_pow b1
    (by calc 1 = 2 ^ 0 := rfl
          _ < 2 ^ (7 * k) := Nat.pow_lt_pow_right (by decide) (by omega))
  -- l ≤ 7k
  have hl1 : l ≤ 7 * k := by
    have : 2 ^ l < 2 ^ (7 * k + 1) := by rw [Nat.pow_succ]; omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
    omega
  -- 7(k-1) < l
  have hl2 : 7 * (k - 1) < l := by
    rcases b2 with b2 | b2
    · subst b2
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl; simp at h1
      · omega
    · have : 2 ^ (7 * (k - 1)) < 2 ^ l := by omega
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
  omega

end Perennial.rabia.model

