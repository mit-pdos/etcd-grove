/-
**Varints are prefix-free** (pure; W4c U4 of `notes/wal-fsext-w4c-plan.md`): the minimal varint
encoding `varintEnc` (`Proof/google_golang_org/protobuf/proto/UfWire.lean`) determines its value from
any byte list it starts, and a value below `128 ^ k` takes at most `k` bytes. The raftpb instance's
decoders (`RaftModel/Snap.lean`, `RaftModel/Hs.lean`) read their canonical encodings back with it.
Lean-first.
-/
module

public import Proof.google_golang_org.protobuf.proto.UfWire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section varint

private theorem w8_toNat_ofNat (n : Nat) (h : n < 256) : (W8 (n : Int)).toNat = n := by
  simp only [BitVec.toNat_ofInt]; omega

/-- A minimal varint's first byte: its value below 128, else the low 7 bits plus 128. -/
private theorem varintEnc_eq (n : Nat) :
    varintEnc n = if n < 128 then [W8 (n : Int)] else W8 ((n % 128 + 128 : Nat) : Int) :: varintEnc (n / 128) := by
  rw [varintEnc]
  split
  · simp [*]
  · congr 2

/-- **Varints are prefix-free**: a byte list starting with two minimal varints starts with the same
one, and the rests agree. -/
theorem varintEnc_append_inj : ∀ (a b : Nat) (r r' : List w8),
    varintEnc a ++ r = varintEnc b ++ r' → a = b ∧ r = r' := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b r r' h
    rw [varintEnc_eq a, varintEnc_eq b] at h
    by_cases ha : a < 128 <;> by_cases hb : b < 128 <;> simp only [ha, hb, ite_true, ite_false,
      List.cons_append, List.nil_append, List.cons.injEq] at h
    · obtain ⟨h1, h2⟩ := h
      have := congrArg BitVec.toNat h1
      rw [w8_toNat_ofNat a (by omega), w8_toNat_ofNat b (by omega)] at this
      exact ⟨this, h2⟩
    · obtain ⟨h1, -⟩ := h
      have := congrArg BitVec.toNat h1
      rw [w8_toNat_ofNat a (by omega), w8_toNat_ofNat _ (by omega)] at this
      omega
    · obtain ⟨h1, -⟩ := h
      have := congrArg BitVec.toNat h1
      rw [w8_toNat_ofNat b (by omega), w8_toNat_ofNat _ (by omega)] at this
      omega
    · obtain ⟨h1, h2⟩ := h
      have := congrArg BitVec.toNat h1
      rw [w8_toNat_ofNat _ (by omega), w8_toNat_ofNat _ (by omega)] at this
      obtain ⟨h3, h4⟩ := ih (a / 128) (by omega) (b / 128) r r' h2
      exact ⟨by omega, h4⟩

/-- A minimal varint is injective. -/
theorem varintEnc_inj {a b : Nat} (h : varintEnc a = varintEnc b) : a = b :=
  (varintEnc_append_inj a b [] [] (by simp [h])).1

/-- **A value below `128 ^ k` takes at most `k` bytes** (`k ≥ 1`). -/
theorem varintEnc_length_le : ∀ (k n : Nat), 1 ≤ k → n < 128 ^ k → (varintEnc n).length ≤ k := by
  intro k
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n _ hn
    rw [varintEnc_eq n]
    by_cases h : n < 128
    · simp [h]
    · simp only [h, ite_false, List.length_cons]
      have hk : 1 ≤ k := by
        rcases k with _ | k
        · simp at hn; omega
        · omega
      have := ih (n / 128) hk (by rw [Nat.pow_succ] at hn; omega)
      omega

/-- A 64-bit value's varint takes at most 10 bytes. -/
theorem varintEnc_length_w64 (n : Nat) (h : n < 2 ^ 64) : (varintEnc n).length ≤ 10 :=
  varintEnc_length_le 10 n (by omega) (by
    have : (2 : Nat) ^ 64 < 128 ^ 10 := by decide
    omega)

end varint

end EtcdGrove
end Perennial
