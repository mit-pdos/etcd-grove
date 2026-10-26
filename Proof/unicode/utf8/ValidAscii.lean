/-
`utf8ValidB` past ASCII bytes, and the mask test of `ValidString`'s ASCII fast path (`word(s) &
hiBits == 0`, `utf8.go`): pure lemmas for `ValidString.lean`.
-/
module

public import Proof.unicode.utf8.Valid

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- An ASCII byte does not change validity. -/
theorem utf8ValidB_cons_ascii (b : w8) (bs : List w8) (hb : b.toNat < 0x80) :
    utf8ValidB (b :: bs) = utf8ValidB bs := by
  conv => lhs; unfold utf8ValidB
  rw [ite_eq_left hb]

/-- ASCII bytes do not change validity. -/
theorem utf8ValidB_ascii_append : ∀ (l r : List w8), (∀ b ∈ l, b.toNat < 0x80) →
    utf8ValidB (l ++ r) = utf8ValidB r
  | [], _, _ => rfl
  | b :: bs, r, h => by
    rw [List.cons_append, utf8ValidB_cons_ascii b _ (h b (List.mem_cons_self ..))]
    exact utf8ValidB_ascii_append bs r (fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- `word(s)` (`utf8.go`, 64-bit): the first eight bytes of `s`, little-endian. -/
def utf8.wordOf (s : List w8) : w64 :=
  W64 (uint.Z (s.getD 0 0)) ||| W64 (uint.Z (s.getD 1 0)) <<< W64 8 |||
    W64 (uint.Z (s.getD 2 0)) <<< W64 16 ||| W64 (uint.Z (s.getD 3 0)) <<< W64 24 |||
    W64 (uint.Z (s.getD 4 0)) <<< W64 32 ||| W64 (uint.Z (s.getD 5 0)) <<< W64 40 |||
    W64 (uint.Z (s.getD 6 0)) <<< W64 48 ||| W64 (uint.Z (s.getD 7 0)) <<< W64 56

theorem utf8.W64_uintZ_w8 (b : w8) : W64 (uint.Z b) = b.setWidth 64 := by
  simp only [W64, uint.Z]
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide : 2 ^ 8 < 2 ^ 64))]

/-- The mask test (`hiBits`, `0x8080808080808080`): every one of the eight bytes is ASCII. -/
theorem utf8.wordOf_mask_ascii (s : List w8) (h : 8 ≤ s.length)
    (hm : utf8.wordOf s &&& W64 9259542123273814144 = W64 0) :
    ∀ b ∈ s.take 8, b.toNat < 0x80 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, r, rfl⟩ :
      ∃ b0 b1 b2 b3 b4 b5 b6 b7 r, s = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r := by
    match s, h with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r, _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  simp only [utf8.wordOf, List.getD_cons_zero, List.getD_cons_succ, utf8.W64_uintZ_w8] at hm
  have hW1 : (W64 9259542123273814144 : w64) = 0x8080808080808080#64 := rfl
  have hW0 : (W64 0 : w64) = 0#64 := rfl
  rw [hW1, hW0] at hm
  -- bit `8 k + 7` of the masked word is byte `k`'s bit 7 (not `bv_decide`, whose proof rests on
  -- native evaluation)
  have h7 : ∀ c : w8, c.getLsbD 7 = false → c.toNat < 0x80 := by
    intro c hc
    have hc' : c.toNat.testBit 7 = false := by simpa [BitVec.getLsbD] using hc
    rw [Nat.testBit_eq_decide_div_mod_eq] at hc'
    have := c.isLt
    simp at hc'
    omega
  have e0 := congrArg (fun x => x.getLsbD 7) hm
  have e1 := congrArg (fun x => x.getLsbD 15) hm
  have e2 := congrArg (fun x => x.getLsbD 23) hm
  have e3 := congrArg (fun x => x.getLsbD 31) hm
  have e4 := congrArg (fun x => x.getLsbD 39) hm
  have e5 := congrArg (fun x => x.getLsbD 47) hm
  have e6 := congrArg (fun x => x.getLsbD 55) hm
  have e7 := congrArg (fun x => x.getLsbD 63) hm
  simp at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> apply h7 <;> assumption

/-- Skipping eight bytes that pass the mask test does not change validity. -/
theorem utf8.validB_drop8 (s : List w8) (h : 8 ≤ s.length)
    (hm : utf8.wordOf s &&& W64 9259542123273814144 = W64 0) :
    utf8ValidB (s.drop 8) = utf8ValidB s := by
  conv => rhs; rw [← List.take_append_drop 8 s]
  exact (utf8ValidB_ascii_append _ _ (utf8.wordOf_mask_ascii s h hm)).symm

theorem utf8.or_mask (a b m : w64) (h : (a ||| b) &&& m = W64 0) :
    a &&& m = W64 0 ∧ b &&& m = W64 0 := by
  have hW0 : (W64 0 : w64) = 0#64 := rfl
  rw [hW0] at h ⊢
  rw [BitVec.and_or_distrib_right] at h
  exact BitVec.or_eq_zero_iff.mp h

end EtcdGrove
end Perennial
