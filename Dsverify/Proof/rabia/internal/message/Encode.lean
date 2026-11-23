/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Encode.lean`, run `rabia-r1wake-1`.)

`sovMessage` and `encodeVarintMessage` (message.pb.go 698-707, 922-924): the length of a varint
and its back-to-front write (prover C1).
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecPure
public import Dsverify.Proof.rabia.internal.message.Varint
public import Perennial.Proof.math.bits

@[expose] public section

namespace Perennial.rabia.model

/-- `xs` written over `bs` at `i`. -/
def writeAt (bs : List w8) (i : Nat) (xs : List w8) : List w8 :=
  bs.take i ++ xs ++ bs.drop (i + xs.length)

theorem writeAt_length (bs : List w8) (i : Nat) (xs : List w8) (h : i + xs.length ≤ bs.length) :
    (writeAt bs i xs).length = bs.length := by
  simp [writeAt]; omega

theorem writeAt_nil (bs : List w8) (i : Nat) : writeAt bs i [] = bs := by
  simp [writeAt]

theorem writeAt_snoc (bs : List w8) (i : Nat) (xs : List w8) (b : w8)
    (h : i + xs.length < bs.length) :
    (writeAt bs i xs).set (i + xs.length) b = writeAt bs i (xs ++ [b]) := by
  unfold writeAt
  obtain ⟨c, rest, hcr⟩ : ∃ c rest, bs.drop (i + xs.length) = c :: rest := by
    cases hd : bs.drop (i + xs.length) with
    | nil => rw [List.drop_eq_nil_iff] at hd; omega
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hti : (bs.take i).length = i := by simp; omega
  have hrest : bs.drop (i + (xs ++ [b]).length) = rest := by
    have := congrArg List.tail hcr
    simpa [List.tail_drop, Nat.add_assoc] using this
  rw [hcr, hrest]
  rw [List.append_assoc, List.set_append_right _ _ (by simp [hti])]
  simp [hti]

theorem byte_cont (vv : w64) :
    W8 (uint.Z ((vv &&& W64 127) ||| W64 128)) = BitVec.ofNat 8 (vv.toNat % 128 + 128) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : ((vv &&& W64 127) ||| W64 128).toNat = vv.toNat % 128 + 128 := by
    rw [BitVec.toNat_or, BitVec.toNat_and]
    have e1 : (W64 127).toNat = 2 ^ 7 - 1 := rfl
    have e2 : (W64 128).toNat = 2 ^ 7 * 1 := rfl
    rw [e1, Nat.and_two_pow_sub_one_eq_mod, e2, Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (by omega : vv.toNat % 2 ^ 7 < 2 ^ 7)]
    omega
  simp only [uint.Z, h1, BitVec.toNat_ofNat]
  simp; omega

theorem byte_last (vv : w64) (_h : vv.toNat < 128) : W8 (uint.Z vv) = BitVec.ofNat 8 vv.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [uint.Z]

theorem take_succ_of_drop {α} (l : List α) (j : Nat) (x : α) (r : List α)
    (h : l.drop j = x :: r) : l.take (j + 1) = l.take j ++ [x] := by
  rw [List.take_add_one]
  have : l[j]? = some x := by
    have := congrArg List.head? h; simpa [List.head?_drop] using this
  rw [this]; rfl

end Perennial.rabia.model

namespace Perennial.rabia.internal.message
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

/-- `sovMessage(x)`: the length of `x`'s varint. -/
theorem wp_sovMessage (x : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits }}
      (App (Val (@! sovMessage)) (Val #x))
    {{ RET #(W64 (varint x.toNat).length); True }} := by
  wp_start as #Hbits
  wp_auto
  wp_apply math.bits.wp_Len64 as %l %Hl
  obtain ⟨Hl1, Hl2, Hl3⟩ := Hl
  have hor : (x ||| 1).toNat = x.toNat ||| 1 := BitVec.toNat_or ..
  have hk := sov_eq x.toNat l.toNat (by rw [← hor]; exact_mod_cast Hl2)
    (by rcases Hl3 with h | h
        · exfalso
          have : (x ||| 1).toNat = 0 := by
            have h' : (x ||| 1) = 0 := h
            rw [h']; rfl
          rw [hor] at this; have := @Nat.right_le_or x.toNat 1; omega
        · rw [← hor]; exact_mod_cast h)
  have hk10 : (varint x.toNat).length ≤ 10 := varint_length_le _ _ (by have := x.isLt; omega) (by omega)
  have hdiv : BitVec.sdiv (l + W64 6) (W64 7) = W64 ((varint x.toNat).length) := by
    rw [← hk]
    have hl : l.toNat ≤ 64 := by word
    have hpos : (l + W64 6).msb = false := by
      rw [BitVec.msb_eq_false_iff_two_mul_lt]; simp; omega
    rw [BitVec.sdiv_eq, hpos]
    simp only [show (W64 7).msb = false from rfl]
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  rw [hdiv]
  wp_end

/-- `encodeVarintMessage(dAtA, offset, v)`: `v`'s varint written just before `offset`; returns
its start. -/
theorem wp_encodeVarintMessage (sl : GoSlice) (bs : List w8) (off v : w64)
    (h0 : 0 ≤ sint.Z off) (hk : (varint v.toNat).length ≤ sint.nat off)
    (hle : sint.nat off ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ sl ↦* bs }}
      (App (App (App (Val (@! encodeVarintMessage)) (Val #sl)) (Val #off)) (Val #v))
    {{ RET #(off - W64 (varint v.toNat).length);
        sl ↦* writeAt bs (sint.nat off - (varint v.toNat).length) (varint v.toNat) }} := by
  wp_start as Hsl
  wp_auto
  wp_apply wp_sovMessage
  · iexact Hpkg2
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  generalize hN : v.toNat = N at hk ⊢
  generalize hb : sint.nat off - (varint N).length = b
  have hk10 : (varint N).length ≤ 10 := varint_length_le _ _ (by have := v.isLt; omega) (by omega)
  ihave HI : (∃ (j : Nat) (vv offv : w64), "v" ∷ v_ptr ↦ vv ∗ "offset" ∷ offset_ptr ↦ offv ∗
      "Hsl" ∷ sl ↦* writeAt bs b ((varint N).take j) ∗
      "%Hj" ∷ ⌜vv.toNat = N / 2 ^ (7 * j) ∧ sint.nat offv = b + j ∧ 0 ≤ sint.Z offv ∧
        (varint N).drop j = varint (N / 2 ^ (7 * j))⌝ : IProp GF) $$ [v offset Hsl]
  · iexists 0, _, _
    simp only [List.take_zero, writeAt_nil]
    iframe
    ipureintro
    refine ⟨by simp [hN], by word, by word, by simp⟩
  wp_for HI
  obtain ⟨Hj1, Hj2, Hj3, Hj4⟩ := Hj
  have hjk : j < (varint N).length := by
    apply Nat.lt_of_not_le; intro hj
    rw [List.drop_eq_nil_of_le hj] at Hj4
    exact varint_ne_nil _ Hj4.symm
  have hwl : (writeAt bs b ((varint N).take j)).length = bs.length :=
    writeAt_length _ _ _ (by simp; omega)
  wp_if_destruct
  · -- a continuation byte
    have hge : ¬ N / 2 ^ (7 * j) < 128 := by word
    rw [varint_ge _ hge] at Hj4
    rw [if_pos ⟨Hj3, by word⟩]
    rw [byte_cont]
    rw [Hj1]
    wp_apply wp_store_slice_index $$ [Hsl] with Hsl
    · iframe; ipureintro; word
    wp_for_post
    iframe
    iexists j + 1, _, _
    rw [show (sint.Z offv).toNat = b + ((varint N).take j).length by
      rw [List.length_take, Nat.min_eq_left (by omega)]; word]
    rw [writeAt_snoc _ _ _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
      ← take_succ_of_drop _ _ _ _ Hj4]
    iframe
    ipureintro
    refine ⟨?_, by word, by word, ?_⟩
    · rw [div_pow_succ]
      have : (vv >>> W64 7).toNat = vv.toNat / 128 := by
        rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, show (W64 7).toNat = 7 from rfl,
          Nat.shiftRight_eq_div_pow]
      rw [this, Hj1]
    · rw [div_pow_succ, ← List.drop_drop, Hj4]; rfl
  · -- the last byte
    have hlt : N / 2 ^ (7 * j) < 128 := by word
    rw [varint_lt _ hlt] at Hj4
    rw [if_pos ⟨Hj3, by word⟩]
    rw [byte_last _ (by word), Hj1]
    wp_apply wp_store_slice_index $$ [Hsl] with Hsl
    · iframe; ipureintro; word
    have hj1 : j + 1 = (varint N).length := by
      have := congrArg List.length Hj4; simp at this; omega
    rw [show (sint.Z offv).toNat = b + ((varint N).take j).length by
      rw [List.length_take, Nat.min_eq_left (by omega)]; word]
    rw [writeAt_snoc _ _ _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
      ← take_succ_of_drop _ _ _ _ Hj4, hj1, List.take_length]
    wp_auto
    wp_end

end proof
end Perennial.rabia.internal.message
