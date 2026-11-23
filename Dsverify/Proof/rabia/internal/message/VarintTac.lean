/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/VarintTac.lean`, run `rabia-r1wake-1`.)

`varint_loop`: the proof of one of `message.pb.go`'s inline varint-decoding loops
(`for shift := uint(0); ; shift += 7 { ...; b := dAtA[iNdEx]; iNdEx++; acc |= T(b&0x7F) << shift;
if b < 0x80 { break } }`), prover C1.

`varint_loop H acc N R ds as idx'` expects, in the context: the cells `shift_ptr` (Iris `shift`, holding
`W64 0`), `iNdEx_ptr` (Iris `iNdEx`, holding some `idx`), the slice `sl` (Iris `Hsl : sl ↦*{dq} ds`),
the accumulator's points-to `H : acc (N % 2 ^ 0)` (up to `simp`), and the Lean facts
`Hpre0 : 0 ≤ sint.Z idx`, `Hpre : ds.drop (sint.nat idx) = varint N ++ R`, `HNlt : N < 2 ^ 64`.
It leaves the code after the loop (as far as `wp_auto` goes) with `H : acc N` (unless `wp_auto` used it up) (as `BitVec.ofNat w N`), `iNdEx ↦ idx'` and
`Hpost0 : 0 ≤ sint.Z idx'`, `Hpostle : sint.nat idx' ≤ ds.length`, `Hpost : ds.drop (sint.nat idx') = R`.
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecPure
public import Dsverify.Proof.rabia.internal.message.Varint

@[expose] public section

namespace Perennial.rabia.internal.message
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model

set_option hygiene false in
macro "varint_loop " ACC:ident acc:term:max N:term:max R:term:max ds:term:max " as " out:ident : tactic => `(tactic| (
  ihave HV : (∃ (vk : Nat) (vsh vidx : w64), "shift" ∷ shift_ptr ↦ vsh ∗ "iNdEx" ∷ iNdEx_ptr ↦ vidx ∗
     "ACC" ∷ $acc ($N % 2 ^ (7 * vk)) ∗
     "%Hvk" ∷ ⌜uint.nat vsh = 7 * vk ∧ 0 ≤ sint.Z vidx ∧
        ($ds).drop (sint.nat vidx) = varint ($N / 2 ^ (7 * vk)) ++ $R ∧
        (vk = 0 ∨ 2 ^ (7 * vk) ≤ $N)⌝ : IProp GF) $$ [shift iNdEx $ACC:ident]
  · iexists 0, _, _
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.div_one]
    iframe
    ipureintro
    refine ⟨rfl, Hpre0, ?_, by simp⟩; simpa using Hpre
  wp_for HV
  obtain ⟨Hvsh, Hvidx0, Hvk, Hvkb⟩ := Hvk
  have Hvshb := varint_shift_bound _ _ HNlt Hvkb
  obtain ⟨vb, Hvb, Hvband, Hvblt, Hvcont, Hvstop⟩ := varint_step1 _ _ _ _ Hvk
  have Hvin : sint.nat vidx < ($ds).length := (List.getElem?_eq_some_iff.mp Hvb).1
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  rw [if_pos ⟨Hvidx0, by word⟩]
  wp_apply wp_load_slice_index sl (sint.Z vidx) $ds dq vb Hvidx0 $$ [Hsl] with Hsl
  · iframe; ipureintro; rw [show (sint.Z vidx).toNat = sint.nat vidx by word]; exact Hvb
  rw [acc_step _ _ _ _ _ Hvsh Hvband]
  wp_if_destruct
  rotate_left
  · wp_for_post
    iframe
    have Hvlt : ¬ $N / 2 ^ (7 * vk) < 128 := fun h => Hif (by have := Hvblt.mpr h; word)
    iexists vk + 1, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, Or.inr (varint_next_bound _ _ Hvlt)⟩
    rw [show sint.nat (vidx + W64 1) = sint.nat vidx + 1 by word, div_pow_succ]
    exact Hvcont Hvlt
  have Hvlt : $N / 2 ^ (7 * vk) < 128 := Hvblt.mp (by word)
  rw [show 7 * (vk + 1) = 7 * vk + 7 by omega, varint_done _ _ Hvlt]
  wp_for_post
  have Hpost : ($ds).drop (sint.nat (vidx + W64 1)) = $R := by
    rw [show sint.nat (vidx + W64 1) = sint.nat vidx + 1 by word]; exact Hvstop Hvlt
  have Hpost0 : 0 ≤ sint.Z (vidx + W64 1) := by word
  have Hpostle : sint.nat (vidx + W64 1) ≤ ($ds).length := by word
  try irename ACC => $ACC:ident
  clear Hvsh Hvidx0 Hvk Hvkb Hvshb Hvband Hvblt Hvcont Hvstop Hvb Hvlt Hif Hvin
  generalize vidx + W64 1 = $out:ident at Hpost Hpost0 Hpostle ⊢
  try clear Hif
  try clear Hif))

end Perennial.rabia.internal.message
