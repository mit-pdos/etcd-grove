/-
The proof of `Spec/hash/fnv/sum64a__Write.lean`: the translated body.
-/
module

public import Spec.hash.fnv.sum64a__Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.fnv.Assumptions]

omit [GooseExts] in
/-- `sum64a(c)` of a byte is its zero extension. -/
theorem W64_uint_Z_w8 (c : w8) : W64 (uint.Z c) = c.zeroExtend 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [uint.Z, W64]

theorem hash.fnv.sum64a.Write.wp_proof : hash.fnv.sum64a.Write.spec (GF := GF) (hG := hG) := by
  intro l h s bs dq
  wp_start as ⟨Hl, Hs⟩
  wp_auto
  ihave %Hs_len := ownSlice_len _ _ _ $$ Hs
  ihave HI : (∃ (i : w64) (cv : w8),
      "i" ∷ i_ptr ↦ i ∗
      "c" ∷ c_ptr ↦ cv ∗
      "hash" ∷ hash_ptr ↦ hash.fnv.fnv64aFrom h (bs.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i c hash]
  · iexists (W64 0), _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, hash.fnv.fnv64aFrom_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hif' : sint.Z i < sint.Z s.len := by simpa using Hif
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hif'⟩)]
    obtain ⟨x_i, Hx_i⟩ : ∃ x, bs[(sint.Z i).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by simp only [sint.nat, sint.Z] at Hs_len Hi Hif' ⊢; omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ x_i Hi.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx_i
    have hix : sint.nat i < bs.length := by simp only [sint.nat, sint.Z] at Hs_len Hi Hif' ⊢; omega
    have htake : bs.take (sint.nat (i + W64 1)) = bs.take (sint.nat i) ++ [x_i] := by
      have e : sint.nat (i + W64 1) = sint.nat i + 1 := by
        simp only [sint.nat, sint.Z] at Hs_len Hi Hif' ⊢; word
      have hx : bs[sint.nat i]? = some x_i := Hx_i
      rw [e, List.take_add_one, hx]; rfl
    wp_for_post
    iframe
    iexists (i + W64 1), x_i
    rw [htake, hash.fnv.fnv64aFrom_append]
    simp only [hash.fnv.fnv64aFrom, List.foldl, hash.fnv.fnv64aStep, hash.fnv.fnv64aPrime,
      W64_uint_Z_w8]
    iframe
    ipureintro; simp only [sint.nat, sint.Z] at Hs_len Hi Hif' ⊢; word
  · have hie : sint.nat i = bs.length := by
      simp only [sint.nat, sint.Z] at Hs_len Hi Hif ⊢; omega
    rw [hie, List.take_length]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
