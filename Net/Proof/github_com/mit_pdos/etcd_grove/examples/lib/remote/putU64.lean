/-
The proof of `putU64` (`Net/Spec/.../lib/remote/putU64.lean`): the loop over `i < 8` stores
`byte(x >> (8*i))`, `u64Le x`'s byte `i` (`u64Le_getElem`, from Perennial's `u64Le_8`); the
invariant: `b` holds `u64Le x`'s first `i` bytes, then `vs` from `i` on.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.putU64
public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

open encoding.binary in
/-- `u64Le x`'s byte `i` is `byte(x >> (8*i))`. -/
theorem u64Le_getElem (x i : w64) (hi : uint.nat i < 8) :
    (u64Le x)[uint.nat i]? = some (W8 (uint.Z (x >>> (W64 8 * i)))) := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 8 ∧ i = W64 n := ⟨uint.nat i, hi, by word⟩
  have hn' : uint.nat (W64 n : w64) = n := by word
  rw [hn', u64Le_8]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals first | rfl | omega

/-- Storing the next byte of `l1` over `l2`. -/
theorem take_drop_set {l1 l2 : List w8} {n : Nat} {a : w8} (h1 : l1[n]? = some a)
    (h2 : n < l2.length) :
    (l1.take n ++ l2.drop n).set n a = l1.take (n + 1) ++ l2.drop (n + 1) := by
  have hn : n < l1.length := by
    rcases Nat.lt_or_ge n l1.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at h1; cases h1
  have ht : (l1.take n).length = n := by simp; omega
  rw [List.set_append, ite_eq_right (by omega), ht, Nat.sub_self, List.take_add_one, h1]
  rw [List.drop_eq_getElem_cons h2, List.set_cons_zero]
  simp

theorem putU64.wp_proof : putU64.spec (GF := GF) (hG := hG) := by
  intro b vs x Hvs
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "Hb" ∷ b ↦* ((u64Le x).take (uint.nat i) ++ vs.drop (uint.nat i)) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i Hb]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hi8 : uint.nat i < 8 := by word
    have hs : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := by word
    rw [ite_eq_left hs]
    wp_apply wp_store_slice_index b (sint.Z i) _ (W8 (uint.Z (x >>> (W64 8 * i)))) $$ [Hb] as Hb
    · iframe Hb; ipureintro; simp only [List.length_append, List.length_take, List.length_drop,
        u64Le_length]; word
    wp_for_post
    iframe
    iexists i + W64 1
    have hsn : (sint.Z i).toNat = uint.nat i := by word
    rw [hsn, take_drop_set (u64Le_getElem x i hi8) (by word),
      show uint.nat (i + W64 1) = uint.nat i + 1 by word]
    iframe
    ipureintro; word
  · have hi8 : uint.nat i = 8 := by word
    rw [hi8, List.take_of_length_le (by simp [u64Le_length])]
    wp_end

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
