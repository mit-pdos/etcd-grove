module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.rvBytes


@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

private theorem w8_shr (n s : w64) :
    W8 (uint.Z (n >>> s)) = n.extractLsb' (uint.nat s) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [W8, uint.Z, uint.nat, BitVec.extractLsb', BitVec.toNat_ushiftRight]
  simp only [Int.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  rw [← Int.natCast_ediv]
  generalize BitVec.toNat n / 2 ^ BitVec.toNat s = a
  omega

private theorem rvBytes_get (n : w64) (j : Nat) (hj : j < 8) :
    (rvBytes n)[j]? = some (n.extractLsb' (56 - 8 * j) 8) := by
  obtain h|h|h|h|h|h|h|h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
    omega
  all_goals subst h; rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem rvBytes.wp_proof :
    rvBytes.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  (try wp_auto)
  ihave HI : (∃ (j : w64) (bs : List w8), "i" ∷ i_ptr ↦ j ∗ "Hsl" ∷ sl ↦* bs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 8 ∧ bs.length = 8 ∧
        ∀ k, k < sint.nat j → bs[k]? = (rvBytes n)[k]?⌝) $$ [i Hsl]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp, fun k hk => ?_⟩
    exact absurd hk (by word)
  wp_for HI
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨Hj0, Hj8, Hbl, Hbs⟩ := Hj
  wp_if_destruct
  · have hj8 : sint.nat j < 8 := by word
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len by
      refine ⟨Hj0, ?_⟩; have := Hlen.1; rw [Hbl] at this; word)]
    wp_apply wp_store_slice_index sl (sint.Z j) bs _ $$ [Hsl] as Hsl
    · iframe; ipureintro; constructor <;> word
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hbl], fun k hk => ?_⟩
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    rw [hj1] at hk
    rw [List.getElem?_set, show (sint.Z j).toNat = sint.nat j by word]
    by_cases hkj : sint.nat j = k
    · subst hkj
      rw [if_pos rfl, if_pos (by omega), rvBytes_get n _ hj8, w8_shr]
      congr 2
      word
    · rw [if_neg hkj]
      exact Hbs k (by omega)
  · have hj8 : sint.nat j = 8 := by word
    have hb : bs = rvBytes n := by
      apply List.ext_getElem?
      intro k
      by_cases hk : k < 8
      · exact Hbs k (by omega)
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [rvBytes]; omega)]
    subst hb
    wp_apply wp_bytes_to_string $$ [$Hsl] as Hsl
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
