/- Lean-first (no Rocq counterpart).

# `randomWord`'s proof

`below(17)` letters (a range loop over the fresh slice, each byte `'a' + below(26)`), as a string.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.randomWord
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem randomWord.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    randomWord.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_auto
  wp_apply wp_below (W64 17) as %n0 %Hn0
  have hn0 : uint.Z n0 < 17 := Hn0.2 (by decide)
  wp_apply (wp_slice_make2 (V := w8) n0) as %dsl ⟨Hd, Hcap⟩
  · ipureintro; word
  try wp_auto
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave IH : iprop(∃ (k : w64) (j : w64) (bs : List w8),
      "i" ∷ i_ptr ↦ k ∗ "Higo" ∷ igo ↦ j ∗ "Hd" ∷ dsl ↦* bs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ sint.nat n0 ∧ bs.length = sint.nat n0 ∧
        ∀ (i : Nat) (b : w8), i < sint.nat k → bs[i]? = some b → isLetter b⌝) $$ [i Higo Hd]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp, fun i b hi => by word⟩
  wp_for IH
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hd
  wp_if_destruct
  · have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z dsl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, bs[sint.nat k]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    wp_apply wp_load_slice_index dsl (sint.Z k) _ (DFrac.own 1) e Hk.1 $$ [Hd] as Hd
    · iframe; ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact He
    try wp_auto
    wp_apply wp_below (W64 26) as %r %Hr
    have hr : uint.Z r < 26 := Hr.2 (by decide)
    try wp_auto
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_store_slice_index dsl (sint.Z k) bs _ $$ [Hd] as Hd
    · iframe; ipureintro; word
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hk.2.2.1], ?_⟩
    intro i b hi hb
    rw [List.getElem?_set] at hb
    by_cases h1 : (sint.Z k).toNat = i
    · rw [if_pos h1] at hb
      by_cases h2 : (sint.Z k).toNat < bs.length
      · rw [if_pos h2] at hb
        obtain rfl := Option.some.inj hb
        unfold isLetter
        constructor <;> word
      · rw [if_neg h2] at hb; cases hb
    · rw [if_neg h1] at hb
      exact Hk.2.2.2 i b (by word) hb
  · try wp_auto
    wp_apply wp_bytes_to_string $$ Hd as Hd
    try wp_auto
    iapply HΦ
    ipureintro
    have hk : sint.nat k = sint.nat n0 := by word
    refine ⟨by word, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    exact Hk.2.2.2 i _ (by word) (List.getElem?_eq_getElem hi)

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
