/- Lean-first (no Rocq counterpart).

# `randomWord`'s proof

`below(33)` bytes (`make`), each set to `'a' + below(26)` by a range loop over the fresh slice (the
invariant: the bytes before the loop's index are lowercase letters), then `string(b)`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.randomWord
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.below

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem randomWord.wp_proof (wp_below : below.spec (GF := GF) (hG := hG)) :
    randomWord.spec (GF := GF) (hG := hG) := by
  wp_start as -
  wp_auto
  wp_apply wp_below (W64 33) as %n0 %Hn0
  have hn0 : uint.Z n0 < 33 := Hn0.2 (by decide)
  wp_apply (wp_slice_make2 (V := w8) n0) as %dsl ⟨Hd, Hcap⟩
  · ipureintro; word
  try wp_auto
  -- the range loop (`slice.forRange`'s own counter `i_ptr`; Go's `i` is `igo`)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave IH : iprop(∃ (k : w64) (j : w64) (bs : List w8),
      "i" ∷ i_ptr ↦ k ∗ "Higo" ∷ igo ↦ j ∗ "Hd" ∷ dsl ↦* bs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ sint.nat n0 ∧ bs.length = sint.nat n0 ∧
        ∀ (m : Nat) (c : w8), m < sint.nat k → bs[m]? = some c →
          97 ≤ c.toNat ∧ c.toNat ≤ 122⌝) $$ [i Higo Hd]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp, fun m c hm _ => ?_⟩
    exfalso
    word
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
    intro m c hm hc
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [hk1] at hm
    rw [show (sint.Z k).toNat = sint.nat k by word] at hc
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
    · rw [List.getElem?_set_ne (by omega)] at hc
      exact Hk.2.2.2 m c hlt hc
    · subst heq
      rw [List.getElem?_set_self (by word)] at hc
      obtain rfl := Option.some.inj hc
      constructor <;> word
  · try wp_auto
    wp_apply (wp_bytes_to_string dsl bs (DFrac.own 1)) $$ Hd as Hd
    try wp_auto
    iapply HΦ
    ipureintro
    refine ⟨by word, fun c hc => ?_⟩
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
    exact Hk.2.2.2 m _ (by word) (List.getElem?_eq_getElem hm)

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
