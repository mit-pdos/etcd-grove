/- Lean-first (no Rocq counterpart).

# `randomArgs`'s proof

A payload of `below(65)` random bytes (a range loop over the fresh slice), a message from
`failMsgs` or none, a fresh id (`take`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.randomArgs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.below
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.counter__take
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

theorem randomArgs.wp_proof (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_take : counter.take.spec (GF := GF) (hG := hG))
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    randomArgs.spec (GF := GF) (hG := hG) := by
  intro γid γb c
  wp_start as ⟨#Hf, #Hc, Hcred⟩
  ihave #Hf' := Hf
  iunfold drvFacts at Hf'
  icases Hf' with ⟨⟨%fsl, #Hfg, #Hfsl⟩, -⟩
  ihave %Hflen := ownSlice_len _ _ _ $$ Hfsl
  wp_auto
  wp_apply wp_below (W64 65) as %n0 %Hn0
  have hn0 : uint.Z n0 < 65 := Hn0.2 (by decide)
  wp_apply (wp_slice_make2 (V := w8) n0) as %dsl ⟨Hd, Hcap⟩
  · ipureintro; word
  try wp_auto
  -- the range loop: each byte random (`slice.forRange`'s own counter `i_ptr`; Go's `i` is `igo`)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave IH : iprop(∃ (k : w64) (j : w64) (bs : List w8),
      "i" ∷ i_ptr ↦ k ∗ "Higo" ∷ igo ↦ j ∗ "Hd" ∷ dsl ↦* bs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ sint.nat n0 ∧ bs.length = sint.nat n0⌝) $$ [i Higo Hd]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp⟩
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
    wp_apply wp_RandomUint64 as %x -
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
    refine ⟨by word, by word, by simp [Hk.2.2]⟩
  · try wp_auto
    -- `fail`: none, or one of `failMsgs`
    wp_apply wp_below (W64 2) as %b %Hb
    have hfl : sint.nat fsl.len = 3 := by rw [← Hflen.1]; rfl
    have hfl' : fsl.len = W64 3 := by word
    wp_if_destruct
    · try wp_auto
      rw [hfl']
      wp_apply wp_below (W64 3) as %m %Hm
      have hm : uint.Z m < 3 := Hm.2 (by decide)
      obtain ⟨s, Hs⟩ : ∃ s, failList[sint.nat m]? = some s :=
        ⟨_, List.getElem?_eq_getElem (by simp [failList]; word)⟩
      try wp_auto
      have Hbnd : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z fsl.len := ⟨by word, by rw [hfl']; word⟩
      simp only [Hbnd, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index fsl (sint.Z m) failList DFrac.discard s (by word) $$ [] as -
      · iframe Hfsl; ipureintro; rw [show (sint.Z m).toNat = sint.nat m by word]; exact Hs
      try wp_auto
      wp_apply wp_take γid γb c $$ [$Hc $Hcred] as %idv Htok
      try wp_auto
      iapply HΦ
      iexists idv, dsl, bs, s
      iframe
      ipureintro
      refine ⟨by word, Or.inr (List.mem_of_getElem? Hs)⟩
    · try wp_auto
      wp_apply wp_take γid γb c $$ [$Hc $Hcred] as %idv Htok
      try wp_auto
      iapply HΦ
      iexists idv, dsl, bs, []
      iframe
      ipureintro
      refine ⟨by word, Or.inl rfl⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
