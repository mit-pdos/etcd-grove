/-
The proof of `wire.RandomBytes` (`Net/Spec/.../wire/RandomBytes.lean`): `make([]byte, n)`, then a
loop storing a random byte at each index; the invariant: the slice keeps its length `n`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.RandomBytes
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions]

theorem RandomBytes.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG)) :
    RandomBytes.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start as %Hn
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) n) as %b ⟨Hb, -⟩
  · ipureintro; exact Hn
  (try wp_auto)
  ihave HI : (∃ (k : w64) (bs : List w8),
      "i" ∷ i_ptr ↦ k ∗ "Hb" ∷ b ↦* bs ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z k ∧ bs.length = sint.nat n⌝ : IProp GF) $$ [i Hb]
  · iexists W64 0, List.replicate (sint.nat n) (zero_val w8)
    iframe i Hb
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for HI
  wp_if_destruct
  · -- the body: a random byte at index `k`
    obtain ⟨Hk0, Hbl⟩ := Hinv
    wp_apply wp_RandomUint64 as %r -
    (try wp_auto)
    ihave %Hlen := ownSlice_len $$ Hb
    obtain ⟨Hl1, Hl2⟩ := Hlen
    have hbn : sint.Z b.len = sint.Z n := by
      have h : (sint.Z b.len).toNat = (sint.Z n).toNat := by
        show sint.nat b.len = sint.nat n
        rw [← Hl1, Hbl]
      omega
    have hkb : (sint.Z k : Int) < bs.length := by
      rw [Hbl]; show sint.Z k < ((sint.Z n).toNat : Int); omega
    rw [ite_eq_left (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z b.len by omega)]
    wp_apply wp_store_slice_index b (sint.Z k) _ _ $$ [$Hb] as Hb
    · ipureintro; omega
    (try wp_auto)
    wp_for_post
    iframe
    iexists k + W64 1, _
    iframe i Hb
    ipureintro
    exact ⟨by word, by simp [Hbl]⟩
  · -- the loop ends
    obtain ⟨-, Hbl⟩ := Hinv
    (try wp_auto)
    iapply HΦ
    iexists bs
    iframe Hb
    ipureintro; exact Hbl
