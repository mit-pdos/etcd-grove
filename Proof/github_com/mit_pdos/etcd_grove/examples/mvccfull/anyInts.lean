/- Lean-first (no Rocq counterpart). The proof of `anyInts`: a new slice of `n` zeros, each overwritten by `anyInt`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.anyInts
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.anyInt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem anyInts.wp_proof (wp_anyInt : anyInt.spec (GF := GF) (hG := hG)) :
    anyInts.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start
  wp_auto
  wp_apply (wp_slice_make2 (V := w64) n) as %sl ⟨Hsl, -⟩
  · ipureintro; exact hn
  (try wp_auto)
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_replicate] at Hsll
  ihave IH : (∃ (j : w64) (ws : List w64), "i" ∷ i_ptr ↦ j ∗ "Hsl" ∷ sl ↦* ws ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ ws.length = sint.nat n⌝ : IProp GF) $$ [i Hsl]
  · iexists W64 0, _
    iframe
    ipureintro; exact ⟨by decide, List.length_replicate⟩
  wp_for IH
  obtain ⟨Hj0, Hwl⟩ := Hj
  wp_if_destruct
  · wp_apply wp_anyInt as %x _
    (try wp_auto)
    (try simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj0, by word⟩,
      _root_.and_self, ↓reduceIte])
    wp_apply wp_store_slice_index sl (sint.Z j) ws x $$ [Hsl] as Hsl
    · iframe; ipureintro; constructor <;> word
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, _
    iframe
    ipureintro
    exact ⟨by word, by rw [List.length_set]; exact Hwl⟩
  · (try wp_auto)
    iapply HΦ
    iexact Hsl

end proof

end mvccfull
end EtcdGrove
end Perennial
