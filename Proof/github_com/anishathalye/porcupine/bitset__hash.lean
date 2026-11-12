/- Lean-first (no Rocq counterpart).

`b.hash()`: a loop over the words.
-/
module

public import Spec.github_com.anishathalye.porcupine.bitset__hash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem bitset.hash.wp_proof : bitset.hash.spec (GF := GF) (hG := hG) := fun b ws dq => by
  wp_start as Hb
  ihave %Hlen := ownSlice_len $$ Hb
  wp_auto
  ihave HI : (∃ (i hv x : w64),
      "i" ∷ i_ptr ↦ i ∗ "h" ∷ h_ptr ↦ hv ∗ "v" ∷ v_ptr ↦ x ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b.len⌝ : IProp GF) $$ [i h v]
  · iexists W64 0, _, _
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := ⟨Hi.1, Hif⟩
    simp only [Hb', and_self, ↓reduceIte]
    list_elem ws (sint.nat i) as w
    wp_apply wp_load_slice_index b (sint.Z i) ws dq w Hi.1 $$ [Hb] as Hb
    · iframe; ipureintro; exact Hw_lookup
    wp_for_post
    iframe
    iexists i + W64 1, _, _
    iframe
    ipureintro; word
  · wp_end

end proof

end porcupine
end EtcdGrove
end Perennial
