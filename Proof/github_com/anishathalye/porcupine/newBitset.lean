/- Lean-first (no Rocq counterpart).

`newBitset(bits)`: `make([]uint64, bits/64 + extra)`.
-/
module

public import Spec.github_com.anishathalye.porcupine.newBitset

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

theorem newBitset.wp_proof : newBitset.spec (GF := GF) (hG := hG) := fun bits => by
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_slice_make2 $$ [] as %sl ⟨Hsl, -⟩
    · ipureintro; word
    iapply HΦ
    rw [show sint.nat (bits / W64 64 + W64 0) = bsChunks (uint.nat bits) by
      unfold bsChunks; split <;> word,
      show zero_val w64 = W64 0 from rfl]
    iexact Hsl
  · wp_apply wp_slice_make2 $$ [] as %sl ⟨Hsl, -⟩
    · ipureintro; word
    iapply HΦ
    rw [show sint.nat (bits / W64 64 + W64 1) = bsChunks (uint.nat bits) by
      unfold bsChunks; split <;> word,
      show zero_val w64 = W64 0 from rfl]
    iexact Hsl

end proof

end porcupine
end EtcdGrove
end Perennial
