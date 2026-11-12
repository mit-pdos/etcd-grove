/- Lean-first (no Rocq counterpart).

`b.clone()`: `make` and `copy`.
-/
module

public import Spec.github_com.anishathalye.porcupine.bitset__clone

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

theorem bitset.clone.wp_proof : bitset.clone.spec (GF := GF) (hG := hG) := fun b ws dq => by
  wp_start as Hb
  ihave %Hlen := ownSlice_len $$ Hb
  wp_auto
  wp_apply wp_slice_make2 $$ [] as %sl ⟨Hsl, -⟩
  · ipureintro; word
  wp_apply wp_slice_copy $$ [Hsl Hb] as %k ⟨%Hk, Hsl, Hb⟩
  · iframe
  wp_auto
  iapply HΦ
  rw [List.length_replicate, ← Hlen.1, List.take_length, List.drop_of_length_le (by simp),
    List.append_nil]
  iframe

end proof

end porcupine
end EtcdGrove
end Perennial
