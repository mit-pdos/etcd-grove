/- Lean-first (no Rocq counterpart).

`cacheKey(model, linearized, state)`: the bitset's hash, xor the model's if it has one.
-/
module

public import Spec.github_com.anishathalye.porcupine.cacheKey
public import Spec.github_com.anishathalye.porcupine.bitset__hash

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem cacheKey.wp_proof (wp_hash : bitset.hash.spec (GF := GF) (hG := hG)) :
    cacheKey.spec (GF := GF) (hG := hG) := fun σ S m lin ws dq st t => by
  wp_start as ⟨#Heh, Hlin, Hst⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_hash $$ [$Hlin] as %h Hlin
  unfold isEqHash
  icases Heh with ⟨-, -, (%Hnil | #Hh)⟩
  · rw [Hnil]
    wp_auto
    wp_end
  · wp_if_destruct
    · wp_end
    · unfold hashSpec
      wp_apply Hh $$ %st %t [$Hst] as %x Hst
      wp_end

end proof

end porcupine
end EtcdGrove
end Perennial
