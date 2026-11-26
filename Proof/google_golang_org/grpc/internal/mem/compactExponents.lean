/-
Proof of `Spec/google_golang_org/grpc/internal/mem/compactExponents.lean` (grpc-mem, 2026-11-26).
-/
module

public import Spec.google_golang_org.grpc.internal.mem.compactExponents

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.mem.Assumptions]

theorem grpc.internal.mem.compactExponents.wp_proof :
    grpc.internal.mem.compactExponents.spec (GF := GF) (hG := hG) := by
  intro s xs
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · -- `len(s) < 2`: `s` itself
    wp_auto
    iapply HΦ
    iframe Hs
    ipureintro; intro y hy; exact hy
  -- the first loop: `vs[:k]` holds elements of `xs`, `vs[i:]` is `xs[i:]`
  ihave IH : iprop(∃ (i k : w64) (vs : List w8), "i" ∷ i_ptr ↦ i ∗ "k" ∷ k_ptr ↦ k ∗
      "s" ∷ s_ptr ↦ s ∗ "Hs" ∷ s ↦* vs ∗
      "%Hinv" ∷ ⌜vs.length = xs.length ∧ 1 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z i ∧
        sint.Z i ≤ xs.length ∧ (∀ j y, j < sint.nat k → vs[j]? = some y → y ∈ xs) ∧
        (∀ j, sint.nat i ≤ j → vs[j]? = xs[j]?)⌝) $$ [i k s Hs]
  · iexists (W64 1), (W64 1), xs
    iframe
    ipureintro
    refine ⟨rfl, by word, by word, by word, ?_, fun j _ => rfl⟩
    intro j y _ hy; exact List.mem_of_getElem? hy
  wp_for IH
  sorry

end proof

end EtcdGrove
end Perennial
