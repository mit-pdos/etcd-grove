/-
Proof of `Spec/k8s_io/client_go/util/workqueue/TypedMaxOfRateLimiter__NumRequeues.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.TypedMaxOfRateLimiter__NumRequeues

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem TypedMaxOfRateLimiter.NumRequeues.wp_proof : TypedMaxOfRateLimiter.NumRequeues.spec (GF := GF) (hG := hG) := by
  intro K T _ r k
  wp_start as #Hr
  iunfold isMaxOfLimiter at Hr
  icases Hr with ⟨%sl, %ls, #Hsl, #Hls, #Hall⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hls
  wp_auto
  ihave IH : iprop(∃ (n : w64) (x : TypedRateLimiter K) (d : w64),
      "i" ∷ i_ptr ↦ n ∗
      "limiter" ∷ limiter_ptr ↦ x ∗
      "ret" ∷ ret_ptr ↦ d ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝) $$ [i limiter ret]
  · iexists W64 0, _, W64 0
    iframe
    ipureintro
    decide
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ls.length := by word
    obtain ⟨e, He⟩ : ∃ e, ls[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn, Hif⟩, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) ls DFrac.discard e Hn $$ [Hls] as -
    · iframe #; ipureintro; exact He
    ihave #He := BigSepL.bigSepL_lookup
      (Φ := fun _ l => iprop(∃ P : time.Duration → Prop, isRateLimiter (K := K) l P)) He $$ Hall
    icases He with ⟨%P, #He⟩
    iunfold isRateLimiter at He
    icases He with ⟨%li, %Hli, -, #HF, #HN⟩
    subst Hli
    wp_auto
    wp_apply HN $$ %k as %c -
    wp_if_destruct
    · wp_for_post
      iframe
      iexists n + W64 1, _, c
      iframe
      ipureintro; word
    · wp_for_post
      iframe
      iexists n + W64 1, _, d
      iframe
      ipureintro; word
  · iapply HΦ; itrivial

end proof

end workqueue
end EtcdGrove
end Perennial
