/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/Registry__MustRegister.lean`: client_golang's
real `(*Registry).MustRegister` (route (b), notes/prom-registry.md, "Step 2") of one collector, over
`(*Registry).Register`'s spec.
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.Registry__MustRegister
public import Spec.github_com.prometheus.client_golang.prometheus.Registry__Register

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open github_com.prometheus.client_golang.prometheus

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]

theorem prometheus.Registry.MustRegister.wp_proof
    (wp_Register : prometheus.Registry.Register.spec (GF := GF) (hG := hG)) :
    prometheus.Registry.MustRegister.spec (GF := GF) (hG := hG) := by
  intro γ r s dq c ps ds
  wp_start as ⟨#Hreg, Hs, #Hdesc, #Hps, Htoks, %Hok⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave IH : (∃ i : w64,
      "Hs" ∷ s ↦*{dq} [GoInterface.ok c] ∗ "i" ∷ i_ptr ↦ i ∗ "c" ∷ (∃ cv : GoInterface, c_ptr ↦ cv) ∗
      "Ht" ∷ (if sint.Z i = 0 then prometheus.idToks γ (prometheus.descKeys ds) else True) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 1⌝ : IProp GF) $$ [Hs i c Htoks]
  · iexists (zero_val w64)
    have h0 : sint.Z (zero_val w64 : w64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    iframe
    isplitl [c]
    · iexists _; iexact c
    ipureintro; decide
  have hs1 : sint.Z s.len = 1 := by
    obtain ⟨h1, h2⟩ := Hlen
    simp only [List.length_cons, List.length_nil] at h1
    word
  wp_for IH
  iNamed c
  wp_if_destruct
  · rename_i Hif
    have hi0 : sint.Z i = 0 := by omega
    rw [if_pos hi0]
    have hy : [GoInterface.ok c][sint.nat i]? = some (GoInterface.ok c) := by
      rw [show sint.nat i = 0 by word]; rfl
    (try wp_auto)
    rw [if_pos ⟨Hi.1, Hif⟩]
    wp_apply wp_load_slice_index s (sint.Z i) [GoInterface.ok c] dq (GoInterface.ok c) Hi.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact hy
    (try wp_auto)
    wp_apply wp_Register $$ [$Hreg $Hdesc $Hps $Ht]
    · ipureintro; exact Hok
    (try wp_auto)
    wp_for_post
    iframe
    iexists (i + W64 1)
    have h1 : sint.Z (i + W64 1) ≠ 0 := by word
    rw [if_neg h1]
    iframe
    isplitl [c]
    · iexists _; iexact c
    ipureintro; word
  · iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
