/- Lean-first (no Rocq counterpart).

`(*chains).isComplete()`: the loop over the clients (`clients_facts`).
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__isComplete
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.FrontierLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem chains.isComplete.wp_proof : chains.isComplete.spec (GF := GF) (hG := hG) :=
    fun ch h cs st hshape hheads => by
  wp_start as Hch
  unfold chainsOwn chainsRepr
  icases Hch with ⟨%chV, Hch, %cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  icases clients_facts h cs st cvs $$ Hcls with ⟨Hcls, %Hfacts⟩
  ihave %Hlen := ownSlice_len $$ Hcl
  wp_auto
  ihave HI : (∃ (i : w64) (cv : client),
      "i" ∷ i_ptr ↦ i ∗ "c" ∷ c_ptr ↦ cv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z chV.clients'.len ∧
        ∀ c', c' < sint.nat i → st.head c' = (chain cs c').length⌝ : IProp GF) $$ [i c]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, fun c' hc' => ?_⟩
    exact absurd hc' (by word)
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z chV.clients'.len := ⟨Hi.1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem cvs (sint.nat i) as cv'
    wp_apply wp_load_slice_index chV.clients' (sint.Z i) cvs _ cv' Hi.1 $$ [Hcl] as Hcl
    · iframe; ipureintro; exact Hcv'_lookup
    obtain ⟨-, Hhd, Hln, Hln0⟩ := Hfacts _ _ Hcv'_lookup
    wp_if_destruct
    · wp_for_post
      iframe
      iexists i + W64 1, cv'
      iframe
      ipureintro
      refine ⟨by word, by word, fun c' hc' => ?_⟩
      rcases Nat.lt_or_ge c' (sint.nat i) with h1 | h1
      · exact Hi.2.2 c' h1
      · have : c' = sint.nat i := by word
        subst this
        word
    · have hdec : decide (∀ c, c < cs.length → st.head c = (chain cs c).length) = false := by
        rw [decide_eq_false]
        intro hall
        apply Hif
        have := hall (sint.nat i) (by rw [← Hcvs.1, Hlen.1]; word)
        word
      rw [hdec]
      wp_for_post
      iapply HΦ
      iexists chV; iframe Hch; iexists cvs; iframe; ipureintro; exact Hcvs
  · have hdec : decide (∀ c, c < cs.length → st.head c = (chain cs c).length) = true := by
      rw [decide_eq_true]
      intro c' hc'
      exact Hi.2.2 c' (by rw [← Hcvs.1, Hlen.1] at hc'; word)
    rw [hdec]
    simp
    iapply HΦ
    iexists chV; iframe Hch; iexists cvs; iframe; ipureintro; exact Hcvs

end proof

end porcupine
end EtcdGrove
end Perennial
