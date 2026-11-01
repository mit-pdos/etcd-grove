/-
Lean-first (no Rocq counterpart).

The proof of `hashString`: a loop over the string's bytes, whose result nothing is claimed of.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.hashString

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem hashString.wp_proof : hashString.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  ihave HI : (∃ (i hv : w64),
      "i" ∷ i_ptr ↦ i ∗ "h" ∷ h_ptr ↦ hv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i h]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z (W64 ↑(List.length s)) := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt' : sint.nat i < s.length := by word
    obtain ⟨c, Hc⟩ : ∃ c, s[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    simp only [Hi, ↓reduceIte, Hc]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, _
    iframe
    ipureintro; word
  · have Hlt : decide (sint.Z i < sint.Z (W64 ↑(List.length s))) = false := by
      cases h : decide (sint.Z i < sint.Z (W64 ↑(List.length s)))
      · rfl
      · rw [h] at Hif; exact absurd rfl Hif
    rw [Hlt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    ipureintro; trivial

end proof

end kvreconf
end EtcdGrove
end Perennial
