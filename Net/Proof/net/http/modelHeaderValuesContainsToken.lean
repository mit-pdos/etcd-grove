/-
The proof of `modelHeaderValuesContainsToken` (`Net/Spec/net/http/modelHeaderValuesContainsToken.lean`):
the range loop over the values, each read through the slice's points-to; on no values the loop does not
run and the answer is `false`.
-/
module

public import Net.Spec.net.http.modelHeaderValuesContainsToken
public import Net.Spec.net.http.modelHeaderValueContainsToken

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelHeaderValuesContainsToken.wp_proof
    (wp_one : modelHeaderValueContainsToken.spec (GF := GF) (hG := hG)) :
    modelHeaderValuesContainsToken.spec (GF := GF) (hG := hG) := by
  intro values vs dq token
  wp_start as Hs
  ihave %Hsl := ownSlice_len $$ Hs
  wp_auto
  ihave HI : (∃ (i : w64) (x : GoString), "i" ∷ i_ptr ↦ i ∗ "v" ∷ v_ptr ↦ x ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i v]
  · iexists W64 0, _
    iframe
    ipureintro; decide
  wp_for HI
  by_cases hlt : sint.Z i < sint.Z values.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have hi : sint.nat i < vs.length := by rw [Hsl.1]; word
    obtain ⟨x0, hx0⟩ : ∃ x, vs[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, hlt⟩)]
    wp_apply (wp_load_slice_index values (sint.Z i) vs dq x0 Hi) $$ [Hs] as Hs
    · iframe; ipureintro; exact hx0
    wp_apply (wp_one x0 token) as %b1
    iintro -
    cases b1
    all_goals repeat (first | wp_if_destruct | wp_for_post | wp_auto)
    · iframe
      iexists _, _
      iframe
      ipureintro; word
    · iapply HΦ
      iframe
      ipureintro
      intro h; subst h; simp at hi
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; intro; rfl

end proof

end net.http
end Perennial
