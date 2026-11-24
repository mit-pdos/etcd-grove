/-
The proof of `shouldClose` (`Net/Spec/net/http/shouldClose.lean`): the `Connection` values (the header's
slice, or the nil slice when it has none) read by the model's `modelHeaderValuesContainsToken`, and the
entry deleted (`Header.Del`) when it holds `close` and the caller asks.
-/
module

public import Net.Spec.net.http.shouldClose
public import Net.Spec.net.http.Header__Del
public import Net.Spec.net.http.modelHeaderValuesContainsToken

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

theorem shouldClose.wp_proof
    (wp_HVCT : modelHeaderValuesContainsToken.spec (GF := GF) (hG := hG))
    (wp_Del : Header.Del.spec (GF := GF) (hG := hG)) :
    shouldClose.spec (GF := GF) (hG := hG) := by
  intro major minor h ms rm
  wp_start as ⟨Hm, Hv⟩
  try wp_auto
  wp_if_destruct
  · try wp_auto
    iapply HΦ; iexists ms; iframe; ipureintro; left; rfl
  wp_apply (wp_map_lookup1 (V := GoSlice) go.string (go.SliceType go.string) h _
    go!"Connection" _) $$ Hm as Hm
  ihave ⟨%vs, Hs, Hback⟩ : (∃ vs : List GoString,
      ((ms !! go!"Connection").getD (zero_val GoSlice)) ↦* vs ∗
      (((ms !! go!"Connection").getD (zero_val GoSlice)) ↦* vs -∗ hdrVals ms go!"Connection") :
      IProp GF) $$ [Hv]
  · cases hk : ms !! go!"Connection" with
    | none =>
      iexists []
      isplitl []
      · rw [show (none : Option GoSlice).getD (zero_val GoSlice) = slice.nil from rfl]
        iapply ownSlice_nil
      · iintro -
        simp only [hdrVals, hk]
        itrivial
    | some s =>
      simp only [hdrVals, hk]
      icases Hv with ⟨%vs, Hs⟩
      iexists vs
      iframe
      iintro Hs
      iexists vs
      iexact Hs
  try wp_auto
  wp_apply wp_HVCT $$ Hs as %hc ⟨Hs, -⟩
  try wp_auto
  cases hc <;> cases rm
  all_goals repeat (first | wp_if_destruct | wp_auto |
    (wp_apply wp_HVCT $$ Hs as %hc2 ⟨Hs, -⟩))
  all_goals (try rw [method_unfold (t := go.GoType.PointerType Header.ty) (m := go!"Del")])
  all_goals (try wp_auto)
  all_goals (try (wp_apply wp_Del h ms go!"Connection" $$ [Hm] as Hm
                  · iframe; ipureintro; decide))
  all_goals (try wp_auto)
  all_goals (try (iapply HΦ; iexists _; iframe Hm; ihave Hv := Hback $$ Hs; iframe Hv))
  all_goals (try (ipureintro; exact Or.inl rfl))
  all_goals (try (ipureintro; exact Or.inr ⟨trivial, rfl⟩))


end proof

end net.http
end Perennial
