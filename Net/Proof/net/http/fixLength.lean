/-
The proof of `fixLength` (`Net/Spec/net/http/fixLength.lean`): no `Content-Length`, a response to a
request other than `HEAD`, not chunked: `0` for the statuses without a body, else `-1` after deleting
the (absent) `Content-Length`. `noResponseBodyExpected` is proved here (`wp_noResponseBodyExpected`).
-/
module

public import Net.Spec.net.http.fixLength
public import Net.Spec.net.http.Header__Del

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

theorem wp_noResponseBodyExpected (m : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! net.http.noResponseBodyExpected)) (Val #m))
    {{ RET #(decide (m = go!"HEAD")); True }} := by
  wp_start
  wp_auto
  iapply HΦ; itrivial

theorem fixLength.wp_proof (wp_Del : Header.Del.spec (GF := GF) (hG := hG)) :
    fixLength.spec (GF := GF) (hG := hG) := by
  intro status method h
  wp_start as ⟨%Hm, Hh⟩
  wp_auto
  wp_apply (wp_map_lookup1 (V := GoSlice) go.string (go.SliceType go.string) h _
    go!"Content-Length" _) $$ Hh as Hh
  all_goals
    repeat (first | wp_if_destruct | wp_apply wp_noResponseBodyExpected | wp_auto)
  · exact absurd rfl Hm
  all_goals
    repeat (first | wp_if_destruct | wp_auto)
  · iapply HΦ; iframe; ipureintro; left; rfl
  by_cases h304 : status = W64 304
  · rw [decide_eq_true h304]
    repeat (first | wp_if_destruct | wp_auto)
    iapply HΦ; iframe; ipureintro; left; rfl
  rw [decide_eq_false h304]
  repeat (first | wp_if_destruct | wp_auto)
  · iapply HΦ; iframe; ipureintro; left; rfl
  rw [method_unfold (t := go.GoType.PointerType Header.ty)]
  wp_auto
  wp_apply wp_Del h ∅ go!"Content-Length" $$ [Hh] as Hh
  · iframe; ipureintro; decide
  repeat (first | wp_if_destruct | wp_auto)
  rw [GMap.delete_empty]
  iapply HΦ; iframe; ipureintro; right; rfl

end proof

end net.http
end Perennial
