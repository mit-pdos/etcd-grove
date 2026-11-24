/-
The proof of `fixLength` (`Net/Spec/net/http/fixLength.lean`): no `Content-Length`, not chunked: `0`
for the statuses without a body, else, after deleting the (absent) `Content-Length` (`delete_absent`),
`0` for a request and `-1` for a response (to a request other than `HEAD`). `noResponseBodyExpected` is proved here (`wp_noResponseBodyExpected`).
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

theorem delete_absent (ms : GMap GoString GoSlice) (k : GoString) (h : ms !! k = none) :
    GMap.delete k ms = ms := by
  apply GMap.ext; intro k'
  by_cases hk : k = k'
  · subst hk; rw [h]; exact GMap.lookup_delete ms k
  · exact GMap.lookup_delete_ne ms hk

theorem fixLength.wp_proof (wp_Del : Header.Del.spec (GF := GF) (hG := hG)) :
    fixLength.spec (GF := GF) (hG := hG) := by
  intro isResp status method h ms
  wp_start as ⟨%Hm, %Hk, Hh⟩
  wp_auto
  wp_apply (wp_map_lookup1 (V := GoSlice) go.string (go.SliceType go.string) h _
    go!"Content-Length" _) $$ Hh as Hh
  rw [show ms !! go!"Content-Length" = (∅ : GMap GoString GoSlice) !! go!"Content-Length" from Hk]
  all_goals
    repeat (first | wp_if_destruct | wp_apply wp_noResponseBodyExpected | wp_auto)
  all_goals try (exfalso; exact Hm (by assumption) (by assumption))
  all_goals try (iapply HΦ; iframe; ipureintro; left; rfl)
  all_goals
    repeat (first | wp_if_destruct | wp_auto)
  all_goals try (iapply HΦ; iframe; ipureintro; left; rfl)
  all_goals try (exfalso; simp only [GMap.lookup_empty, Option.getD_none] at Hif; exact absurd Hif (by decide))
  all_goals
    by_cases h304 : status = W64 304
    all_goals try simp only [h304, decide_true, decide_false]
    all_goals try rw [decide_eq_false h304]
    all_goals
      repeat (first
        | (exfalso; contradiction)
        | (iapply HΦ; iframe; ipureintro; left; rfl)
        | (iapply HΦ; iframe; ipureintro; right; exact ⟨trivial, rfl⟩)
        | wp_if_destruct
        | wp_apply wp_noResponseBodyExpected
        | (iframe; ipureintro; decide)
        | wp_apply wp_Del h ms go!"Content-Length" $$ [Hh] as Hh
        | rw [method_unfold (t := go.GoType.PointerType Header.ty)]
        | rw [delete_absent ms _ Hk]
        | wp_auto)

end proof

end net.http
end Perennial
