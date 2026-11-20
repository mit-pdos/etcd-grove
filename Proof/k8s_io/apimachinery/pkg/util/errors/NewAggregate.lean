/-
`utilerrors.NewAggregate(errlist)` (`k8s.io/apimachinery/pkg/util/errors/errors.go`, translated
with its body): the proof of its spec (`Spec/.../util/errors/NewAggregate.lean`), for conditional
authorization's proofs (the union builder's and the evaluation's aggregated errors) and the node
selector's. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.errors

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.errors.Assumptions]

/-- `NewAggregate(errlist)`: `nil` for an empty list, else a loop over the list (reading each
element, comparing it with `nil`) appending the non-`nil` ones to a fresh slice `errs`, then `nil`
if `errs` is empty, else `aggregate(errs)` converted to `Aggregate`. -/
theorem NewAggregate.wp_proof : NewAggregate.spec (GF := GF) (hG := hG) := by
  intro s dq es
  wp_start as Hs
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave Hn : (slice.nil ↦* ([] : List GoInterface) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hc : ownSliceCap (GF := GF) GoInterface slice.nil (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (sl : GoSlice) (ys : List GoInterface) (ev : GoInterface),
      "i" ∷ i_ptr ↦ n ∗
      "errs" ∷ errs_ptr ↦ sl ∗
      "Hn" ∷ sl ↦* ys ∗
      "Hc" ∷ ownSliceCap GoInterface sl (DFrac.own 1) ∗
      "e" ∷ e_ptr ↦ ev ∗
      "Hs" ∷ s ↦*{dq} es ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ es.length⌝) $$ [i errs Hn Hc e Hs]
  · iexists W64 0, slice.nil, [], _
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < es.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hb.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨x, Hx⟩ : ∃ x, es[(sint.Z n).toNat]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index s (sint.Z n) es dq x Hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    cases x with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word⟩
    | ok i =>
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_apply wp_slice_append $$ [$Hn $Hc $Hosl] as %sl' ⟨Hn, Hc, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word⟩
  · wp_if_destruct
    · iapply HΦ
      iframe
    · iapply HΦ
      iframe

end proof

end utilerrors
end EtcdGrove
end Perennial
