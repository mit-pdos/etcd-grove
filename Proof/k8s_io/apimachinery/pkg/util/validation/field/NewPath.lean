/-
`field.NewPath(name, moreNames...)` (`path.go`, translated with its body): the proof of its spec.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.NewPath

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode 

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- `NewPath(name, moreNames...)` allocates a `*Path` for `name`, then a child for each of
`moreNames` (a loop over the slice, read only). -/
theorem NewPath.wp_proof : NewPath.spec (GF := GF) (hG := hG) := by
  intro name s dq more
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave IH : iprop(∃ (n : w64) (rp : Loc) (an : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "r" ∷ r_ptr ↦ rp ∗
      "anotherName" ∷ anotherName_ptr ↦ an ∗
      "Hs" ∷ s ↦*{dq} more ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ more.length⌝) $$ [i r anotherName Hs]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < more.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hb.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨x, Hx⟩ : ∃ x, more[(sint.Z n).toNat]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index s (sint.Z n) more dq x Hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    wp_for_post
    iframe
    iexists n + W64 1, _, _
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  · iapply HΦ
    iframe

end proof

end field
end EtcdGrove
end Perennial
