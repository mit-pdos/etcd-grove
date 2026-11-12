/-
Proof of `Spec.container.heap.down.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.container.heap.down
public import Proof.container.heap.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : container.heap.Assumptions]

theorem heap.down.wp_proof : heap.down.spec (GF := GF) (hG := hG) := by
  intro A h R E xs i0 n Hi0 Hil Hn
  wp_start as ⟨#Hiface, HR⟩
  iunfold heap.heapIface at Hiface
  icases Hiface with ⟨#HLen, #HLess, #HSwap, #HPush⟩
  wp_auto
  ihave HI : (∃ (iv : w64) (ys : List A),
      "i" ∷ i_ptr ↦ iv ∗ "HR" ∷ R ys ∗
      "%Hi" ∷ ⌜ys.Perm xs ∧ 0 ≤ sint.Z iv ∧ sint.Z iv < xs.length⌝ : IProp GF) $$ [i HR]
  · iexists i0, xs
    iframe
    ipureintro; exact ⟨List.Perm.refl _, Hi0, Hil⟩
  wp_for HI
  have Hl : ys.length = xs.length := Hi.1.length_eq
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hi.1
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hi.1
  have HJ1 : 0 ≤ sint.Z (W64 2 * iv + W64 1) ∧ sint.Z (W64 2 * iv + W64 1) < ys.length := by
    rw [Hl]; word
  wp_join iprop(∃ jv : w64, "j" ∷ j_ptr ↦ jv ∗ "HR" ∷ R ys ∗ "h" ∷ h_ptr ↦ GoInterface.ok h ∗
      "%Hjv" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv < ys.length⌝) with [j HR h j1 j2]
    as ⟨%jv, j, HR, h, %Hjv⟩
  · have HJ2 : 0 ≤ sint.Z (W64 2 * iv + W64 1 + W64 1) ∧
        sint.Z (W64 2 * iv + W64 1 + W64 1) < ys.length := by
      rw [Hl]; word
    wp_apply HLess $$ %ys %(W64 2 * iv + W64 1 + W64 1) %(W64 2 * iv + W64 1) [HR] as %b HR
    · iframe; ipureintro; exact ⟨HJ2.1, HJ2.2, HJ1.1, HJ1.2⟩
    wp_if_destruct
    · isplitl []
      · ipureintro; trivial
      iexists _
      iframe
      ipureintro; exact HJ1
    · isplitl []
      · ipureintro; trivial
      iexists _
      iframe
      ipureintro; exact HJ2
  · iexists _
    iframe
    ipureintro; exact HJ1
  wp_apply HLess $$ %ys %jv %iv [HR] as %b HR
  · iframe; ipureintro; refine ⟨Hjv.1, Hjv.2, Hi.2.1, ?_⟩; rw [Hl]; exact Hi.2.2
  cases b
  · wp_auto
    wp_for_post
    iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hi.1
  · wp_auto
    wp_bind (App (App (Val #(methods h.ty go!"Swap" h.v)) _) _)
    iapply HSwap $$ %ys %iv %jv [HR]
    · iframe; ipureintro; refine ⟨Hi.2.1, ?_, Hjv.1, Hjv.2⟩; rw [Hl]; exact Hi.2.2
    inext
    iintro HR
    wp_auto
    wp_for_post
    iframe
    iexists jv, _
    iframe
    ipureintro
    refine ⟨(heap.listSwap_perm _ _ _).trans Hi.1, Hjv.1, ?_⟩
    rw [← Hl]; exact Hjv.2

end proof

end EtcdGrove
end Perennial
