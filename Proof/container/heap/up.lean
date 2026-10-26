/-
Proof of `Spec/container/heap/up.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.container.heap.up
public import Proof.container.heap.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : container.heap.Assumptions]

theorem heap.up.wp_proof : heap.up.spec (GF := GF) (hG := hG) := by
  intro A h R E xs j Hj0 Hjl
  wp_start as ⟨#Hiface, HR⟩
  iunfold heap.heapIface at Hiface
  icases Hiface with ⟨#HLen, #HLess, #HSwap, #HPush⟩
  wp_auto
  ihave HI : (∃ (jv : w64) (ys : List A),
      "j" ∷ j_ptr ↦ jv ∗ "HR" ∷ R ys ∗
      "%Hj" ∷ ⌜ys.Perm xs ∧ 0 ≤ sint.Z jv ∧ sint.Z jv < xs.length⌝ : IProp GF) $$ [j HR]
  · iexists j, xs
    iframe
    ipureintro; exact ⟨List.Perm.refl _, Hj0, Hjl⟩
  wp_for HI
  have Hl : ys.length = xs.length := Hj.1.length_eq
  have Hp := heap.parent_range jv Hj.2.1
  wp_if_destruct
  · wp_for_post
    iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hj.1
  · wp_apply HLess $$ %ys %jv %(BitVec.sdiv (jv - W64 1) (W64 2)) [HR] as %b HR
    · iframe; ipureintro; refine ⟨Hj.2.1, ?_, Hp.1, ?_⟩ <;> rw [Hl] <;> word
    cases b
    · wp_auto
      wp_for_post
      iapply HΦ
      iexists ys
      iframe
      ipureintro; exact Hj.1
    · wp_auto
      wp_bind (App (App (Val #(methods h.ty go!"Swap" h.v)) _) _)
      iapply HSwap $$ %ys %(BitVec.sdiv (jv - W64 1) (W64 2)) %jv [HR]
      · iframe; ipureintro; refine ⟨Hp.1, ?_, Hj.2.1, ?_⟩ <;> rw [Hl] <;> word
      inext
      iintro HR
      wp_auto
      wp_for_post
      iframe
      iexists BitVec.sdiv (jv - W64 1) (W64 2), _
      iframe
      ipureintro
      exact ⟨(heap.listSwap_perm _ _ _).trans Hj.1, Hp.1, by word⟩

end proof

end EtcdGrove
end Perennial
