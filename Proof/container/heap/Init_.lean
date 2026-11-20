/-
Proof of `Spec/container/heap/Init_.lean` (prove-smallinits, 2026-11-20: `Init` translated, over
`down`'s spec; until then the trust-boundary axiom). Lean-first.
-/
module

public import Spec.container.heap.Init_
public import Spec.container.heap.down

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : container.heap.Assumptions]

theorem heap.Init_.wp_proof
    (hdown : heap.down.spec (GF := GF) (hG := hG)) :
    heap.Init_.spec (GF := GF) (hG := hG) := by
  intro A h R E xs
  wp_start as ⟨#Hiface, HR⟩
  ihave #Hiface' := Hiface
  iunfold heap.heapIface at Hiface'
  icases Hiface' with ⟨#HLen, -, -, -⟩
  wp_auto
  wp_bind (App (Val #(methods h.ty go!"Len" h.v)) _)
  iapply HLen $$ %xs [$HR]
  inext
  iintro %n ⟨HR, %Hn⟩
  wp_auto
  ihave HI : (∃ (iv : w64) (ys : List A),
      "i" ∷ i_ptr ↦ iv ∗ "HR" ∷ R ys ∗
      "%Hi" ∷ ⌜ys.Perm xs ∧ -1 ≤ sint.Z iv⌝ : IProp GF) $$ [i HR]
  · iexists _, xs
    iframe
    ipureintro; exact ⟨List.Perm.refl _, by word⟩
  wp_for HI
  have Hl : ys.length = xs.length := Hi.1.length_eq
  wp_if_destruct
  · wp_apply (hdown A h R E ys iv n (by word) (by omega) (by omega)) $$ [$Hiface $HR]
      as %b ⟨%zs, HR, %Hzs⟩
    wp_for_post
    iframe
    iexists _, zs
    iframe
    ipureintro
    exact ⟨Hzs.trans Hi.1, by word⟩
  · iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hi.1

end proof

end EtcdGrove
end Perennial
