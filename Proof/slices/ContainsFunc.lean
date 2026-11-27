/-
Proof of `Spec/slices/ContainsFunc.lean`: an instance of Perennial's proved `slices.ContainsFunc`
(translated with its body since Perennial 52d62e83c), for a predicate that says nothing. Until
the pin bump to it, an axiom here (the trust boundary). Lean-first (no Rocq counterpart).
-/
module

public import Spec.slices.ContainsFunc
public import Perennial.Spec.slices.ContainsFunc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace slices

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.slices.Assumptions]

theorem ContainsFunc.wp_proof
    (wp_ContainsFunc : _root_.Perennial.slices.ContainsFunc.spec (GF := GF) (hG := hG)) :
    ContainsFunc.spec (GF := GF) (hG := hG) := by
  intro V _ _ E _ s dq xs f
  iintro %Φ ⟨Hs, #Hf⟩ HΦ
  wp_apply (wp_ContainsFunc (S := go.GoType.SliceType E) s dq xs f (fun _ _ => True)) $$ [Hs]
    as %b ⟨Hs, -⟩
  · iframe
    unfold _root_.Perennial.slices.funcAnswers
    iintro !> %x %Hx
    ispecialize Hf $$ %x %Hx
    iintro !> %Ψ _ HΨ
    iapply Hf
    · itrivial
    iintro !> %b _
    iapply HΨ
    ipureintro
    trivial
  iapply HΦ
  iexact Hs

end proof

end slices
end EtcdGrove
end Perennial
