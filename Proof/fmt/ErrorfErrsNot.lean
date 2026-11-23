/-
The proof of `Spec/fmt/ErrorfErrsNot.lean` (2026-11-22, restated over error trees), from Perennial's `fmt.wp_Errorf`:
with one `%w` of the error argument `e`, the result is a `*fmt.wrapError` holding `e` (`fmt.errorfErr`), whose tree is
`e`'s with it added (`errTreeNot_wrapError`, `errTreeTerm_wrapError`, `Proof/errors/ErrTree.lean`); it is not the
target, whose type is not `*fmt.wrapError`.
-/
module

public import Spec.fmt.ErrorfErrsNot
public import Proof.fmt.ErrorfArgs
public import Proof.errors.ErrTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.fmt.Assumptions] [_root_.Perennial.errors.Assumptions]

/-- See the spec's file header. -/
theorem fmt.ErrorfErrsNot.wp_proof :
    fmt.ErrorfErrsNot.spec (GF := GF) (hG := hG) := by
  intro format args_sl args errs e t hwf hw he ht
  iintro %Φ ⟨#Hpkg, Hsl, #Herrs, #Hn, #Ht⟩ HΦ
  wp_apply (fmt.wp_Errorf_wrap1 format args_sl args errs e hwf hw he) $$ [$Hpkg $Hsl $Herrs]
    as %l ⟨#Hok, #Hc⟩
  have hne : interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l ≠ t := by
    intro h
    cases t with
    | nil => cases h
    | ok tii =>
      exact (ht tii rfl).2 (by cases h; rfl)
  iapply HΦ
  iframe Hok
  isplitl []
  · iapply errTreeNot_wrapError l (GoInterface.ok e) t hne
    iframe Hc Hn
  · iapply errTreeTerm_wrapError l (GoInterface.ok e)
    iframe Hc Ht

end proof

end EtcdGrove
end Perennial
