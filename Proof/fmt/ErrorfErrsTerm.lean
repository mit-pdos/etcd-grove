/-
The proof of `Spec/fmt/ErrorfErrsTerm.lean` (2026-11-22, restated over error trees), from Perennial's `fmt.wp_Errorf`:
with no `%w` the result is a leaf `*errors.errorString` (`errTreeTerm_errorString`); with one, of the error argument
`e`, a `*fmt.wrapError` holding `e` (`fmt.wp_Errorf_wrap1`, `errTreeTerm_wrapError`).
-/
module

public import Spec.fmt.ErrorfErrsTerm
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
theorem fmt.ErrorfErrsTerm.wp_proof :
    fmt.ErrorfErrsTerm.spec (GF := GF) (hG := hG) := by
  intro format args_sl args errs hwf hw
  iintro %Φ ⟨#Hpkg, Hsl, #Herrs⟩ HΦ
  obtain ⟨ds, hds, hw0 | ⟨j, e, hj, hjx, he⟩⟩ := hw
  · obtain ⟨-, ds', hds', hargs⟩ := hwf
    rw [hds] at hds'
    cases hds'
    ihave #Hoks := BigSepL.bigSepL_mono (Φ := fun _ e => iprop(errOk (GF := GF) e ∗ errTreeTerm (GoInterface.ok e)))
      (Ψ := fun _ e => errOk (GF := GF) e) (fun {_ _} _ => by iintro ⟨H, -⟩; iexact H) $$ Herrs
    ihave Hargs := fmt.argsOkAt_of_errArgsAt (GF := GF) errs ds args hargs $$ Hoks
    ihave Hok := _root_.Perennial.fmt.argsOk_intro (GF := GF) (mv := fmt.errorfVerbs) hds $$ Hargs
    wp_apply (_root_.Perennial.fmt.wp_Errorf format args_sl args (DFrac.own 1)) $$ [$Hpkg $Hsl $Hok]
      as %err ⟨-, %s, -, Herr⟩
    iunfold _root_.Perennial.fmt.errorfErr at Herr
    icases Herr with ⟨%hp, #HE, Hw⟩
    simp only [hds, hw0]
    icases Hw with ⟨%l, %hl, -⟩
    subst hl
    iapply HΦ
    isplitl []
    · unfold errOk
      isplitr
      · ipureintro; exact ⟨hp.2.1, hp.2.2.1⟩
      imodintro
      iintro %Ψ HΨ
      iapply HE
      inext
      iapply HΨ
    · iapply errTreeTerm_errorString l
  · ihave #Hoks := BigSepL.bigSepL_mono (Φ := fun _ e => iprop(errOk (GF := GF) e ∗ errTreeTerm (GoInterface.ok e)))
      (Ψ := fun _ e => errOk (GF := GF) e) (fun {_ _} _ => by iintro ⟨H, -⟩; iexact H) $$ Herrs
    ihave #Ht := BigSepL.bigSepL_mem (Φ := fun e => iprop(errOk (GF := GF) e ∗ errTreeTerm (GoInterface.ok e)))
      he $$ Herrs
    icases Ht with ⟨-, #Ht⟩
    wp_apply (fmt.wp_Errorf_wrap1 format args_sl args errs e hwf ⟨ds, j, hds, hj, hjx⟩ he)
      $$ [$Hpkg $Hsl $Hoks] as %l ⟨#Hok, #Hc⟩
    iapply HΦ
    iframe Hok
    iapply errTreeTerm_wrapError l (GoInterface.ok e)
    iframe Hc Ht

end proof

end EtcdGrove
end Perennial
