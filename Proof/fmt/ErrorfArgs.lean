/- Lean-first (no Rocq counterpart).

# The error arguments of `fmt.Errorf` as Perennial's `fmt.argsOk` (moved out of `ErrorfErrs.lean`, 2026-11-22, so
that the proofs of `fmt.ErrorfErrs`, `ErrorfErrsNot` and `ErrorfErrsTerm` share them)
-/
module

public import Spec.fmt.ErrorfErrs
public import Perennial.Proof.fmt
public import Spec.fmt.ErrorfErrsNot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section args
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.fmt.Assumptions] [_root_.Perennial.errors.Assumptions]

/-- An argument `fmt.errArgAt` its directive, the error arguments `errOk`, is `fmt.argOkAt` it under
`Errorf`'s verbs. -/
theorem fmt.argOkAt_of_errArgAt (errs : List GoInterfaceOk) (d : fmt.Directive) (a : GoInterface)
    (h : fmt.errArgAt errs d a) :
    ([∗list] e ∈ errs, errOk (GF := GF) e) ⊢ fmt.argOkAt fmt.errorfVerbs d a := by
  iintro #Herrs
  cases a with
  | nil => unfold _root_.Perennial.fmt.argOkAt; itrivial
  | ok ii =>
    rcases h with hw | ⟨hmem, hv, hs⟩
    · unfold _root_.Perennial.fmt.argOkAt; ileft; ipureintro; exact hw
    · ihave #He := BigSepL.bigSepL_mem (Φ := fun e => errOk (GF := GF) e) hmem $$ Herrs
      unfold errOk
      icases He with ⟨%hm, #HW⟩
      iapply fmt.argOkAt_of_error
      isplitr
      · ipureintro
        refine ⟨?_, hs⟩
        simp only [fmt.errArgVerbs, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with h | h | h <;> rw [h] <;> decide
      isplitr
      · rw [fmt.stringMethodSpec_unfold]; iexact HW
      · ipureintro; exact hm

theorem fmt.argsOkAt_of_errArgsAt (errs : List GoInterfaceOk) (ds : List fmt.Directive)
    (xs : List GoInterface) (h : fmt.errArgsAt errs ds xs) :
    ([∗list] e ∈ errs, errOk (GF := GF) e) ⊢ fmt.argsOkAt fmt.errorfVerbs ds xs := by
  induction xs generalizing ds with
  | nil => iintro -; cases ds <;> (unfold _root_.Perennial.fmt.argsOkAt; itrivial)
  | cons a xs ih =>
    iintro #Herrs
    cases ds with
    | nil =>
      obtain ⟨h1, h2⟩ := h
      unfold _root_.Perennial.fmt.argsOkAt
      isplitl []
      · iapply (fmt.argOkAt_of_errArgAt errs _ a h1); iexact Herrs
      · iapply (ih [] h2); iexact Herrs
    | cons d ds =>
      obtain ⟨h1, h2⟩ := h
      unfold _root_.Perennial.fmt.argsOkAt
      isplitl []
      · iapply (fmt.argOkAt_of_errArgAt errs d a h1); iexact Herrs
      · iapply (ih ds h2); iexact Herrs

/-- An error argument (`errOk`: `Error() string`) is an `error`: `fmt.asError` keeps it. -/
theorem fmt.asError_errOk (e : GoInterfaceOk)
    (hm : methodSet e.ty !! go!"Error" = some _root_.Perennial.fmt.noArgStringSig) :
    _root_.Perennial.fmt.asError (GoInterface.ok e) = GoInterface.ok e := by
  have h : go.typeSetContains e.ty go.error = true := by
    go_type_set
    simp only [go.typeSetElemContains, decide_eq_true_eq]
    exact hm
  simp [_root_.Perennial.fmt.asError, h]

/-- What `fmt.Errorf` returns with one `%w` of `e` (`fmt.wrapsErr`): an `errOk` `*fmt.wrapError` holding `e`. -/
theorem fmt.wp_Errorf_wrap1 (format : GoString) (args_sl : GoSlice) (args : List GoAny)
    (errs : List GoInterfaceOk) (e : GoInterfaceOk)
    (hwf : fmt.errArgsWf errs format args) (hw : fmt.wrapsErr format args e) (he : e ∈ errs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args ∗ ([∗list] e ∈ errs, errOk e) }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l);
        errOk ⟨go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty, #l⟩ ∗
        l.[fmt.wrapError, go!"err"] ↦□ GoInterface.ok e }} := by
  obtain ⟨-, ds, hds, hargs⟩ := hwf
  obtain ⟨ds', j, hds', hj, hjx⟩ := hw
  rw [hds] at hds'
  cases hds'
  iintro %Φ ⟨#Hpkg, Hsl, #Herrs⟩ HΦ
  ihave #He := BigSepL.bigSepL_mem (Φ := fun e => errOk (GF := GF) e) he $$ Herrs
  ihave %hm : ⌜methodSet e.ty !! go!"Error" = some _root_.Perennial.fmt.noArgStringSig⌝ $$ [He]
  · iunfold errOk at He; icases He with ⟨%h, -⟩; ipureintro; exact h.2
  ihave Hargs := fmt.argsOkAt_of_errArgsAt (GF := GF) errs ds args hargs $$ Herrs
  ihave Hok := _root_.Perennial.fmt.argsOk_intro (GF := GF) (mv := fmt.errorfVerbs) hds $$ Hargs
  wp_apply (_root_.Perennial.fmt.wp_Errorf format args_sl args (DFrac.own 1)) $$ [$Hpkg $Hsl $Hok]
    as %err ⟨-, %s, -, Herr⟩
  iunfold _root_.Perennial.fmt.errorfErr at Herr
  icases Herr with ⟨%hp, #HE, Hw⟩
  simp only [hds, hj, hjx, Option.getD_some, fmt.asError_errOk e hm]
  icases Hw with ⟨%l, %hl, -, #Hc⟩
  subst hl
  iapply HΦ
  iframe Hc
  unfold errOk
  isplitr
  · ipureintro; exact ⟨hp.2.1, hp.2.2.1⟩
  imodintro
  iintro %Ψ HΨ
  iapply HE
  inext
  iapply HΨ

end args

end EtcdGrove
end Perennial
