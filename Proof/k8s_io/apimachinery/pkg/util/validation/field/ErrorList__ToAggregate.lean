/-
`field.ErrorList.ToAggregate()` (`errors.go`, translated with its body): the proof of its spec,
over `fmt.Sprintf`'s generic spec (`fmt.SprintfArgs.spec`; each error formatted by its `Error()`,
`field/ErrorMethods.lean`), the generic `sets.Set`'s specs (through `sets.String`,
`sets/StringMethods.lean`) and `utilerrors.NewAggregate`'s (hypotheses). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorList__ToAggregate
public import Proof.k8s_io.apimachinery.pkg.util.validation.field.ErrorMethods
public import Proof.k8s_io.apimachinery.pkg.util.sets.StringMethods
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apimachinery.pkg.util.validation.field

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- `list.ToAggregate()`: `nil` for an empty list; else a loop over the list formatting each error
(`fmt.Sprintf("%v", err)`, its `Error()`), skipping one whose message the set `errorMsgs` has, else
adding the message to the set and the error to `errs`; then `utilerrors.NewAggregate(errs)`. -/
theorem ErrorList.ToAggregate.wp_proof
    (wp_SprintfArgs : EtcdGrove.fmt.SprintfArgs.spec (GF := GF) (hG := hG))
    (wp_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG)) :
    ErrorList.ToAggregate.spec (GF := GF) (hG := hG) := by
  intro s dq errs
  wp_start as ⟨Hs, #Herrs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · iapply HΦ; iframe
  wp_apply wp_slice_make3 (V := GoInterface) (W64 0) s.len ⟨by word, by word⟩ as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  wp_apply (sets.wp_NewString_nil_of wp_New) as %m Hm
  have HmsE : methodSet (go.GoType.PointerType Error.ty) !! go!"Format" = none := by
    have h1 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType Error.ty) go!"Format")
    simp only [go.methodSetLookup] at h1
    simpa using h1
  ihave IH : iprop(∃ (n : w64) (sl : GoSlice) (ys : List GoInterface)
      (ms : GMap GoString sets.Elem) (ev : Loc),
      "i" ∷ i_ptr ↦ n ∗
      "errs" ∷ errs_ptr ↦ sl ∗
      "Ho" ∷ sl ↦* ys ∗
      "Hocap" ∷ ownSliceCap GoInterface sl (DFrac.own 1) ∗
      "errorMsgs" ∷ errorMsgs_ptr ↦ m ∗
      "Hm" ∷ m ↦$ ms ∗
      "err" ∷ err_ptr ↦ ev ∗
      "Hs" ∷ s ↦*{dq} errs ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ errs.length⌝) $$ [i errs Ho Hocap errorMsgs Hm err Hs]
  · iexists W64 0, o0, [], ∅, _
    iframe
    ipureintro
    refine ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < errs.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hb.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    obtain ⟨x, Hx⟩ : ∃ x, errs[(sint.Z n).toNat]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index s (sint.Z n) errs dq x Hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    ihave #Hxok := BigSepL.bigSepL_lookup Hx $$ Herrs
    ihave #HxS := Error.error_stringMethodSpec wp_SprintfArgs x $$ [Hpkg Hxok]
    · iframe #
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply wp_SprintfArgs _ _ _ (DFrac.own 1) $$ [$Hasl] as %msg -
    · fmt_args_ok
    wp_apply (sets.String.wp_ptr_Has_of wp_Has errorMsgs_ptr (DFrac.own 1) m (DFrac.own 1) ms msg)
      $$ [$errorMsgs $Hm] as ⟨errorMsgs, Hm⟩
    wp_if_destruct
    · wp_for_post
      iframe
      iexists n + W64 1, _, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word⟩
    · wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %msl ⟨Hmsl, -⟩
      wp_apply (sets.String.wp_ptr_Insert_of wp_Insert errorMsgs_ptr (DFrac.own 1) m ms _ (DFrac.own 1) [msg])
        $$ [$errorMsgs $Hm $Hmsl] as ⟨errorMsgs, Hm, -⟩
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $Hosl] as %sl' ⟨Ho, Hocap, -⟩
      wp_for_post
      iframe
      iexists n + W64 1, _, _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word⟩
  · wp_apply wp_NewAggregate $$ [$Ho] as %a Ho
    iapply HΦ; iframe

end proof

end field
end EtcdGrove
end Perennial
