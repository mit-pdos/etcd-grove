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
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

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
    unfold utilerrors.errTreeOrNil; itrivial
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
      "%Hb" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ errs.length⌝ ∗
      "%Hys" ∷ ⌜∀ y ∈ ys, ∃ x ∈ errs, y = interface.mkOk (go.GoType.PointerType Error.ty) #x⌝)
      $$ [i errs Ho Hocap errorMsgs Hm err Hs]
  · iexists W64 0, o0, [], ∅, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, by simp⟩
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
    have hF := go.method_set_is (t := go.GoType.PointerType Error.ty) go!"Format"
    have hE := go.method_set_is (t := go.GoType.PointerType Error.ty) go!"Error"
    simp (config := { decide := true }) only [go.methodSetLookup_cons, go.methodSetLookup_nil,
      gooseReduceIteDecide] at hF hE
    ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    wp_apply (wp_SprintfArgs go!"%v" [.dir none _root_.Perennial.fmt.verb_v] _ _ [.method fun _ => True] (DFrac.own 1)
        (by fmt_encode) (by fmt_fits)) $$ [$Hfmt $Hasl] as %msg -
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl
      · iapply (fmt.isArg_error ⟨go.GoType.PointerType Error.ty, #x⟩ hF
          (by simpa [_root_.Perennial.fmt.noArgStringSig] using hE))
        iexact HxS
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
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
      refine ⟨⟨by word, by word⟩, fun y hy => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact Hys y hy
      · exact ⟨x, List.mem_of_getElem? Hx, rfl⟩
  · wp_apply wp_NewAggregate $$ [$Ho] as %a ⟨Ho, Ha⟩
    iapply HΦ
    iframe
    icases Ha with (%ha | ⟨%sl, %zs, ⟨%ha, %hzs⟩, #Hzs⟩)
    · subst ha; unfold utilerrors.errTreeOrNil; itrivial
    · subst ha
      unfold utilerrors.errTreeOrNil
      iapply utilerrors.errTree_aggregate
      isplitr; · iexact Hzs
      have key : ∀ z, z ∈ zs →
          iprop(□ (isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field ∗
            [∗list] e ∈ errs, errorOk e)) ⊢ utilerrors.errTree z := by
        intro z hzin
        obtain ⟨-, hzm⟩ := hzs z hzin
        obtain ⟨x, hx, rfl⟩ := Hys z hzm
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
        iintro #⟨#Hpkg, #Herrs⟩
        ihave #Hxok := BigSepL.bigSepL_lookup hj $$ Herrs
        ihave #HxS := Error.error_stringMethodSpec wp_SprintfArgs x $$ [Hpkg Hxok]
        · iframe #
        iapply utilerrors.errTree_of_leaf
        simp only [utilerrors.errLeafOk, errOk]
        isplitr
        · isplitr
          · ipureintro
            have h2 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType Error.ty) go!"Error")
            simp only [go.methodSetLookup] at h2
            exact ⟨HmsE, by simpa [noArgStringSig] using h2⟩
          · iunfold fmt.stringMethodSpec at HxS
            iexact HxS
        · ipureintro
          have h3 := (go.MethodSetIs.method_set_is (t := go.GoType.PointerType Error.ty) go!"Errors")
          simp only [go.methodSetLookup] at h3
          simpa using h3
      iapply (BigSepL.bigSepL_intro (P := iprop(□ (isPkgInit (PROP := IProp GF)
          pkg_id.k8s_io.apimachinery.pkg.util.validation.field ∗ [∗list] e ∈ errs, errorOk e)))
        (fun k z hz => key z (List.mem_of_getElem? hz)))
      imodintro
      iframe #

end proof

end field
end EtcdGrove
end Perennial
