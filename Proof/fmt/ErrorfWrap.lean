/-
The proof of `Spec/fmt/ErrorfWrap.lean` (`fmt.Errorf` of `pre ++ "%w"` over one error), over
Perennial's `fmt.wp_Errorf` (fmtmodel, 2026-11-20; over Perennial's previous model of `fmt.Errorf`,
`errors.New(format)`, from H0, 2026-11-18, `notes/perheap-scope.md` §5a; an axiom before).
-/
module

public import Spec.fmt.ErrorfWrap
public import Perennial.Proof.fmt
public import Proof.fmt.OutLemmas

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **`fmt.Errorf(pre ++ "%w", inner)`**, from Perennial's `fmt.wp_Errorf` (fmtmodel, 2026-11-20;
until then proved over the previous model, `errors.New(format)`, which neither formatted nor
wrapped: the left disjunct). The format's one directive is `%w`, of `inner`, an `error` whose
`Error()` returns needing nothing (`fmtErrorOk`, so `argOkAt`): Perennial's model returns Go's
`&wrapError{msg: s, err: inner}`, `s` the formatted string, which begins with `pre`
(`fmt.SprintfOut_litPrefix`, `pre` having no `%`): the right disjunct (`fmt.wrapErrIs`; its method
set is goose's, `Error` and `Unwrap`). (errdesc stage 2b, 2026-11-21: the description conjunct, and the
trust-boundary fact `rpctypes.errDesc_wrapError` it rested on, are gone with the pure `errDesc`;
`errorfWrap_descIs` proves the description's prefix.) -/
theorem fmt.ErrorfWrap.wp_proof : fmt.ErrorfWrap.spec (GF := GF) (hG := hG) := by
  intro pre args_sl inner dq hpre
  iintro %Φ ⟨#Hpkg, Hsl, #Hin⟩ HΦ
  have hds := fmt.fmtDirectives_pre_w pre hpre
  iunfold fmtErrorOk at Hin
  icases Hin with ⟨%hm, #HE⟩
  ihave #Hat := fmt.argOkAt_of_error (GF := GF) (mv := fmt.errorfVerbs) (d := ⟨W8 119, false⟩)
    (ii := inner) $$ [HE]
  · isplitr
    · ipureintro; exact ⟨by decide, rfl⟩
    isplitr
    · iexact HE
    · ipureintro; exact hm
  ihave Hok := _root_.Perennial.fmt.argsOk_intro (GF := GF) (mv := fmt.errorfVerbs)
    (xs := [GoInterface.ok inner]) hds $$ [Hat]
  · unfold _root_.Perennial.fmt.argsOkAt _root_.Perennial.fmt.argsOkAt
    isplitl
    · iexact Hat
    · itrivial
  wp_apply (_root_.Perennial.fmt.wp_Errorf (pre ++ go!"%w") args_sl [GoInterface.ok inner] dq)
    $$ [$Hpkg $Hsl $Hok] as %err ⟨Hsl, %s, %Hs, Herr⟩
  iunfold _root_.Perennial.fmt.errorfErr at Herr
  icases Herr with ⟨%-, #HEr, Hcase⟩
  have hw : _root_.Perennial.fmt.wrapArgs [⟨W8 119, false⟩] 1 = [0] := by decide
  have hae : _root_.Perennial.fmt.asError (GoInterface.ok inner) = GoInterface.ok inner := by
    simp only [_root_.Perennial.fmt.asError, _root_.Perennial.fmt.tsc_error, hm.2,
      _root_.Perennial.fmt.noArgStringSig, decide_true, ↓reduceIte]
  simp only [hds, List.length_singleton, hw, List.getElem?_cons_zero, Option.getD_some, hae]
  icases Hcase with ⟨%l, %hl, #Hmsg, #Herrc⟩
  subst hl
  have hpre' : pre <+: s := by
    have := fmt.SprintfOut_litPrefix Hs
    rwa [show go!"%w" = W8 37 :: go!"w" from rfl, fmt.litPrefix_append_pct _ _ hpre] at this
  obtain ⟨s', rfl⟩ := hpre'
  have ms := fun m => go.MethodSetIs.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) m
  iapply HΦ
  iframe Hsl
  iunfold fmt.errorfWrapIs
  iright
  iunfold fmt.wrapErrIs
  isplitr
  · ipureintro
    refine ⟨⟨_, l, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (have h := ms go!"Unwrap"; simpa [go.methodSetLookup] using h)
      | (have h := ms go!"As"; simp [go.methodSetLookup] at h; rw [h]; simp)
      | (have h := ms go!"Is"; simp [go.methodSetLookup] at h; rw [h]; simp)
      | (have h := ms go!"GRPCStatus"; simpa [go.methodSetLookup] using h)
      | exact _root_.Perennial.fmt.wrapError_facts.1
      | exact _root_.Perennial.fmt.wrapError_facts.2
  isplitr
  · iexists s'
    iexact HEr
  · imodintro
    iintro %Ψ HΨ
    iclear HEr HE Hat Hmsg
    rw [method_unfold]
    wp_auto
    iexact HΨ

end proof

end EtcdGrove
end Perennial
