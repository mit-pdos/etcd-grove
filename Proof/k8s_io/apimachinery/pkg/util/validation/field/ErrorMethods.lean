/-
`*field.Error`'s `Error()` (translated with its body, as `ErrorBody` and `ErrorType.String` are):
for an error that is `field.errorOk` (`Spec/.../field/ErrorOk.lean`), it returns some string,
needing nothing but `fmt`'s initialization (`fmt.stringMethodSpec`, what `fmt` needs of a `%v`
argument). From `fmt.Sprintf`'s generic spec (`fmt.SprintfArgs.spec`, a hypothesis). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorOk
public import Spec.fmt.SprintfArgs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.validation.field

/-- `string` is not an interface type (for Go's method call on a value of a named string type,
`ErrorType`'s `String`: `go_method_resolve_step` asks it of the underlying type). -/
instance notInterface_string : go.NotInterface go.string := ⟨by unfold go.string; trivial⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- `ErrorType(t).String()` returns some string (a constant, or `fmt.Sprintf` of `t` quoted). -/
theorem ErrorType.string_stringMethodSpec
    (wp_SprintfArgs : EtcdGrove.fmt.SprintfArgs.spec (GF := GF) (hG := hG)) (t : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.fmt ⊢
      _root_.Perennial.fmt.stringMethodSpec (GF := GF) ⟨ErrorType.ty, #t⟩ go!"String" := by
  iintro #Hinit
  unfold _root_.Perennial.fmt.stringMethodSpec
  imodintro
  iintro %Φ HΦ
  simp only [method_unfold]
  unfold ErrorType.String.impl
  wp_auto
  repeat (wp_if_destruct; · iapply HΦ)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply (_root_.Perennial.fmt.Sprintf_pure_of wp_SprintfArgs go!"<unknown error %q>" [.lit go!"<unknown error ", .dir none _root_.Perennial.fmt.verb_q, .lit go!">"] _
      [interface.mkOk go.string #t] _ (DFrac.own 1) (by fmt_encode) ?fits (.str _ _ _ .nil))
    $$ [$Hinit $Hasl] as %str -
  case fits => fmt_fits
  iapply HΦ

/-- `ErrorType`'s method set: `String() string`, no `Format`, no `Error` (goose's
`ErrorType.TypeAssumptions`). -/
theorem ErrorType.methodSet_facts :
    methodSet ErrorType.ty !! go!"Format" = none ∧ methodSet ErrorType.ty !! go!"Error" = none ∧
      methodSet ErrorType.ty !! go!"String" = some _root_.Perennial.fmt.noArgStringSig ∧
      methodSet ErrorType.ty !! go!"CanInterface" = none := by
  have h1 := (go.MethodSetIs.method_set_is (t := ErrorType.ty) go!"Format")
  have h2 := (go.MethodSetIs.method_set_is (t := ErrorType.ty) go!"Error")
  have h3 := (go.MethodSetIs.method_set_is (t := ErrorType.ty) go!"String")
  have h4 := (go.MethodSetIs.method_set_is (t := ErrorType.ty) go!"CanInterface")
  simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3 h4
  exact ⟨by simpa using h1, by simpa using h2,
    by simpa [_root_.Perennial.fmt.noArgStringSig] using h3, by simpa using h4⟩

/-- The variable `omitValue` (a field-less struct): its points-to is its address's not being `nil`,
`field`'s fact (`fieldInit`). -/
theorem omitValue_pointsto (dq : DFrac) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field ⊢
      globalAddr omitValue ↦{dq} (OmitValueType.mk) := by
  iintro #Hpkg
  ihave %Hnn : (k8s_io.apiserver.pkg.storage.etcd3.fieldInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  simp only [TypedPointsto.typedPointstoDef]
  isplitl
  · itrivial
  · ipureintro; exact Hnn

/-- `e.ErrorBody()` of a read-only `*Error` of a known type with a string bad value returns some
string. -/
theorem Error.wp_ErrorBody
    (wp_SprintfArgs : EtcdGrove.fmt.SprintfArgs.spec (GF := GF) (hG := hG))
    (e : Loc) (v : Error)
    (hty : v.Type' ∈ knownErrorTypes) (hbad : ∃ str : GoString, v.BadValue' = interface.mkOk go.string #str) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field ∗ e ↦□ v }}
      (App (Val (e @!! go.GoType.PointerType Error.ty @!! go!"ErrorBody")) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  obtain ⟨str, hstr⟩ := hbad
  wp_start as #He
  iStructNamed He
  ihave Ho := omitValue_pointsto (DFrac.own 1) $$ Hpkg
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #HTs := ErrorType.string_stringMethodSpec wp_SprintfArgs v.Type' $$ Hfmt
  have Hms : methodSet ErrorType.ty !! go!"Format" = none ∧ methodSet ErrorType.ty !! go!"Error" = none ∧
      methodSet ErrorType.ty !! go!"String" = some _root_.Perennial.fmt.noArgStringSig ∧
      methodSet ErrorType.ty !! go!"CanInterface" = none := ErrorType.methodSet_facts
  have Hne : (go.string = OmitValueType.ty) = False := by
    simp only [eq_iff_iff, iff_false]; unfold OmitValueType.ty go.string
    intro hh; injection hh with h1; simp at h1
  simp only [knownErrorTypes, List.mem_cons, List.not_mem_nil, or_false] at hty
  rcases hty with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp only [h]
  all_goals
    wp_auto
    first
    | (simp only [hstr, interface.mkOk, Hne, ↓reduceIte]
       (try wp_auto)
       wp_apply wp_slice_literal
       isplitr
       · ipureintro; rfl
       iintro %asl ⟨Hasl, -⟩
       wp_apply (wp_SprintfArgs go!"%s: %q" [.dir none _root_.Perennial.fmt.verb_s, .lit go!": ", .dir none _root_.Perennial.fmt.verb_q] _ _
           [.method fun _ => True, .str _] (DFrac.own 1) (by fmt_encode) (by fmt_fits))
         $$ [$Hfmt $Hasl] as %s1 -
       · iapply BigSepL2.bigSepL2_cons.2
         isplitl
         · iapply (fmt.isArg_stringer (GF := GF) ⟨ErrorType.ty, #v.Type'⟩ Hms.1 Hms.2.1 Hms.2.2.1 Hms.2.2.2)
           iexact HTs
         iapply BigSepL2.bigSepL2_cons.2
         isplitr; · simp only [_root_.Perennial.fmt.isArg]; ipureintro; rfl
         iapply BigSepL2.bigSepL2_nil.2; itrivial)
    | ((try simp only [method_unfold])
       (try wp_auto)
       iunfold _root_.Perennial.fmt.stringMethodSpec at HTs
       wp_apply HTs as %s1)
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as -
    wp_if_destruct
    · iapply HΦ; itrivial
    · wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      wp_apply (_root_.Perennial.fmt.Sprintf_pure_of wp_SprintfArgs go!": %s" [.lit go!": ", .dir none _root_.Perennial.fmt.verb_s] _ _ _ (DFrac.own 1)
          (by fmt_encode) (by fmt_fits) (.str _ _ _ .nil)) $$ [$Hfmt $Hasl] as %s2 -
      iapply HΦ; itrivial

/-- **`(*Error).Error()` of an `errorOk` error returns some string**, needing nothing more (its
`fmt.stringMethodSpec`): `fmt.Sprintf("%s: %s", e.Field, e.ErrorBody())`. -/
theorem Error.error_stringMethodSpec
    (wp_SprintfArgs : EtcdGrove.fmt.SprintfArgs.spec (GF := GF) (hG := hG)) (e : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation.field ∗ errorOk e ⊢
      _root_.Perennial.fmt.stringMethodSpec (GF := GF) ⟨go.GoType.PointerType Error.ty, #e⟩ go!"Error" := by
  iintro ⟨#Hpkg, #He⟩
  iunfold errorOk at He
  icases He with ⟨%v, #He, %Hty, %Hbad⟩
  unfold _root_.Perennial.fmt.stringMethodSpec
  imodintro
  iintro %Φ HΦ
  simp only [method_unfold]
  ihave #He' := He
  iStructNamed He'
  wp_auto
  wp_apply (Error.wp_ErrorBody wp_SprintfArgs e v Hty Hbad) $$ [] as %b -
  · iexact He
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply (_root_.Perennial.fmt.Sprintf_pure_of wp_SprintfArgs go!"%s: %s" [.dir none _root_.Perennial.fmt.verb_s, .lit go!": ", .dir none _root_.Perennial.fmt.verb_s] _ _ _ (DFrac.own 1)
      (by fmt_encode) ?fits ?pa) $$ [$Hfmt $Hasl] as %s1 -
  case pa =>
    (try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]); (try simp only [List.set_cons_succ, List.set_cons_zero])
    exact .str _ _ _ (.str _ _ _ .nil)
  case fits => fmt_fits
  iapply HΦ

end proof

end field
end EtcdGrove
end Perennial
