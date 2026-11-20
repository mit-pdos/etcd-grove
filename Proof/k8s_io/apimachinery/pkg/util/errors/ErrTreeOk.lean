/-
**An error tree is `errOk`** (2026-11-20): its `Error()` returns some string needing nothing (a
leaf's by `errOk`, an `aggregate`'s by `aggregate.Error`'s spec), its type has `Error() string` and no
`Format`. What `fmt.Errorf("%w", err)` asks of an error (`fmt.argOkAt` under `w`). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.errors.aggregate__Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.errors

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.errors.Assumptions]

/-- A tree's `errOk`. -/
theorem errTreeN_errOk (wp_Error : aggregate.Error.spec (GF := GF) (hG := hG)) (n : Nat)
    (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors ∗ errTreeN n e ⊢
      ∃ ii : GoInterfaceOk, ⌜e = .ok ii⌝ ∗ errOk ii := by
  iintro ⟨#Hpkg, #He⟩
  ihave Hcase : iprop(errLeafOk e ∨ ∃ (m : Nat) (sl : GoSlice) (ys : List GoInterface),
      ⌜e = interface.mkOk aggregate.ty #sl⌝ ∗ sl ↦*□ ys ∗ [∗list] z ∈ ys, errTreeN m z) $$ [He]
  · cases n with
    | zero => simp only [errTreeN]; ileft; iexact He
    | succ m =>
      rw [errTreeN]
      icases He with (Hl | ⟨%sl, %ys, %he, #Hs, #Hys⟩)
      · ileft; iexact Hl
      · iright
        iexists m, sl, ys
        isplitr; · ipureintro; exact he
        isplitr; · iexact Hs
        iexact Hys
  icases Hcase with (#Hl | ⟨%m, %sl, %ys, %he, #Hs, #Hys⟩)
  · cases e with
    | nil => simp only [errLeafOk]; iexfalso; iexact Hl
    | ok ii =>
      simp only [errLeafOk]
      icases Hl with ⟨#Hok, -⟩
      iexists ii
      isplitr; · ipureintro; rfl
      iexact Hok
  · subst he
    iexists ⟨aggregate.ty, #sl⟩
    isplitr; · ipureintro; rfl
    simp only [errOk]
    isplitr
    · ipureintro
      have h1 := (go.MethodSetIs.method_set_is (t := aggregate.ty) go!"Format")
      have h2 := (go.MethodSetIs.method_set_is (t := aggregate.ty) go!"Error")
      simp only [go.methodSetLookup] at h1 h2
      exact ⟨by simpa using h1, by simpa [noArgStringSig] using h2⟩
    iintro !> %Φ HΦ
    iapply (wp_Error m sl ys)
    · iframe #
    · inext; iintro %str -; iapply HΦ

/-- A tree is `errOk`. -/
theorem errTree_errOk (wp_Error : aggregate.Error.spec (GF := GF) (hG := hG)) (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors ∗ errTree e ⊢
      ∃ ii : GoInterfaceOk, ⌜e = .ok ii⌝ ∗ errOk ii := by
  iintro ⟨#Hpkg, #He⟩
  unfold errTree
  icases He with ⟨%n, #He⟩
  iapply errTreeN_errOk wp_Error n e
  iframe #

/-- `nil` or a tree is `errOkOrNil`. -/
theorem errTreeOrNil_errOkOrNil (wp_Error : aggregate.Error.spec (GF := GF) (hG := hG))
    (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.errors ∗ errTreeOrNil e ⊢
      errOkOrNil e := by
  cases e with
  | nil => unfold errOkOrNil; iintro -; itrivial
  | ok ii =>
    unfold errTreeOrNil errOkOrNil
    iintro ⟨#Hpkg, #He⟩
    ihave ⟨%ii', %h, #Hok⟩ := errTree_errOk wp_Error (.ok ii) $$ [Hpkg He]
    · iframe #
    cases h
    iexact Hok

end lemmas

end utilerrors
end EtcdGrove
end Perennial
