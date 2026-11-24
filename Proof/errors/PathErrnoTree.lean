/- Lean-first (no Rocq counterpart).

# The error tree of a `*PathError` of an errno

`os.errnoPathErr err e` (`&PathError{Op, Path, Errno(e)}`, what the part's `os` models return on a failed system
call) is a two-error tree for `errors.Is`: the `*PathError` (no `Is` method; `Unwrap` returns its `Err` field, the
`Errno`) and the `Errno` (its `Is`, `wp_Errno_Is`; no `Unwrap`). `pathErrno_walkTree` states it with exact
relations, the `Errno`'s `Is` answer any relation `Ie` that `ErrnoIsPost` implies; the four `errors.Is` specs of
`Spec/errors/` (`IsErrno`, `IsPathErrnoEof`, `IsPathErrnoTerm`) and `IsPathErrnoNotExist` are proved over it.
-/
module

public import Proof.syscall.ErrnoIs
public import Proof.os.ErrnoPathErr
public import Proof.os.PkgInit
public import Perennial.Proof.errors.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section defs
variable [GooseExts] [GoGlobalContext]

/-- The errors of the tree of the `*PathError` `err` of the errno `e`. -/
abbrev peS (err : GoInterface) (e : w64) : GoError → Prop :=
  fun x => x = err ∨ x = errnoErr e

/-- What each error's `Is` answers: the `*PathError` has none (`false`), the `Errno` answers by `Ie`. -/
abbrev peI (err : GoInterface) (e : w64) (Ie : Bool → Prop) : GoInterfaceOk → Bool → Prop :=
  fun ii b => (interface.ok ii = err → b = false) ∧ (interface.ok ii = errnoErr e → Ie b) ∧
    (interface.ok ii ≠ err → interface.ok ii ≠ errnoErr e → b = false)

/-- What each error's `Unwrap` returns: the `*PathError` the `Errno`, the `Errno` nothing. -/
abbrev peU (err : GoInterface) (e : w64) : GoInterfaceOk → List GoError → Prop :=
  fun ii cs => (interface.ok ii = err → cs = [errnoErr e]) ∧ (interface.ok ii ≠ err → cs = [])

/-- An `Errno` is no pointer error. -/
theorem errno_ne_ptr (T : go.GoType) : syscall.Errno.ty ≠ go.GoType.PointerType T := by
  rw [← errno_ty_eq]; intro h; cases h

/-- A `*PathError` is no `*errorString`. -/
theorem pathError_ne_es (pe x : Loc) :
    interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe ≠ esErr x := by
  unfold esErr interface.mkOk
  intro h
  injection h with h
  injection h with h
  injection h with h
  rw [io.fs.PathError.ty.eq_1, _root_.Perennial.errors.errorString.ty.eq_1] at h
  injection h with h
  revert h; decide

/-- An `Errno` is no `*errorString`. -/
theorem errno_ne_es (e : w64) (he : e ≠ 0) (x : Loc) : errnoErr e ≠ esErr x := by
  unfold errnoErr esErr; simp only [he, ↓reduceIte]
  unfold interface.mkOk
  intro h
  injection h with h
  injection h with h
  exact errno_ne_ptr _ h

/-- **`peS` is typed** at a target whose dynamic type is a pointer type: the `*PathError` holds a pointer, the
`Errno` is of another type. -/
theorem peS_treeTyped (pe : Loc) (e : w64) (he : e ≠ 0) (t : GoInterface)
    (ht : ∀ tii, t = interface.ok tii → ∃ T, tii.ty = go.GoType.PointerType T) :
    _root_.Perennial.errors.TreeTyped (peS (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) e) t := by
  have hen : errnoErr e = interface.mkOk syscall.Errno.ty #e := by
    unfold errnoErr; simp only [he, ↓reduceIte]
  intro ii tii hii htt hty
  rcases hii with hii | hii
  · cases hii; exact ⟨pe, rfl⟩
  · rw [hen] at hii; cases hii
    obtain ⟨T, hT⟩ := ht tii htt
    exact absurd (hty.trans hT) (errno_ne_ptr T)


end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `syscall.Errno`'s methods: `Is(error) bool`, no `Unwrap`. -/
theorem errno_methods [syscall.Assumptions] :
    methodSet syscall.Errno.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool]) ∧
    methodSet syscall.Errno.ty !! go!"Unwrap" = none := by
  have h1 := go.MethodSetIs.method_set_is (t := syscall.Errno.ty) go!"Is"
  have h2 := go.MethodSetIs.method_set_is (t := syscall.Errno.ty) go!"Unwrap"
  refine ⟨?_, ?_⟩
  · rw [h1]; try simp [go.methodSetLookup]
  · rw [h2]; try decide

/-- `*fs.PathError`'s methods: no `Is`, `Unwrap() error`. -/
theorem pathError_methods [os.Assumptions] :
    methodSet (go.GoType.PointerType io.fs.PathError.ty) !! go!"Is" = none ∧
    methodSet (go.GoType.PointerType io.fs.PathError.ty) !! go!"Unwrap" =
      some (go.Signature [] false [go.error]) := by
  have h1 := go.MethodSetIs.method_set_is (t := go.GoType.PointerType io.fs.PathError.ty) go!"Is"
  have h2 := go.MethodSetIs.method_set_is (t := go.GoType.PointerType io.fs.PathError.ty) go!"Unwrap"
  refine ⟨?_, ?_⟩
  · rw [h1]; try decide
  · rw [h2]; try simp [go.methodSetLookup]

/-- `(*PathError).Unwrap` returns its `Err` field. -/
theorem wp_pathError_Unwrap [os.Assumptions] (pe : Loc) (c : GoInterface) :
    {{ (structFieldRef io.fs.PathError go!"Err" pe ↦□ c : IProp GF) }}
      (App (Val #(methods (go.GoType.PointerType io.fs.PathError.ty) go!"Unwrap" #pe)) (Val #()))
    {{ RET #c; True }} := by
  wp_start as #Hc
  wp_auto
  iapply HΦ
  itrivial

/-- **The tree of `os.errnoPathErr err e`** at a target `Errno.Is` compares, with exact relations (see the file
header). -/
theorem pathErrno_walkTree [syscall.Assumptions] [os.Assumptions] (err : GoInterface) (e : w64) (he : e ≠ 0) (t : GoInterface) (ht : ErrnoIsTarget t)
    (xPe xEx xNE xUn : Loc) (Ie : Bool → Prop) (hIe : ∀ b, ErrnoIsPost e t xPe xEx xNE xUn b → Ie b) :
    errnoIsVars (GF := GF) xPe xEx xNE xUn ∗ os.errnoPathErr (GF := GF) err e ⊢
      _root_.Perennial.errors.errorWalkTree (GF := GF) (peS err e) (peI err e Ie) (peU err e) t := by
  obtain ⟨hEIs, hEU⟩ := errno_methods (GF := GF) (hG := hG)
  obtain ⟨hPIs, hPU⟩ := pathError_methods (GF := GF) (hG := hG)
  iintro ⟨#Hv, #Hp⟩
  iunfold os.errnoPathErr at Hp
  icases Hp with ⟨%pe, %op, %path, %herr, -, -, #Herr⟩
  subst herr
  have hen : errnoErr e = interface.mkOk syscall.Errno.ty #e := by
    unfold errnoErr; simp only [he, ↓reduceIte]
  have hne' : interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe ≠ interface.mkOk syscall.Errno.ty #e := by
    unfold interface.mkOk; intro h
    injection h with h
    injection h with h
    exact errno_ne_ptr _ h.symm
  have hne : interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe ≠ errnoErr e := by
    rw [hen]; exact hne'
  iintro !> %ii %hii
  rcases hii with hii | hii
  · -- the `*PathError`
    cases hii
    unfold _root_.Perennial.errors.errorWalkNode
    simp only [hPIs, hPU, reduceCtorEq, ↓reduceIte]
    isplitr
    · ipureintro
      exact ⟨fun _ => rfl, fun h => absurd h hne, fun h => absurd rfl h⟩
    iintro !> %Φ - HΦ
    wp_apply wp_pathError_Unwrap pe (errnoErr e) $$ [Herr]
    · iexact Herr
    iapply HΦ
    ipureintro
    exact ⟨Or.inr rfl, fun _ => rfl, fun h => absurd rfl h⟩
  · -- the `Errno`
    rw [hen] at hii
    cases hii
    unfold _root_.Perennial.errors.errorWalkNode
    simp only [hEIs, hEU, reduceCtorEq, ↓reduceIte]
    isplitr
    · iintro !> %Φ - HΦ
      wp_apply (wp_Errno_Is e t xPe xEx xNE xUn ht) $$ [Hv] as %b %hb
      · iexact Hv
      iapply HΦ
      ipureintro
      refine ⟨fun h => absurd h.symm hne', fun _ => hIe b hb,
        fun _ h => absurd (by rw [hen]) h⟩
    · ipureintro
      exact ⟨fun h => absurd h.symm hne', fun _ => rfl⟩

/-- The tree of an `Errno` alone, at a target `Errno.Is` compares: its `Is` answers some boolean, no `Unwrap`. -/
theorem errno_walkTree [syscall.Assumptions] (e : w64) (he : e ≠ 0) (t : GoInterface) (ht : ErrnoIsTarget t) (xPe xEx xNE xUn : Loc) :
    errnoIsVars (GF := GF) xPe xEx xNE xUn ⊢
      _root_.Perennial.errors.errorWalkTree (GF := GF) (· = errnoErr e) (fun _ _ => True) (fun _ cs => cs = []) t := by
  obtain ⟨hEIs, hEU⟩ := errno_methods (GF := GF) (hG := hG)
  have hen : errnoErr e = interface.mkOk syscall.Errno.ty #e := by
    unfold errnoErr; simp only [he, ↓reduceIte]
  iintro #Hv
  iintro !> %ii %hii
  rw [hen] at hii
  cases hii
  unfold _root_.Perennial.errors.errorWalkNode
  simp only [hEIs, hEU, reduceCtorEq, ↓reduceIte]
  isplitr
  · iintro !> %Φ - HΦ
    wp_apply (wp_Errno_Is e t xPe xEx xNE xUn ht) $$ [Hv] as %b -
    · iexact Hv
    iapply HΦ
    itrivial
  · ipureintro; trivial


end wps

end EtcdGrove
end Perennial
