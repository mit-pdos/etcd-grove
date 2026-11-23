/- Lean-first (no Rocq counterpart).

# `syscall.Errno.Is` and the error tree of an `Errno`

`Errno.Is(target)` (syscall_unix.go) is a `switch` comparing `target` with internal/oserror's `ErrPermission`,
`ErrExist`, `ErrNotExist` and `errors.ErrUnsupported` (four `errors.New` errors, `errors.newVar`): it answers
`e == ENOENT` at `oserror.ErrNotExist`, and `false` at any target that is none of the four (`wp_Errno_Is`).
Its comparisons step at any target whose dynamic type, if `*errorString`, holds a pointer (`ErrnoIsTarget`):
an interface `==` of values of different dynamic types is `false` (Perennial's `go_eq_interface`), so an `Errno`
target or another pointer type compares without a step of its own.

An `Errno` has an `Is` method and no `Unwrap`: `errno_errorWalkNode` is its node of an error tree, whose `Is`
answers as above.
-/
module

public import Proof.syscall.PkgInit
public import Proof.syscall.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.internal.oserror.Base
public import Perennial.Golang.Theory.TypeSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section defs
variable [GooseExts] [GoGlobalContext]

/-- An `*errors.errorString` at `x`, as an `error`. -/
abbrev esErr (x : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x

/-- A target `Errno.Is` compares without getting stuck: if it is an `*errorString`, it holds a pointer. -/
def ErrnoIsTarget (t : GoInterface) : Prop :=
  ∀ tii, t = interface.ok tii → tii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty →
    ∃ l : Loc, tii.v = #l

theorem errnoIsTarget_pointer (tii : GoInterfaceOk) (h : _root_.Perennial.errors.IsPointerError tii) :
    ErrnoIsTarget (interface.ok tii) := by
  obtain ⟨T, l, -, hl⟩ := h
  intro tii' ht _
  cases ht
  exact ⟨l, hl⟩

theorem errnoIsTarget_not_es (t : GoInterface)
    (h : ∀ tii, t = interface.ok tii → tii.ty ≠ go.GoType.PointerType _root_.Perennial.errors.errorString.ty) :
    ErrnoIsTarget t := by
  intro tii ht hty
  exact absurd hty (h tii ht)

/-- What `Errno(e).Is(t)` answers, given internal/oserror's `ErrNotExist` at `xNE` and the four errors the
`switch` compares with at `xPe`, `xEx`, `xNE`, `xUn`: `e == ENOENT` at `ErrNotExist`, `false` at none. -/
def ErrnoIsPost (e : w64) (t : GoInterface) (xPe xEx xNE xUn : Loc) (b : Bool) : Prop :=
  (t = esErr xNE → b = decide (e = W64 2)) ∧
  (t ≠ esErr xPe → t ≠ esErr xEx → t ≠ esErr xNE → t ≠ esErr xUn → b = false)

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The four errors `Errno.Is` compares with** (persistent): internal/oserror's `ErrPermission`, `ErrExist`,
`ErrNotExist` and `errors.ErrUnsupported` hold the `*errorString`s at `xPe`, `xEx`, `xNE`, `xUn`, whose messages
differ (`errors.errorString_ne`). -/
def errnoIsVars (xPe xEx xNE xUn : Loc) : IProp GF :=
  iprop(globalAddr _root_.Perennial.internal.oserror.ErrPermission ↦□ esErr xPe ∗
    globalAddr _root_.Perennial.internal.oserror.ErrExist ↦□ esErr xEx ∗
    globalAddr _root_.Perennial.internal.oserror.ErrNotExist ↦□ esErr xNE ∗
    globalAddr _root_.Perennial.errors.ErrUnsupported ↦□ esErr xUn ∗
    xPe.[errors.errorString, go!"s"] ↦□ go!"permission denied" ∗
    xEx.[errors.errorString, go!"s"] ↦□ go!"file already exists" ∗
    xNE.[errors.errorString, go!"s"] ↦□ go!"file does not exist" ∗
    xUn.[errors.errorString, go!"s"] ↦□ go!"unsupported operation")

instance errnoIsVars_persistent (xPe xEx xNE xUn : Loc) :
    Persistent (errnoIsVars (GF := GF) xPe xEx xNE xUn) := by
  unfold errnoIsVars; infer_instance

/-- internal/oserror's fact (as `internal.oserror.isInit_access`, without its package's `Assumptions`, which it
does not use). -/
theorem oserror_isInit :
    isPkgInit (PROP := IProp GF) pkg_id.internal.oserror ⊢ _root_.Perennial.internal.oserror.isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.oserror

/-- `syscall`'s initialization gives the four errors `Errno.Is` compares with. -/
theorem errnoIsVars_of_init [_root_.Perennial.errors.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.syscall ⊢ ∃ xPe xEx xNE xUn : Loc, errnoIsVars (GF := GF) xPe xEx xNE xUn := by
  iintro #Hs
  ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hose : isPkgInit (PROP := IProp GF) pkg_id.internal.oserror $$ []
  · iPkgInit
  ihave #Hun := _root_.Perennial.errors.errUnsupported_of_init $$ Herr
  ihave #Ho := oserror_isInit $$ Hose
  icases Ho with ⟨-, #VPe, #VEx, #VNE, -⟩
  iunfold _root_.Perennial.errors.newVar at VPe VEx VNE Hun
  icases VPe with ⟨%xPe, #OPe, #SPe, -⟩
  icases VEx with ⟨%xEx, #OEx, #SEx, -⟩
  icases VNE with ⟨%xNE, #ONE, #SNE, -⟩
  icases Hun with ⟨%xUn, #OUn, #SUn, -⟩
  iexists xPe, xEx, xNE, xUn
  iunfold errnoIsVars
  iframe #

/-- **`Errno(e).Is(t)`**: see `ErrnoIsPost`. -/
theorem wp_Errno_Is [syscall.Assumptions] (e : w64) (t : GoInterface) (xPe xEx xNE xUn : Loc)
    (ht : ErrnoIsTarget t) :
    errnoIsVars (GF := GF) xPe xEx xNE xUn ⊢
    {{ True }}
      (App (Val #(methods syscall.Errno.ty go!"Is" #e)) (Val #t))
    {{ (b : Bool), RET #b; ⌜ErrnoIsPost e t xPe xEx xNE xUn b⌝ }} := by
  iintro #Hv
  iunfold errnoIsVars at Hv
  icases Hv with ⟨#OPe, #OEx, #ONE, #OUn, #SPe, #SEx, #SNE, #SUn⟩
  ihave %h1 := _root_.Perennial.errors.errorString_ne xNE xPe _ _ (by decide) $$ SNE SPe
  ihave %h2 := _root_.Perennial.errors.errorString_ne xNE xEx _ _ (by decide) $$ SNE SEx
  iintro !> %Φ - HΦ
  wp_method_call
  wp_call
  rcases t with ⟨tty, tv⟩ | _
  · by_cases hty : tty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty
    · subst hty
      obtain ⟨l, rfl⟩ := ht _ rfl rfl
      have hes : ∀ y, GoInterface.ok ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #l⟩ = esErr y ↔
          l = y := by
        intro y
        constructor
        · intro h
          unfold esErr interface.mkOk at h
          injection h with h
          injection h with _ h
          exact go.intoVal_inj h
        · rintro rfl; rfl
      simp only [esErr, interface.mkOk]
      wp_auto
      wp_if_destruct
      · revert Hif; intro hPe
        repeat' (first | wp_if_destruct | wp_auto)
        all_goals
          iapply HΦ
          ipureintro
          exact ⟨fun h => absurd ((hes _).mp h) (fun h' => h1 (h'.symm.trans hPe)),
            fun h => absurd ((hes _).mpr hPe) h⟩
      revert Hif; intro hPe
      try wp_auto
      wp_if_destruct
      · revert Hif; intro hEx
        repeat' (first | wp_if_destruct | wp_auto)
        all_goals
          iapply HΦ
          ipureintro
          exact ⟨fun h => absurd ((hes _).mp h) (fun h' => h2 (h'.symm.trans hEx)),
            fun _ h => absurd ((hes _).mpr hEx) h⟩
      revert Hif; intro hEx
      try wp_auto
      wp_if_destruct
      · revert Hif; intro hNE
        try wp_auto
        iapply HΦ
        ipureintro
        exact ⟨fun _ => rfl, fun _ _ h => absurd ((hes _).mpr hNE) h⟩
      revert Hif; intro hNE
      try wp_auto
      wp_if_destruct
      · revert Hif; intro hUn
        repeat' (first | wp_if_destruct | wp_auto)
        all_goals
          iapply HΦ
          ipureintro
          exact ⟨fun h => absurd ((hes _).mp h) hNE, fun _ _ _ h => absurd ((hes _).mpr hUn) h⟩
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨fun h => absurd ((hes _).mp h) hNE, fun _ _ _ _ => rfl⟩
    · wp_auto
      simp only [hty, ↓reduceIte]
      wp_auto
      simp only [hty, ↓reduceIte]
      wp_auto
      simp only [hty, ↓reduceIte]
      wp_auto
      simp only [hty, ↓reduceIte]
      wp_auto
      iapply HΦ
      ipureintro
      refine ⟨fun h => ?_, fun _ _ _ _ => rfl⟩
      unfold esErr interface.mkOk at h
      injection h with h
      injection h with h
      exact absurd h hty
  · simp only [esErr, interface.mkOk]
    wp_auto
    iapply HΦ
    ipureintro
    refine ⟨fun h => ?_, fun _ _ _ _ => rfl⟩
    cases h

end wps

end EtcdGrove
end Perennial
