/-
Package variables initialized by `errors.New` (item 8, package initialization, 2026-10-17).

`errorsNewVarInit init X msg`: running `init` (the untranslated initializer `X.init` of a
package variable `var X = errors.New(msg)`, an axiom of the translation) does what Go's
`errors.New(msg)` and the store into `X` do (`context.wp_New_errorString`): `X`'s cell (owned, as
`wp_GlobalAlloc` gives it) holds a fresh `*errorString` whose `Error()` returns `msg`. A
package's axiom `<pkg>.<X>_init : errorsNewVarInit X.init X msg` states it of one variable; each
is checked against its Go line.

`ErrorStringLeaf`: the method set of `*errorString` (Go's `errors` package defines only `Error`)
has no `As`, `Unwrap` or `Is` method. A fact about the method sets, which the semantics leaves
uninterpreted: a premise, as Perennial's `context.ErrorStringIsError`.
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The method set of `*errors.errorString` has no `As`, `Unwrap` or `Is` method (Go's `errors`
package gives it only `Error`). -/
class ErrorStringLeaf [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  leaf : ∀ v : val,
    _root_.Perennial.errors.isLeafError
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, v⟩
  noIs : methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !! go!"Is" ≠
    some (go.Signature [go.error] false [go.bool])

/-- An `errors.New` error (a `*errorString`) is a leaf pointer error without an `Is` method. -/
theorem errorString_leaf [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] [ErrorStringLeaf]
    (x : Loc) :
    _root_.Perennial.errors.IsPointerError
        ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ ∧
      _root_.Perennial.errors.isLeafError
        ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ ∧
      methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !! go!"Is" ≠
        some (go.Signature [go.error] false [go.bool]) :=
  ⟨⟨_, _, rfl, rfl⟩, ErrorStringLeaf.leaf _, ErrorStringLeaf.noIs⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `init` runs `X = errors.New(msg)`: `X`'s cell, owned, holds a fresh `*errorString` whose
`Error()` returns `msg`. -/
abbrev errorsNewVarInit (init : val) (X msg : GoString) : Prop :=
  {{ (True : IProp GF) }} (App (Val init) (Val #()))
  {{ RET #(); ∃ x : Loc,
      globalAddr X ↦ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∗
      □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }} }}

/-- The `Error()` of an error whose message is known (`errors.New`'s, `context.wp_New_errorString`)
returns some string, as a triple (the form of the server's `errMsgOk`, the lease's and auth's
error-variable facts). -/
theorem errorMsg_triple (ty : go.GoType) (v : val) (msg : GoString) :
    iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods ty go!"Error" v)) (Val #())) {{ Φ }}) ⊢
    {{ (True : IProp GF) }} (App (Val #(methods ty go!"Error" v)) (Val #()))
      {{ (m : GoString), RET #m; True }} := by
  iintro #H %Φ !> - HΦ
  iapply H
  inext
  iapply HΦ
  itrivial

/-- **`X` holds an `errors.New(msg)` error** (persistent; a package fact): a fixed `*errorString`
whose `Error()` returns `msg`. What `errorsNewVarInit` gives, made persistent. -/
def errorsNewVar (X msg : GoString) : IProp GF :=
  iprop(∃ x : Loc,
    globalAddr X ↦□ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
        go!"Error" #x)) (Val #())) {{ Φ }})

instance errorsNewVar_persistent (X msg : GoString) : Persistent (errorsNewVar (GF := GF) X msg) := by
  unfold errorsNewVar; infer_instance

/-- `errorsNewVar` of each `(X, msg)` of a list. -/
def errorsNewVars : List (GoString × GoString) → IProp GF
  | [] => iprop(True)
  | (X, m) :: l => iprop(errorsNewVar X m ∗ errorsNewVars l)

instance errorsNewVars_persistent (l : List (GoString × GoString)) :
    Persistent (errorsNewVars (GF := GF) l) := by
  induction l with
  | nil => unfold errorsNewVars; infer_instance
  | cons p l ih => obtain ⟨X, m⟩ := p; unfold errorsNewVars; infer_instance

theorem errorsNewVars_mem {l : List (GoString × GoString)} {X m : GoString} (h : (X, m) ∈ l) :
    errorsNewVars (GF := GF) l ⊢ errorsNewVar X m := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨Y, n⟩ := p
    unfold errorsNewVars
    rcases List.mem_cons.1 h with h | h
    · cases h; exact sep_elim_left
    · exact sep_elim_right.trans (ih h)

end defs

end EtcdGrove
end Perennial
