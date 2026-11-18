/-
**`errors.New`'s message cell** (D19k, 2026-10-18): what tells two `errors.New` variables apart.

`errors.New(msg)` allocates a fresh `errorString{s: msg}` and nothing writes its `s` field again,
so the field holds `msg` for good (`errStrCell`; Perennial's `context.wp_New_errorString` persists
the cell in its proof and drops it from its postcondition: `wp_New_errorString_cell` here is the
same proof keeping it, a candidate Perennial change). Two variables whose cells hold different
messages hold different pointers (`errVarApart_of`): two `↦□` at one cell agree. The packages'
facts carry the cells of the variables a proof must tell apart (`errVarCell`): the server's
`applyEntryNormal` needs the backend's errors told apart from `ErrNoSpace` (the apply package's
`applyErrVars`), so that `errors.Is(ar.Err, ErrNoSpace)` is `false` (D19k).

`errorsNewVarInitC init X msg`: `errorsNewVarInit`'s statement with the cell, the form of the
`errorsNewVarsInit` axioms (`etcdserver/errors`, bbolt's `errors`): still what Go's
`var X = errors.New(msg)` does.
-/
module

public import Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The `errorString` at `x` holds `msg`** (persistent): its `s` field, which only
`errors.New` writes. -/
def errStrCell (x : Loc) (msg : GoString) : IProp GF :=
  iprop(x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ msg)

/-- **`X` holds an `errors.New(msg)` error with its cell** (persistent; a package fact). -/
def errVarCell (X msg : GoString) : IProp GF :=
  iprop(∃ x : Loc,
    globalAddr X ↦□ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∗
    errStrCell x msg)

/-- `errVarCell` of each `(X, msg)` of a list. -/
def errVarCells : List (GoString × GoString) → IProp GF
  | [] => iprop(True)
  | (X, m) :: l => iprop(errVarCell X m ∗ errVarCells l)

end defs

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

end wp

end EtcdGrove
end Perennial
