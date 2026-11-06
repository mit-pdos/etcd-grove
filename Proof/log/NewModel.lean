/-
`log.New` (names-only in Perennial's `log`) as the package initializers that call it need it: raft's
(`defaultLogger`, `discardLogger`) and bbolt's (`discardLogger`). Moved out of raft's `Init.lean`
(2026-11-03) so that bbolt's initializer can use it without raft.

The class `log.NewModel` says that the name `log.New` stands for `log.New.model`, a function that
returns a new `*Logger` (what raft and bbolt need of it; the Go function allocates and initializes a
`Logger`, without failing).
-/
module

public import Perennial.Code.log
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.log

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace log

/-- A model of `log.New(out, prefix, flag)`: a fresh pointer. `Logger` is an opaque type in
Perennial's `log` (no layout, so no typed allocation), and raft and bbolt only store the pointer
(in their `DefaultLogger`s), so the model allocates an untyped cell: what Go returns is a fresh,
non-`nil` `*Logger`. -/
def New.model [GooseExts] [GoGlobalContext] : val :=
  λ: "out" "prefix" "flag", Alloc (Val #())

/-- The name `log.New` stands for `New.model`: an assumption about the semantics, like the
`FuncUnfold` fields of a package's `Assumptions` (Perennial translates `log` without
`New`). -/
class NewModel [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  New_unfold : FuncUnfold log.New [] New.model

attribute [instance] NewModel.New_unfold

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions] [NewModel]

theorem wp_New (out : GoInterface) (pfx : GoString) (flag : w64) :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! log.New)) (Val #out)) (Val #pfx)) (Val #flag))
    {{ (l : Loc), RET #l; True }} := by
  wp_start
  wp_apply (wp_alloc_untyped _ (isPanic_intoVal _)) as %l Hl
  iapply HΦ
  itrivial

end wps

end log

end Perennial
