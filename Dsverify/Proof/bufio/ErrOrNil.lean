/-
`bufio.errWf`, `bufio.errOrNil` (the lab's `Harness/Proof/bufio/Defs.lean`): an error result, `nil`
or an error with some message (`models_lab.errAny`) of a pointer type holding a pointer. One copy
for the part's kits (swiftpaxos's `lib/Bufio.lean`, vr's hubs); the main tree's
`Proof/bufio/ErrOrNil.lean` (zeldovich's J1, `prove-ps2-jsonlean`) has the same two definitions:
when it lands, this file goes and its users import that one.
-/
module

public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace bufio

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A non-nil error of a pointer type holds a pointer (true of every error Go code makes; what
comparing it with an `errors.New` error needs). -/
def errWf [GooseExts] [GoGlobalContext] (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → ∀ T : go.GoType, e.ty = go.GoType.PointerType T →
    ∃ l : Loc, e.v = #l

/-- An error result: `nil`, or an error with some message (and `errWf`). -/
def errOrNil (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (models_lab.errAny err ∗ ⌜errWf err⌝))

instance errOrNil_persistent (err : GoInterface) : Persistent (errOrNil (GF := GF) err) := by
  unfold errOrNil; infer_instance

end defs

end bufio

end Perennial
