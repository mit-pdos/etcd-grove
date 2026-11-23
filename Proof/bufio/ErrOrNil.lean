/-
An error result, as the specs of writers and of the encoding/json model's `Encoder` state it: `nil`,
or an error with some message. Moved from `Dsverify`'s vr kit (`Spec/jsonlib.lean`, from the lab's
`Harness/Proof/bufio/Defs.lean`, master 915f964) so that the kits use the main tree's
(mit-pdos/etcd-grove#24). Definitions only. Lean-first (no Rocq counterpart).
-/
module

public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace bufio

/-- A non-nil error of a pointer type holds a pointer (true of every error Go code makes; what
comparing it with an `errors.New` error needs). -/
def errWf [GooseExts] [GoGlobalContext] (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → ∀ T : go.GoType, e.ty = go.GoType.PointerType T →
    ∃ l : Loc, e.v = #l

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- An error result: `nil`, or an error with some message (and `errWf`). -/
def errOrNil (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (models_lab.errAny err ∗ ⌜errWf err⌝))

instance errOrNil_persistent (err : GoInterface) : Persistent (errOrNil (GF := GF) err) := by
  unfold errOrNil; infer_instance

end defs

end bufio
end Perennial
