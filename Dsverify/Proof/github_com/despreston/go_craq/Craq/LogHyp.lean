/-
**Hypothesis H6** (notes/dsv-craq.md, "Hypotheses"; `notes/perennial-changes.md`, 2026-11-23):
the `log` calls go-craq makes that Perennial's `log` model does not specify. Perennial trusts
`log.Printf` and `log.Println` on `fmt.ArgsWf` arguments only; go-craq's node logs through a
`*log.Logger` (`log.Default()`, its `Printf` and `Println`) and both the node and the coordinator
pass errors (Go calls their `Error()`) and values without formatting methods (`%+v`, `%#v`: no
method called). The specs are the lab's (`Harness/Proof/log.lean`, whose `log` model was its own),
with the arguments `argOk` allows. They are the class `LogHyp` (a `Prop`), taken as an instance by
the proofs that log, up to the kit's statement; never an axiom.
-/
module

public import Perennial.Proof.log
public import Perennial.Proof.fmt.Base
public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A `log` argument go-craq passes: `nil` or one `fmt` formats without a method (`fmt.ArgWf`), a
value of a type with neither `Error` nor `String`, or an error with an `Error()` method
(`errAny`). -/
def argOk (v : GoInterface) : IProp GF :=
  iprop(⌜∀ ii, v = interface.ok ii → fmt.ArgWf ii ∨
      (go.typeSetContains ii.ty go.error = false ∧ go.typeSetContains ii.ty fmt.Stringer.ty = false)⌝ ∨
    models_lab.errAny v)

instance argOk_persistent (v : GoInterface) : Persistent (argOk (GF := GF) v) := by
  unfold argOk; infer_instance

end defs

/-- **H6** (the file header). -/
class LogHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] [log.Assumptions] : Prop where
  /-- `log.Default()` returns a logger. -/
  wp_Default :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log }}
      (App (Val (@! log.Default)) (Val #()))
    {{ (l : Loc), RET #l; True }}
  /-- `l.Printf(format, args...)` on any `*Logger`. -/
  wp_Logger_Printf : ∀ (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface)
      (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
        (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}
  /-- `l.Println(args...)` on any `*Logger`. -/
  wp_Logger_Println : ∀ (l : Loc) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}
  /-- `log.Printf(format, args...)` on arguments `argOk` allows. -/
  wp_Printf : ∀ (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (App (Val (@! log.Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end github_com.despreston.go_craq

end Perennial
