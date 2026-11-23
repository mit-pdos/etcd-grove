/-
(The lab's `log.wp_Println`, `Harness/Proof/log.lean`, run `rabia-r1wake-1`.) `log.Println`'s spec
the rabia kit uses (`send` logs the configuration), proved in `Println.lean` from Perennial's
trusted model of `log` (`Perennial/TrustedCode/log.lean`: `Println.impl` does nothing; until #24
the spec was the field of a hypothesis class `log.Hyps`, a premise of the kit's statement).

What Go's `log.Println(args...)` does, as far as the program can tell: it writes a line to the
standard logger's output (outside the model) and returns; it reads its arguments' slice. As for
Perennial's `log.Printf.spec`, the arguments must be of predeclared basic types or named integer
types without formatting methods (`fmt.ArgsWf`): Go formats them as `fmt.Sprintln` does, calling
the `Error()`/`String()` methods of arguments that have them, which the model does not.
-/
module

public import Perennial.Proof.log.Base
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `log.Println(args...)`: returns, its arguments' slice kept. -/
abbrev log.Println.spec : Prop :=
  ∀ (arg : GoSlice) (xs : List GoInterface) (dq : DFrac), fmt.ArgsWf xs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end spec

end Perennial
