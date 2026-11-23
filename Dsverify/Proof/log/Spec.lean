/-
(The lab's `log.wp_Println`, `Harness/Proof/log.lean`, run `rabia-r1wake-1`.) `log.Println`'s spec
the rabia kit uses (`send` logs the configuration), as a **hypothesis** (notes/dsv-rabia.md, "The
hypotheses"): Perennial's model of `log` has `Println` names only, with no spec, so the spec is the
field of the class `Hyps` (a `Prop`), which every theorem that calls it takes as an instance
argument, up to the kit's closed statement.

What Go's `log.Println(args...)` does, as far as the program can tell: it writes a line to the
standard logger's output (outside the model) and returns; it reads its arguments' slice.
-/
module

public import Perennial.Proof.log.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `log.Println(args...)`: returns, its arguments' slice kept. -/
abbrev log.Println.spec : Prop :=
  ∀ (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end spec

/-- **The hypothesis** (the header). -/
class log.Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where
  Println : log.Println.spec (GF := GF)

end Perennial
