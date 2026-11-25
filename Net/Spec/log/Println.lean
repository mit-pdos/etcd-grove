/-
`log.Println(args...)`'s spec, as Perennial's `log.Printf.spec` (`Perennial/Spec/log/Printf.lean`):
it returns, the output not modelled (Perennial's trusted model, `TrustedCode/log.lean`, does
nothing), for arguments for which Go calls no formatting method (`fmt.ArgsWf`). Perennial states
`Printf`'s spec but not `Println`'s (`notes/perennial-changes.md`); proved in
`Net/Proof/log/Println.lean`.
-/
module

public import Perennial.Proof.log.Base
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

/-- See the file header. -/
abbrev log.Println.spec : Prop :=
  ∀ (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
  fmt.ArgsWf xs →
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }}

end spec

end Perennial
