/-
The vocabulary of the future `log/slog` hypotheses (notes/dsv-vr.md, "Hypotheses"): what the vr
hubs mention of `log/slog`, from the lab's model (`Harness/Proof/log/slog.lean`, lab master 915f964).
**Definitions only**: the specs (`New.spec`, `Logger.{Debug,Info,Warn,Error}.spec`, `Debug.spec`)
will be hypotheses stated over these names.

* `isLogger l` (persistent): `l` is a `*Logger` whose handler is fixed for good (what the lab's
  `New` returned and its logging methods took).
-/
module

public import Dsverify.Proof.log.slog.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace log.slog

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.slog.Assumptions]

/-- The `*Logger` `l`, its handler fixed for good (persistent). -/
def isLogger (l : Loc) : IProp GF :=
  iprop(∃ h : GoInterface, structFieldRef log.slog.Logger go!"handler" l ↦□ h)

instance isLogger_persistent (l : Loc) : Persistent (isLogger (GF := GF) l) := by
  unfold isLogger; infer_instance

end defs

end log.slog

end Perennial
