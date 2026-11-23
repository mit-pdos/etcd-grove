/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/dlog/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`dlog`'s logger as the other packages use it: the deployment's loggers are non-verbose
(`&dlog.Logger{}`: `kit.go`'s `serve` and `connect`), whose methods print nothing and return
(`Fatal` included).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `l` is a non-verbose logger with no log (persistent): `&dlog.Logger{}`. -/
def dlog.quiet (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ l ↦□ (dlog.Logger.mk null false))

instance dlog.quiet_persistent (l : Loc) : Persistent (dlog.quiet (GF := GF) l) := by
  unfold dlog.quiet; infer_instance

end defs

end Perennial.github_com.imdea_software.swiftpaxos
