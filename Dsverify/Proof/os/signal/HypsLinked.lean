/-
`os/signal`'s environment assumption as `Notify`'s proof (the linking tier, CLAUDE.md "Import
tiers"): `NotifyQuiet.wp_proof` is the field of the class `NoSignals sigs` (`Spec.lean`) that states
`NotifyQuiet.spec sigs`. A proof file takes the class as an instance argument and uses its field; only
linking modules see this.
-/
module

public import Dsverify.Proof.os.signal.Spec

@[expose] public section

noncomputable section

namespace Perennial.os.signal

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

theorem NotifyQuiet.wp_proof (sigs : List os.Signal) [h : NoSignals sigs GF] :
    NotifyQuiet.spec (GF := GF) sigs :=
  h.notifyQuiet

end proof

end Perennial.os.signal
