/-
`os/signal`'s hypotheses as its functions' proofs (the linking tier, CLAUDE.md "Import tiers"): each
`<F>.wp_proof` is the field of the hypothesis class (`Spec.lean`) that states `<F>.spec`. A proof
file takes the class as an instance argument and uses its fields; only linking modules see these.
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

theorem Notify.wp_proof [h : Hyps GF] : Notify.spec (GF := GF) := h.Notify
theorem NotifyQuiet.wp_proof [h : NoSignals GF] : NotifyQuiet.spec (GF := GF) := h.notifyQuiet
theorem Stop.wp_proof [h : Hyps GF] : Stop.spec (GF := GF) := h.Stop

end proof

end Perennial.os.signal
