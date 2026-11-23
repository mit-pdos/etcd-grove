/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecutorMain.lean`, run `rabia-r1wake-1`.)

`Consensus.Executor.wp_proof`: the main loop with `decideSlot`'s proof. -/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecDecide
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecutorFinal

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS] [math.rand.Hyps GF]

theorem Consensus.Executor.wp_proof (D : ExDeps (GF := GF)) : Consensus.Executor.spec (GF := GF) :=
  Consensus.Executor.wp_proof_of D
    (fun γ cf k γl γc ch c σ x hk hx => wp_decideSlot_proof (cf := cf) D γ k γl γc ch c hk σ x hx)

end proof

end Perennial.rabia.roles.server.layers.consensus
