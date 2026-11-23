/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/MsgHandlerFinal.lean`, run `rabia-r1wake-1`.)

`Consensus.MsgHandler.wp_proof`: the loop with the per-message proof. -/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Handler
public import Dsverify.Proof.rabia.roles.server.layers.consensus.MsgHandler

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
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS]

theorem Consensus.MsgHandler.wp_proof (hGID : Slot.GetIsDone.spec (GF := GF))
    (hGRD : Slot.GetHasRecvDec.spec (GF := GF)) (hSRD : Slot.SetHasRecvDec.spec (GF := GF))
    (hHEM : Slot.HasEnoughMsg.spec (GF := GF)) (hPRP : Slot.PutRecvProposals.spec (GF := GF))
    (hPBC : Slot.PutRecvBCMsgs.spec (GF := GF)) (hPush : heapPush.spec (GF := GF))
    (hMajT : Slot.RecvProposalsMajT.spec (GF := GF))
    (hMajV : Slot.RecvProposalsMajV.spec (GF := GF)) :
    Consensus.MsgHandler.spec (GF := GF) :=
  Consensus.MsgHandler.wp_proof_of
    (fun γ cf k γl γc ch c v m X j l hX hc hl hty =>
      wp_binConMsgHandling (cf := cf) hGID hGRD hSRD hHEM hPRP hPBC γ k γl γc ch c v m X j l hX hc hl
        hty)
    hPush hHEM hMajT hMajV

end proof

end Perennial.rabia.roles.server.layers.consensus
