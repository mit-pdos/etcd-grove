/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/NewClient.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.NewClient`'s proof over its callees' specs (the layout's `Proof/<pkg>/<Fn>.lean`): see
`NewClientBody.lean` (`swift.handler.NewClient.wp_proofI`). It rests on the change log C6 record
(`swift.handler.ClientPkgFacts`, a marked hypothesis: the swift package's state) and on the
law `sp.clientSeq_pos` (change log C13, HUB-REQUEST 10). Linked in `Proof/client/Link.lean`
(`swift.wp_NewClient`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.NewClientBody
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions] [net.Assumptions] [net.FieldAssumptions]
  [rpc.Assumptions] [replica.defs.Assumptions]

theorem swift.NewClient.wp_proof (facts : swift.handler.ClientPkgFacts)
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_initCs : swift.rd.initCs.specI (hG := hG))
    (wp_reg : swift.rd.RegisterRPCTable.specI (hG := hG))
    (wp_hm : swift.handler.handleMsgs.specI (hG := hG))
    (wp_maj : replica.quorum.NewMajorityOf.specI (hG := hG))
    (wp_tq : replica.quorum.NewThreeQuartersOf.specI (hG := hG)) :
    swift.NewClient.spec (hG := hG) :=
  swift.handler.NewClient.wp_proofI facts wp_Println wp_initCs wp_reg wp_hm wp_maj wp_tq

end proof

end Perennial.github_com.imdea_software.swiftpaxos
