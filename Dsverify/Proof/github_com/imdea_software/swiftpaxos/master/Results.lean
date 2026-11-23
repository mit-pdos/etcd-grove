/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The master group's results, linked over its proofs. The callees in other groups are taken as
hypotheses, through their specs: `dlog`'s `Printf`/`Fatal` (frozen, `Spec/dlog/`) and
`defs.NewBeTheLeaderReply` (frozen, `Spec/defs/`); the receiver is proved over the generated
codec (`master/Rcvr.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Rcvr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.RunLoop
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Methods
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Register
public import Net.Proof.net.rpc.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [net.Assumptions] [replica.defs.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

theorem master.wp_New : master.New.spec := master.New.wp_proof

/-- `Run`, linked: its receiver is the generated codec's (`master.rcvr.wp_proof`, over
`swiftSrvCodecLaws`). -/
theorem master.Master.wp_Run
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_NBR : replica.defs.NewBeTheLeaderReply.spec) :
    master.Master.Run.spec :=
  master.Master.Run.wp_proof wp_Printf wp_Fatal (master.Master.run.wp_proof wp_Printf wp_Fatal wp_NBR
    net.rpc.Client.Call.wp)
    (master.rcvr.wp_proof master.Master.GetLeader.wp_proof
      (master.Master.GetReplicaList.wp_proof wp_Printf) (master.Master.Register.wp_proof wp_Printf))

end link

end Perennial.github_com.imdea_software.swiftpaxos
