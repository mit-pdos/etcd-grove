/-
The master package closed: `master.New`, the receivers' method bodies (`Register`, `GetLeader`,
`GetReplicaList`) and `Master.Run`'s spec from the parts (`run()`, the `defs` helpers, dlog's
logger, Net's `Listen`). Left as hypotheses: the clients' calls `btlCall.spec`, `pingCall.spec`
and the receiver `masterRcv.spec` (`NetRpc/`, proved by the RPC layer), and net/rpc over HTTP
(`[RpcHttpAddr GF] [RpcHttpHyp GF]`, `Interface/RpcHttpHyps.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Register
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.GetLeader
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.GetReplicaList
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.BtlReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.RunLoop
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Run
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Misc.Dlog
public import Net.Proof.net.Listen

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [go.BasicIntoValInj]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions] [epaxos.Assumptions]

theorem master.wp_New : master.New.specM (GF := GF) := master.New.wp_proof

theorem master.wp_Register (γ : EpNames) : masterRegister.spec (GF := GF) γ (isMaster γ) :=
  masterRegister.wp_proof γ

theorem master.wp_GetLeader (γ : EpNames) : masterGetLeader.spec (GF := GF) (isMaster γ) :=
  masterGetLeader.wp_proof γ

theorem master.wp_GetReplicaList (γ : EpNames) :
    masterGetReplicaList.spec (GF := GF) (isMaster γ) :=
  masterGetReplicaList.wp_proof dlog.Logger.Printf.spec_holds γ

variable [log.Assumptions] [net.http.Assumptions] [RA : RpcHttpAddr GF] [RH : RpcHttpHyp GF]

theorem master.wp_run (hBtl : btlCall.spec (GF := GF)) (hPing : pingCall.spec (GF := GF))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) : Master.run.specM (GF := GF) γ W :=
  Master.run.wp_proof dlog.Logger.Printf.spec_holds dlog.Logger.Fatal.spec_holds
    replica.defs.NewBeTheLeaderReply.wp_proof replica.defs.UpdateBeTheLeaderReply.wp_proof
    hBtl hPing γ W

/-- `Master.Run`'s spec, from the master package's proofs; the RPC layer's call and receiver
specs and net/rpc over HTTP (`RpcHttpHyp`) are its premises. -/
theorem master.wp_Run (hBtl : btlCall.spec (GF := GF)) (hPing : pingCall.spec (GF := GF))
    (γ : EpNames) (W : net.rpc.RpcWorld GF) (hRcv : masterRcv.spec (GF := GF) γ (isMaster γ)) :
    Master.Run.specM (GF := GF) γ W :=
  Master.Run.wp_proof dlog.Logger.Printf.spec_holds dlog.Logger.Fatal.spec_holds
    net.Listen.wp_proof γ W hRcv (master.wp_run hBtl hPing γ W)

end link

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
