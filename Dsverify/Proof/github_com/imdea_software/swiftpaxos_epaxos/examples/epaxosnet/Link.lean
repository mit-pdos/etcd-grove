/-
The EPaxos kit's links (craq's `examples/craqnet/Link.lean`, paxos's `Linked.lean`): every proof of
the kit applied to its callees' results. The master package's (`master/Link.lean`: `master.wp_New`,
`master.wp_Run`, the receivers' bodies), the epaxos package's (`epaxos/Link.lean`: `wp_New`;
`epaxos/Rpc.lean`: the replica's `BeTheLeader`/`Ping`), the RPC layer's (`NetRpc/`: the clients'
calls from Net's `Client.Call` and the codec's laws, the receivers from the server codec's laws),
the wire's (`wire/Link.lean`), dlog's, Net's (`Listen`, `DialTimeout`, `Conn.*`, net/rpc's
`SetCodec`, `Client.Call`, `Client.Close`), bufio's, `time.Sleep`, primitive's `RandomUint64`, and
remote's `ServeClient`/`Check`; then the kit's `Server`, `Client`, `Orch`. What is not proved stays
an instance argument: net/rpc over HTTP (`RpcHttpAddr`, `RpcHttpHyp`, `Interface/RpcHttpHyps.lean`)
and gods' treemap (`StateTreemap`, `Interface/Treemap.lean`), which the statement takes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServerProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServeReplica
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ServeHelpers
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Register
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ClientProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.OpProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.KitProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ModelProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Rpc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Calls
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Bindings
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.CodecProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.CodecSrvProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Results
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Misc.Dlog
public import Net.Proof.net.rpc.Results
public import Net.Proof.net.Listen
public import Net.Proof.net.DialTimeout
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Proof.bufio.NewWriter
public import Proof.bufio.NewWriterSize
public import Proof.bufio.NewWriterSizeRep
public import Proof.bufio.NewReaderOk
public import Proof.bufio.NewReaderSize
public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Flush
public import Perennial.Proof.time.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.EtcdGrove.dsvepaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.github_com.imdea_software.swiftpaxos_epaxos
  Perennial.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
open Perennial.github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : examples.epaxosnet.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [epaxos.Assumptions] [log.Assumptions] [net.http.Assumptions]
variable [io.Assumptions] [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
variable [replica.Assumptions] [replica.defs.Assumptions] [bufio.Assumptions]
variable [bvi : go.BasicIntoValInj] [NaInvG GF] [TH : StateTreemap GF]

/-- `nodeConfig`, over `digit`. -/
theorem wp_nodeConfig : nodeConfig.spec (GF := GF) (hG := hG) :=
  nodeConfig.wp_proof digit.wp_proof

/-- The clients' calls (`NetRpc/Calls.lean`), from Net's `Client.Call` and the codec's laws. -/
theorem wp_btlCall : btlCall.spec (GF := GF) :=
  btlCall_holds epCodecLaws net.rpc.Client.Call.wp

theorem wp_pingCall : pingCall.spec (GF := GF) :=
  pingCall_holds epCodecLaws net.rpc.Client.Call.wp

theorem wp_registerCall : registerCall.spec (GF := GF) :=
  registerCall_holds epCodecLaws net.rpc.Client.Call.wp

/-- The master's receiver (`NetRpc/Bindings.lean`), from its method bodies. -/
theorem wp_masterRcv (γ : EpNames) : masterRcv.spec (GF := GF) γ (isMaster γ) :=
  masterRcv_holds epSrvCodecLaws epArgFacts epDecLen γ (isMaster γ) (master.wp_Register γ)
    (master.wp_GetLeader γ) (master.wp_GetReplicaList γ)

/-- A replica's receiver, from its `BeTheLeader`/`Ping` (`epaxos/Rpc.lean`). -/
theorem wp_replicaRcv (γ : EpNames) (i : Nat) : replicaRcv.spec (isReplica (GF := GF) γ i) :=
  replicaRcv_holds epSrvCodecLaws (isReplica γ i)
    (replicaBtl_holds dlog.Logger.Println.spec_holds γ i) (replicaPing_holds γ i)

section rpcHttp
variable [RpcHttpAddr GF] [RpcHttpHyp GF]

theorem wp_register : register.spec (GF := GF) (hG := hG) :=
  register.wp_proof wp_registerCall net.rpc.Client.Close.wp

theorem wp_serveReplica : serveReplica.spec (GF := GF) (hG := hG) :=
  serveReplica.wp_proof isReplica net.rpc.SetCodec.wp wp_nodeConfig host.wp_proof itoa.wp_proof
    wp_register wp_New wp_replicaRcv net.Listen.wp_proof

/-- Every server machine. -/
theorem wp_Server : Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof net.rpc.SetCodec.wp wp_nodeConfig master.wp_New
    (fun γ W => master.wp_Run wp_btlCall wp_pingCall γ W (wp_masterRcv γ)) wp_serveReplica

end rpcHttp

/-- `Op`, over the wire's, Net's and bufio's proofs. -/
theorem wp_Op : examples.epaxosnet.Op.spec (GF := GF) (hG := hG) :=
  Op.wp_proof state.NIL.wp_proof replica.defs.Propose.Marshal.wp_proof
    replica.defs.ProposeReplyTS.Unmarshal.wp_proof net.DialTimeout.wp_proof net.Conn.Read.wp_proof
    net.Conn.Write.wp_proof net.Conn.Close.wp_proof
    (EtcdGrove.bufio.NewWriter.wp_proof
      (EtcdGrove.bufio.NewWriterSize.wp_proof EtcdGrove.bufio.NewWriterSize.wp_proofRep))
    (EtcdGrove.bufio.NewReader.wp_proofOk
      (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE))
    (EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof)
    EtcdGrove.bufio.Writer.Flush.wp_proof

variable [ρ : RemoteGS]

/-- Every client machine. -/
theorem wp_Client : Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof wp_Op ServerAddrs.wp_proof Codec.wp_proof time.wp_Sleep time.wp_Now time.wp_Since
    EtcdGrove.remote.wp_ServeClient

/-- The orchestrator. -/
theorem wp_Orch : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof Model.wp_proof Codec.wp_proof
    (Gen.wp_proof github_com.goose_lang.primitive.wp_RandomUint64) EtcdGrove.remote.wp_Check

end linked

end Perennial.EtcdGrove.dsvepaxos
