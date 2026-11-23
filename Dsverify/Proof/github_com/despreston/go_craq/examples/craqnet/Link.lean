/-
The craq kit's links (the lab's `Craq/Proof/Link.lean`, onto remote and Net): every proof applied
to its callees' results. The protocol's laws (`Protocol/`), the codec's laws (`CodecProof.lean`),
the store, node and coordinator specs, transport/netrpc's clients, the configuration messages over
Net's `net` specs, Net's `SetCodec`, remote's `Check`/`ServeClient`; then the kit's `Client`,
`Orch`, `Server`. What is not proved stays an argument: the hypothesis classes (instance
arguments: `LogHyp`, `RpcHttpAddr`, `RpcHttpDial`, `RpcHttpServe`) and the findings' premises (F1:
`removeNodeOk.spec`, F3: the nodes' `errOk`), which the statement takes.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ClientProof
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ServerProof
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitProof
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ModelProof
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Mains
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.All
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Simple
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Pure
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Commit
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.CodecProof
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Kv.New
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.All
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Svc
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Start
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.New
public import Net.Proof.net.rpc.Results
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.EtcdGrove.dsvcraq

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.github_com.despreston.go_craq Perennial.github_com.despreston.go_craq.examples.craqnet
open Perennial.github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : Perennial.github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions]
variable [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF] [rd : RpcHttpDial GF] [bvi : go.BasicIntoValInj] [NaInvG GF]

/-- The protocol's laws the node's proofs use. -/
theorem nodeLaws : NodeP.Laws (GF := GF) :=
  ⟨commit.wp_proof, read.wp_proof, tailTok_cvLb.wp_proof, tailTok_lb.wp_proof, cvLb_zero.wp_proof,
    cvLb_mono.wp_proof, valsElem_agree.wp_proof, covers_nil.wp_proof, roleHalf_agree.wp_proof,
    roleHalf_update.wp_proof, nlog_covers.wp_proof, nlog_covers_le.wp_proof, nlog_append.wp_proof,
    covers_mono.wp_proof, cvOf_append.wp_proof, cvOf_commit.wp_proof⟩

theorem wp_NewNodeClient : netrpc.wp_NewNodeClient.spec (GF := GF) (hG := hG) :=
  let L := craqCodecLaws (GF := GF) (hG := hG)
  netrpcP.wp_NewNodeClient L.enc_EmptyArgs L.enc_WriteArgs L.enc_CommitArgs L.enc_string
    L.enc_NodeMeta L.enc_PropagateRequest L.dec_EmptyReply L.dec_VersionResponse L.dec_Item
    L.dec_PropagateResponse

theorem factory : netrpc.factory.spec (GF := GF) (hG := hG) :=
  let L := craqCodecLaws (GF := GF) (hG := hG)
  netrpcP.factory L.enc_EmptyArgs L.enc_WriteArgs L.enc_CommitArgs L.enc_string
    L.enc_NodeMeta L.enc_PropagateRequest L.dec_EmptyReply L.dec_VersionResponse L.dec_Item
    L.dec_PropagateResponse

theorem wp_NewCoordinatorClient : netrpc.wp_NewCoordinatorClient.spec (GF := GF) (hG := hG) :=
  let L := craqCodecLaws (GF := GF) (hG := hG)
  netrpcP.wp_NewCoordinatorClient L.enc_string L.enc_ClientWriteArgs L.dec_NodeMeta
    L.dec_EmptyReply

theorem wp_awaitConf : awaitConf.spec (GF := GF) (hG := hG) :=
  examples.craqnet.wp_awaitConf net.Listen.wp_proof net.Listener.Accept.wp_proof
    net.Conn.Read.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof

theorem wp_configure [LogHyp GF] : configure.spec (GF := GF) (hG := hG) :=
  examples.craqnet.wp_configure net.Dial.wp_proof net.Conn.Write.wp_proof net.Conn.Read.wp_proof
    net.Conn.Close.wp_proof

/-- Every server machine (F1, F3: the findings' premises). -/
theorem wp_Server [LogHyp GF] [RpcHttpServe GF]
    (HRN : ∀ cfg : Cfg GF, removeNodeOk.spec cfg)
    (HE : ∀ (cfg : Cfg GF) (a : GoString),
      ⊢ net.rpc.errOk (nodeSpec (G := hG.goose_globalGS) cfg.γ cfg.chain a)) :
    Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof net.rpc.SetCodec.wp coordinator.wp_New coordinator.wp_Start
    (coordinator.coord_svc assign.wp_proof collect.wp_proof) factory kvp.wp_New node.wp_New
    (node.wp_Start nodeLaws) (node.node_svc nodeLaws) wp_NewCoordinatorClient wp_awaitConf HRN HE

theorem wp_Client [LogHyp GF] [ρ : RemoteGS] : Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof wp_awaitConf net.rpc.SetCodec.wp wp_NewNodeClient wp_NewCoordinatorClient
    Codec.wp_proof EtcdGrove.remote.wp_ServeClient

theorem wp_Orch [LogHyp GF] [ρ : RemoteGS] : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof wp_configure Model.wp_proof Codec.wp_proof Gen.wp_proof EtcdGrove.remote.wp_Check

end linked

end Perennial.EtcdGrove.dsvcraq
