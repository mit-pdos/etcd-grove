/-
The craq kit's links (the lab's `Craq/Proof/Link.lean`, onto remote and Net): every proof applied
to its callees' results. The protocol's laws (`Protocol/`), the codec's laws (`CodecProof.lean`),
the store, node and coordinator specs, transport/netrpc's clients, the configuration messages over
Net's `net` specs, Net's `SetCodec`, remote's `Check`/`ServeClient`; then the kit's `Client`,
`Orch`, `Server`; net/rpc's client over HTTP (`DialHTTP`) is Net's (models-rpc-http's
`net.rpc.DialHTTP.wp`, in `RpcClientSpecs`, over Perennial's proofs of `strings.Cut`/`TrimLeft`),
and the package-level `rpc.RegisterName` is Net's
(`net.rpc.RegisterName.wp`). What is not proved stays an argument: the hypothesis
classes (instance arguments: `LogHyp`, `RpcHttpServe`, the server side), which the statement takes
(F1, RemoveNode's obligation: `cnewArg_RemoveNode`; F3, the nodes' `errOk`: `nodeSpec_errOk`).
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
variable [bvi : go.BasicIntoValInj] [NaInvG GF]

/-- Net's net/rpc client specs, for the kit's rpc clients (`Craq/Hyps.lean`'s `RpcClientSpecs`):
`Client.Call`, `Client.Close`, and models-rpc-http's `DialHTTP` (over `DialHTTPPath` and net/http's
`ReadResponse`, with Perennial's `strings.Cut`/`TrimLeft`). -/
instance rpcClientSpecs : RpcClientSpecs GF :=
  ⟨net.rpc.Client.Call.wp, net.rpc.Client.Close.wp,
    net.rpc.DialHTTP.wp⟩

/-- The protocol's laws the node's proofs use. -/
theorem nodeLaws : NodeP.Laws (GF := GF) :=
  ⟨commit.holds, read.holds, tailTok_cvLb.holds, tailTok_lb.holds, cvLb_zero.holds,
    cvLb_mono.holds, valsElem_agree.holds, covers_nil.holds, roleHalf_agree.holds,
    roleHalf_update.holds, nlog_covers.holds, nlog_covers_le.holds, nlog_append.holds,
    covers_mono.holds, cvOf_append.holds, cvOf_commit.holds⟩

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

/-- Every server machine (F1 discharged, `cnewArg_RemoveNode`; F3 discharged, `nodeSpec_errOk`). -/
theorem wp_Server [LogHyp GF] [RpcHttpServe GF] :
    Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof net.rpc.RegisterName.wp net.rpc.SetCodec.wp coordinator.wp_New coordinator.wp_Start
    (coordinator.coord_svc assign.holds collect.holds) factory kvp.wp_New node.wp_New
    (node.wp_Start nodeLaws) (node.node_svc nodeLaws) wp_NewCoordinatorClient wp_awaitConf
    (fun cfg a => nodeSpec_errOk cfg.γ cfg.chain a)

theorem wp_Client [LogHyp GF] [ρ : RemoteGS] : Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof wp_awaitConf net.rpc.SetCodec.wp wp_NewNodeClient wp_NewCoordinatorClient
    Codec.wp_proof EtcdGrove.remote.wp_ServeClient

theorem wp_Orch [LogHyp GF] [ρ : RemoteGS] : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof wp_configure Model.wp_proof Codec.wp_proof Gen.wp_proof EtcdGrove.remote.wp_Check

end linked

end Perennial.EtcdGrove.dsvcraq
