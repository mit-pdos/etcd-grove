/-
The QuePaxa kit's links: its functions' proofs (`KitGen`, `KitCodecFn`, `KitOrch`, `KitServer`,
`KitClient`)
applied to their callees' proofs (the kit's model, remote's `Link.lean`, `net`'s, `IoReadFull`'s,
Perennial's `strings.Split`, the replica's `Replica/Results`).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitServer
public import Dsverify.Proof.raxos.examples.quepaxanet.KitOrch
public import Dsverify.Proof.raxos.examples.quepaxanet.KitClient
public import Perennial.Proof.time.After
public import Dsverify.Proof.raxos.examples.quepaxanet.ModelProof
public import Dsverify.Proof.raxos.Replica.Results
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Net.Proof.net.Dial
public import Net.Proof.net.Conn__Write
public import Perennial.Proof.strings.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [_root_.Perennial.io.Assumptions] [log.Assumptions] [strings.Assumptions]
variable [NaInvG GF]

attribute [local instance] qpBufioDeps_holds qpNetDeps_holds qpFormatIntDeps_holds
  qpPrintfDeps_holds

theorem wp_Codec : Codec.spec (GF := GF) (hG := hG) := codec_proof

theorem wp_Gens : Gens.spec (GF := GF) (hG := hG) := gens_proof

theorem wp_Orch [hyp.RandHyp GF] : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof Model.wp_proof EtcdGrove.remote.wp_Check net.Conn.Read.wp_proof
    net.Conn.Write.wp_proof net.Conn.Close.wp_proof
    (raxos.ioLt.ReadFull.wp_proof raxos.ioLt.ReadAtLeast.wp_proof) net.Dial.wp_proof

theorem wp_Server [hyp.sync.MapHyp qv.map] [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.UtcHyp GF] [hyp.PrintlnHyp GF] [hyp.PbHyp GF] [hyp.SortHyp GF]
    [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
    [strconv.Assumptions] [time.Assumptions] [fmt.Assumptions]
    [_root_.Perennial.bufio.Assumptions] [errors.Assumptions] :
    Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof strings.wp_Split raxos.New.wp_proof raxos.Server.NetworkInit.wp_proof
    raxos.Server.StartProposers.wp_proof raxos.Server.Run.wp_proof net.Listen.wp_proof
    net.Listener.Accept.wp_proof net.Conn.Read.wp_proof net.Conn.Write.wp_proof
    net.Conn.Close.wp_proof (raxos.ioLt.ReadFull.wp_proof raxos.ioLt.ReadAtLeast.wp_proof)

theorem wp_Client [hyp.PbHyp GF] [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
    [time.Assumptions] [_root_.Perennial.bufio.Assumptions] [errors.Assumptions]
    [github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
    [github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]
    [github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Assumptions] :
    Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof EtcdGrove.remote.wp_ServeClient wp_Codec net.Listen.wp_proof
    net.Listener.Accept.wp_proof net.Conn.Read.wp_proof net.Conn.Write.wp_proof
    net.Conn.Close.wp_proof (raxos.ioLt.ReadFull.wp_proof raxos.ioLt.ReadAtLeast.wp_proof)
    net.Dial.wp_proof
    (EtcdGrove.bufio.NewReader.wp_proofOk
      (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE))
    time.After.wp_proof

end linked

end raxos.examples.quepaxanet
end Perennial

#print axioms Perennial.raxos.examples.quepaxanet.wp_Codec
#print axioms Perennial.raxos.examples.quepaxanet.wp_Gens
#print axioms Perennial.raxos.examples.quepaxanet.wp_Orch
#print axioms Perennial.raxos.examples.quepaxanet.wp_Server
#print axioms Perennial.raxos.examples.quepaxanet.wp_Client
