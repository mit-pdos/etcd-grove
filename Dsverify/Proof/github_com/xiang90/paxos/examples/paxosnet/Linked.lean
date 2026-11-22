/-
The paxos kit's links: its functions' proofs (`KitProof.lean`) applied to their callees' linked
results (the paxos package's `Link.lean`, remote's `Link.lean`).
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.KitProof
public import Dsverify.Proof.github_com.xiang90.paxos.examples.paxosnet.Mains
public import Dsverify.Proof.github_com.xiang90.paxos.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.xiang90.paxos.examples.paxosnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [field_sem : net.FieldAssumptions]
variable [NaInvG GF]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [package_sem : github_com.xiang90.paxos.examples.paxosnet.Assumptions]

theorem wp_Server : Server.spec (GF := GF) (hG := hG) :=
  Server.wp_proof github_com.xiang90.paxos.wp_RunServer
theorem wp_Client : Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof github_com.xiang90.paxos.wp_NewNetCluster github_com.xiang90.paxos.wp_Propose Codec.wp_proof
    EtcdGrove.remote.wp_ServeClient
theorem wp_Orch : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof Model.wp_proof Codec.wp_proof Gen.wp_proof woS_pendDec EtcdGrove.remote.wp_Check

end linked

end github_com.xiang90.paxos.examples.paxosnet
end Perennial
