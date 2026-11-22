/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/Link.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The links (hand-written, decision D3): each Go function's proof applied to its callees' linked
results, `X.wp_X : X.spec`. The only file where the modules' proofs meet.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.NetProof
public import Dsverify.Proof.github_com.xiang90.paxos.AcceptorProof
public import Dsverify.Proof.github_com.xiang90.paxos.LearnerProof
public import Dsverify.Proof.github_com.xiang90.paxos.ProposerProof
public import Dsverify.Proof.github_com.xiang90.paxos.DeployProof

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Net

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions] [field_sem : net.FieldAssumptions]
  [sync.Assumptions]

-- transport (no callees outside its module)
theorem wp_newTCPNode : newTCPNode.spec (GF := GF) (hG := hG) := newTCPNode.wp_proof
theorem wp_serve : tcpNode.serve.spec (GF := GF) (hG := hG) := tcpNode.serve.wp_proof
theorem wp_network : tcpNode.network.spec (GF := GF) (hG := hG) := tcpNode.network.wp_proof
theorem wp_send : tcpNetwork.send.spec (GF := GF) (hG := hG) := tcpNetwork.send.wp_proof
theorem wp_recv : tcpNetwork.recv.spec (GF := GF) (hG := hG) := tcpNetwork.recv.wp_proof
theorem wp_poll : tcpNetwork.poll.spec (GF := GF) (hG := hG) := tcpNetwork.poll.wp_proof
-- agents
theorem wp_newAcceptor : newAcceptor.spec (GF := GF) (hG := hG) := newAcceptor.wp_proof
theorem wp_acceptor_run : acceptor.run.spec (GF := GF) (hG := hG) :=
  acceptor.run.wp_proof wp_send wp_recv
theorem wp_newLearner : newLearner.spec (GF := GF) (hG := hG) := newLearner.wp_proof
theorem wp_learn : learner.learn.spec (GF := GF) (hG := hG) := learner.learn.wp_proof wp_recv
theorem wp_newProposer : newProposer.spec (GF := GF) (hG := hG) := newProposer.wp_proof
theorem wp_proposer_run : proposer.run.spec (GF := GF) (hG := hG) :=
  proposer.run.wp_proof wp_send wp_recv
-- deployment
theorem wp_initialize : initialize'.spec (GF := GF) (hG := hG) := initialize'.wp_proof
theorem wp_NewNetCluster : NewNetCluster.spec (GF := GF) (hG := hG) :=
  NewNetCluster.wp_proof wp_newTCPNode wp_serve
theorem wp_RunServer : RunServer.spec (GF := GF) (hG := hG) :=
  RunServer.wp_proof wp_newTCPNode wp_serve wp_network wp_send wp_newAcceptor wp_acceptor_run
    wp_newLearner wp_learn
theorem wp_Propose : NetCluster.Propose.spec (GF := GF) (hG := hG) :=
  NetCluster.Propose.wp_proof wp_network wp_poll wp_recv wp_newProposer wp_proposer_run

end link

end github_com.xiang90.paxos

end Perennial
