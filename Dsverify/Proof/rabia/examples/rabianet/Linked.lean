/-
The rabia kit's links (as paxos's `Linked.lean`): its machines' proofs (`OrchProof.lean`,
`ClientProof.lean`, `ServerProof.lean`) applied to their callees' linked results (the server
package's `roles/server/Link.lean`, remote's `Link.lean`, `Model()`'s proof). The library
hypotheses stay instance arguments (`zerolog.Hyps`, `os.signal.NoSignals`, `math.rand.Hyps`,
`log.Hyps`): the closed statement carries them.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.Mains
public import Dsverify.Proof.rabia.roles.server.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Net EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [NaInvG GF]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [srv_sem : rabia.roles.server.Assumptions]
variable [tcp_sem : rabia.internal.tcp.Assumptions] [msg_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj] [sync.Assumptions]
variable [math.rand.Hyps GF] [log.Hyps GF]

theorem wp_Server [github_com.rs.zerolog.Hyps GF] [os.signal.NoSignals GF] :
    Server.spec (GF := GF) :=
  Server.wp_proof rabia.roles.server.wp_ServerInit rabia.roles.server.wp_Prologue
    rabia.roles.server.wp_ServerMain

theorem wp_Client (wp_Codec : Codec.spec (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof wp_Codec EtcdGrove.remote.wp_ServeClient

theorem wp_Orch (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_gens : gens.spec (GF := GF) (hG := hG)) :
    Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof Model.wp_proof wp_Codec wp_gens EtcdGrove.remote.wp_Check

end linked

end Perennial.rabia.examples.rabianet
