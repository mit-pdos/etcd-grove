/-
The rabia kit's links (as paxos's `Linked.lean`): the configuration protocol's proofs
(`ConfProof.lean`, over `net`'s proofs, `KitNetDeps`) and the machines' (`OrchProof.lean`,
`ClientProof.lean`, `ServerProof.lean`) applied to their callees' linked results (the server
package's `roles/server/Link.lean`, remote's `Link.lean`, `Model()`'s proof). The library
hypotheses stay instance arguments (`zerolog.Hyps`, `os.signal.NoSignals`, `math.rand.Hyps`): the
closed statement carries them; `log.Println`'s proof (from Perennial's model) is `kitNetDeps`'.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.Mains
public import Dsverify.Proof.rabia.examples.rabianet.ConfProof
public import Dsverify.Proof.rabia.examples.rabianet.ConnReadFull
public import Dsverify.Proof.rabia.examples.rabianet.ClientProof
public import Dsverify.Proof.rabia.examples.rabianet.ServerProof
public import Dsverify.Proof.rabia.examples.rabianet.OrchProof
public import Dsverify.Proof.rabia.examples.rabianet.ModelProof
public import Dsverify.Proof.rabia.internal.config.CalcConstants
public import Dsverify.Proof.log.Println
public import Dsverify.Proof.rabia.roles.server.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Net.Proof.net.Listen
public import Net.Proof.net.Dial
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close

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
variable [math.rand.Hyps GF]

-- the configuration protocol
theorem kitNetDeps : KitNetDeps (GF := GF) where
  dial := net.Dial.wp_proof
  listen := net.Listen.wp_proof
  accept := net.Listener.Accept.wp_proof
  read := net.Conn.Read.wp_proof
  write := net.Conn.Write.wp_proof
  close := net.Conn.Close.wp_proof
  readFullLt := io.ReadFull.wp_proofLt
  calcConstants := rabia.internal.config.Config.CalcConstants.wp_proof
  println := log.Println.wp_proof
theorem wp_configure_linked : configure.spec (GF := GF) := configure.wp_proof kitNetDeps
theorem wp_waitConf : waitConf.spec (GF := GF) := waitConf.wp_proof kitNetDeps
theorem wp_New : New.spec (GF := GF) := New.wp_proof kitNetDeps
theorem wp_newClient : newClient.spec (GF := GF) :=
  newClient.wp_proof ClientConfAddrs.wp_proof wp_waitConf NetAddrs.wp_proof wp_configure_linked
    ProxyAddrs.wp_proof EtcdGrove.dsvrabia.wp_ClientTcpInit EtcdGrove.dsvrabia.wp_ClientTCP_Connect

-- the machines
theorem wp_Server [github_com.rs.zerolog.Hyps GF] [os.signal.NoSignals GF] :
    Server.spec (GF := GF) :=
  Server.wp_proof EtcdGrove.dsvrabia.wp_ServerInit EtcdGrove.dsvrabia.wp_Prologue
    EtcdGrove.dsvrabia.wp_ServerMain wp_configure_linked ProxyAddrs.wp_proof NetAddrs.wp_proof
    ServerConfAddrs.wp_proof wp_waitConf

theorem wp_Client (wp_Codec : Codec.spec (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) :=
  Client.wp_proof wp_Codec EtcdGrove.remote.wp_ServeClient wp_newClient ClientAddrs.wp_proof
    attempt.wp_proof

theorem wp_Orch (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_gens : gens.spec (GF := GF) (hG := hG)) :
    Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof Model.wp_proof wp_Codec wp_gens EtcdGrove.remote.wp_Check wp_New
    ClientAddrs.wp_proof attempt.wp_proof

end linked

end Perennial.rabia.examples.rabianet
