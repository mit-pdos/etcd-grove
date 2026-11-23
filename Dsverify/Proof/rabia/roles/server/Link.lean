/-
The server's links (as paxos's `Link.lean`, hand-written): `ServerInit` and `Server.Prologue`
applied to tcp's endpoints' proofs (`ProxyTcpInit`, `NetTCPInit`, `ProxyTCP.Connect`,
`NetTCP.Connect`). The library hypotheses stay instance arguments (`zerolog.Hyps`,
`os.signal.NoSignals`, `math.rand.Hyps`): the closed statement carries them.
-/
module

public import Dsverify.Proof.rabia.roles.server.ServerInit
public import Dsverify.Proof.rabia.roles.server.Server__Prologue
public import Dsverify.Proof.rabia.roles.server.Server__ServerMain
public import Dsverify.Proof.rabia.internal.tcp.ProxyTcpInit
public import Dsverify.Proof.rabia.internal.tcp.ProxyTCP__Connect
public import Dsverify.Proof.rabia.internal.tcp.NetTCPInit
public import Dsverify.Proof.rabia.internal.tcp.NetTCP__Connect

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.rabia.roles.server

open Iris Iris.BI Net

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.Assumptions]
variable [tcp_sem : rabia.internal.tcp.Assumptions] [msg_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj] [sync.Assumptions]

theorem wp_ServerInit [github_com.rs.zerolog.Hyps GF] : ServerInit.spec (GF := GF) :=
  ServerInit.wp_proof rabia.internal.tcp.ProxyTcpInit.wp_proof rabia.internal.tcp.NetTCPInit.wp_proof

theorem wp_Prologue [github_com.rs.zerolog.Hyps GF] [os.signal.NoSignals GF] :
    Server.Prologue.spec (GF := GF) :=
  Server.Prologue.wp_proof rabia.internal.tcp.NetTCP.Connect.wp_proof
    rabia.internal.tcp.ProxyTCP.Connect.wp_proof

theorem wp_ServerMain [github_com.rs.zerolog.Hyps GF] [math.rand.Hyps GF] :
    Server.ServerMain.spec (GF := GF) :=
  Server.ServerMain.wp_proof

end link

end Perennial.rabia.roles.server
