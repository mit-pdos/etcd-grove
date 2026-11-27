/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/Results.lean (lab master 915f964;
notes/dsv-vr.md): the results of `network`, one theorem per spec of `Spec/network.lean`, over any
`GF`, on the net extension. Each takes as hypotheses the specs of what it calls outside the
package's proven callees (no `sorry`, no axiom); the net extension's (`net.Dial`, `Listen`,
`Listener.Accept`, `Conn.Close`, `Conn.RemoteAddr`) and `events.NewNetworkEvent` are their proofs
(`Net/Proof/net/`, `Proof/events/Results.lean`). The rest are hypotheses:
* the events package's (`Spec/events.lean`): `events.Event.FromDecoder.spec` (`NewTCP`, kept in
  `isTCP`'s reader contract; `Proof/events/Results.lean` proves it over JSON hypotheses),
  `events.newDecoder.spec` (`json.NewDecoder` on a connection: a JSON hypothesis);
* `log/slog`'s: `log.slog.Debug.spec` (`LibHyps.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Recv
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Serve
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.NewTCP
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.HandleConn
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.assert.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.Results
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__RemoteAddr

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF] [models_lab.jsoncodec.JsonCodec GF]
variable [go.BasicIntoValInj]

theorem network.NewTCP.wp
    (wp_FromDecoder : events.Event.FromDecoder.spec (GF := GF) (hG := hG)) :
    network.NewTCP.spec (GF := GF) (hG := hG) :=
  network.NewTCP.wp_proof wp_FromDecoder ipv4port.IPv4Port.FromHostPort.wp assert.Assert.wp queue.New.wp

theorem network.TCP.Run.wp
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG)) :
    network.TCP.Run.spec (GF := GF) (hG := hG) :=
  network.TCP.Run.wp_proof wp_Debug wp_newDecoder events.NewNetworkEvent.wp net.Conn.Close.wp_proof
    net.Listener.Accept.wp_proof net.Conn.RemoteAddr.wp_proof net.Listen.wp_proof
    ipv4port.FromAddrString.wp ipv4port.IPv4Port.String_ptr.wp
    (network.TCP.handleConn.wp_proof wp_Debug wp_newDecoder events.NewNetworkEvent.wp
      net.Conn.Close.wp_proof ipv4port.IPv4Port.String_ptr.wp queue.Queue.Push.wp)

theorem network.TCP.Send.wp
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG)) :
    network.TCP.Send.spec (GF := GF) (hG := hG) :=
  network.TCP.Send.wp_proof wp_Debug wp_newDecoder events.NewNetworkEvent.wp net.Dial.wp_proof
    net.Conn.Close.wp_proof ipv4port.IPv4Port.String_ptr.wp
    (network.TCP.handleConn.wp_proof wp_Debug wp_newDecoder events.NewNetworkEvent.wp
      net.Conn.Close.wp_proof ipv4port.IPv4Port.String_ptr.wp queue.Queue.Push.wp)

theorem network.TCP.Recv.wp : network.TCP.Recv.spec (GF := GF) (hG := hG) :=
  network.TCP.Recv.wp_proof queue.Queue.Pop.wp

theorem network.Network.Send.wp
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG)) :
    network.Network.Send.spec (GF := GF) (hG := hG) :=
  network.Network.Send.wp_proof wp_Debug wp_newDecoder events.NewNetworkEvent.wp net.Dial.wp_proof
    net.Conn.Close.wp_proof ipv4port.IPv4Port.String_ptr.wp
    (network.TCP.handleConn.wp_proof wp_Debug wp_newDecoder events.NewNetworkEvent.wp
      net.Conn.Close.wp_proof ipv4port.IPv4Port.String_ptr.wp queue.Queue.Push.wp)

theorem network.Network.Recv.wp : network.Network.Recv.spec (GF := GF) (hG := hG) :=
  network.Network.Recv.wp_proof queue.Queue.Pop.wp

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
