/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/Results.lean (lab master 915f964;
notes/dsv-vr.md): the results of `network`, one theorem per spec of `Spec/network.lean`, over any
`GF`, on the net extension. Each takes as hypotheses the specs of what it calls outside the
package's proven callees (no `sorry`, no axiom):
* the net extension's canonical specs (`Net/Spec/net/`): `net.Dial.spec`, `net.Listen.spec`,
  `net.Listener.Accept.spec`, `net.Conn.Close.spec`, `net.Conn.RemoteAddr.spec`;
* the events package's (`Spec/events.lean`): `events.Event.FromDecoder.spec` (`NewTCP`, kept in
  `isTCP`'s reader contract), `events.newDecoder.spec` (`json.NewDecoder` on a connection),
  `events.NewNetworkEvent.spec`;
* `log/slog`'s: `log.slog.Debug.spec` (`LibHyps.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Recv
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Serve
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.NewTCP

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF] [models_lab.jsoncodec.JsonCodec GF]

theorem network.NewTCP.wp
    (wp_FromDecoder : events.Event.FromDecoder.spec (GF := GF) (hG := hG)) :
    network.NewTCP.spec (GF := GF) (hG := hG) :=
  network.NewTCP.wp_proof wp_FromDecoder

theorem network.TCP.Run.wp
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_RemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG)) :
    network.TCP.Run.spec (GF := GF) (hG := hG) :=
  network.TCP.Run.wp_proof wp_Debug wp_newDecoder wp_NewNetworkEvent wp_Close wp_Accept
    wp_RemoteAddr wp_Listen

theorem network.TCP.Send.wp
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    network.TCP.Send.spec (GF := GF) (hG := hG) :=
  network.TCP.Send.wp_proof wp_Debug wp_newDecoder wp_NewNetworkEvent wp_Dial wp_Close

theorem network.TCP.Recv.wp : network.TCP.Recv.spec (GF := GF) (hG := hG) :=
  network.TCP.Recv.wp_proof

theorem network.Network.Send.wp
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    network.Network.Send.spec (GF := GF) (hG := hG) :=
  network.Network.Send.wp_proof wp_Debug wp_newDecoder wp_NewNetworkEvent wp_Dial wp_Close

theorem network.Network.Recv.wp : network.Network.Recv.spec (GF := GF) (hG := hG) :=
  network.Network.Recv.wp_proof

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
