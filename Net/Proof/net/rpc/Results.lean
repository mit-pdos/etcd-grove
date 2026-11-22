/-
The results of the net/rpc model (`models/net/rpc`, project models-net; phase 5.2 of
`notes/dsverify-net-port-plan.md`, the Lean half): each proved spec with its callees' proofs
plugged in (the net extension's `Conn.Read` for the reads, Perennial's `sync.Mutex`), restated, with
`#print axioms` of each (none beyond Lean's; the translation's trusted `go/token.IsExported` is not
reached by these).

* the wire's helpers: `putU64`, `getU64`, `putString`, `putFrame`, `getString`;
* the reads: `readFull` (gob's `recvMessage` errors: `io.EOF` between frames,
  `io.ErrUnexpectedEOF` within one, the connection's `*OpError`), `readFrame`, and the client
  codec's `ReadResponseHeader` (a frame of `respHdr seq sm e`, or `errFrame`, or a read error) and
  `ReadResponseBody` (a frame, decoded into the body unless it is `nil`);
* the client codec's `WriteRequest` (the sticky error, or `reqWire` written through the library's
  `sendTok`) and `Close`;
* the codec registry: `SetCodec`, `getCodec` (`Codec.lean`: `CodecSpec`, `codecIs`, `codecSet`).

Not yet stated (the plan note, phase 5.2, lists what remains): the server codec's methods, the
Client (`Call`, `Go`, `Close`, `NewClient`, `Dial`, `DialHTTP(Path)`), the Server (`Register(Name)`,
`ServeConn`/`ServeCodec`, `ServeHTTP`, `HandleHTTP`) and the generated `Codec`'s `Receiver`.
-/
module

public import Net.Proof.net.rpc.putU64
public import Net.Proof.net.rpc.getU64
public import Net.Proof.net.rpc.putString
public import Net.Proof.net.rpc.putFrame
public import Net.Proof.net.rpc.getString
public import Net.Proof.net.rpc.readFull
public import Net.Proof.net.rpc.readFrame
public import Net.Proof.net.rpc.getCodec
public import Net.Proof.net.rpc.SetCodec
public import Net.Proof.net.rpc.clientCodec__ReadResponseHeader
public import Net.Proof.net.rpc.clientCodec__ReadResponseBody
public import Net.Proof.net.rpc.clientCodec__WriteRequest
public import Net.Proof.net.rpc.clientCodec__Close
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__Read
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions]

theorem putU64.wp : putU64.spec (GF := GF) (hG := hG) := putU64.wp_proof

theorem getU64.wp : getU64.spec (GF := GF) (hG := hG) := getU64.wp_proof

theorem putString.wp : putString.spec (GF := GF) (hG := hG) := putString.wp_proof putU64.wp_proof

theorem putFrame.wp : putFrame.spec (GF := GF) (hG := hG) := putFrame.wp_proof putU64.wp_proof

theorem getString.wp : getString.spec (GF := GF) (hG := hG) := getString.wp_proof getU64.wp_proof

theorem getCodec.wp [sync.Assumptions] : getCodec.spec (GF := GF) (hG := hG) :=
  getCodec.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

theorem SetCodec.wp [sync.Assumptions] : SetCodec.spec (GF := GF) (hG := hG) :=
  SetCodec.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]

theorem readFull.wp : readFull.spec (GF := GF) (hG := hG) :=
  readFull.wp_proof net.Conn.Read.wp_proof

theorem readFrame.wp : readFrame.spec (GF := GF) (hG := hG) :=
  readFrame.wp_proof readFull.wp getU64.wp_proof

theorem clientCodec.ReadResponseHeader.wp : clientCodec.ReadResponseHeader.spec (GF := GF) (hG := hG) :=
  clientCodec.ReadResponseHeader.wp_proof readFrame.wp getU64.wp_proof getString.wp

theorem clientCodec.ReadResponseBody.wp [sync.Assumptions] :
    clientCodec.ReadResponseBody.spec (GF := GF) (hG := hG) :=
  clientCodec.ReadResponseBody.wp_proof readFrame.wp getCodec.wp

theorem clientCodec.WriteRequest.wp [sync.Assumptions] [NetProtoGS] :
    clientCodec.WriteRequest.spec (GF := GF) (hG := hG) :=
  clientCodec.WriteRequest.wp_proof getCodec.wp putU64.wp_proof putString.wp putFrame.wp
    net.Conn.Write.wp_proof

theorem clientCodec.Close.wp : clientCodec.Close.spec (GF := GF) (hG := hG) :=
  clientCodec.Close.wp_proof net.Conn.Close.wp_proof

end results

end net.rpc
end Perennial

#print axioms Perennial.net.rpc.putU64.wp
#print axioms Perennial.net.rpc.getU64.wp
#print axioms Perennial.net.rpc.putString.wp
#print axioms Perennial.net.rpc.putFrame.wp
#print axioms Perennial.net.rpc.getString.wp
#print axioms Perennial.net.rpc.getCodec.wp
#print axioms Perennial.net.rpc.SetCodec.wp
#print axioms Perennial.net.rpc.readFull.wp
#print axioms Perennial.net.rpc.readFrame.wp
#print axioms Perennial.net.rpc.clientCodec.ReadResponseHeader.wp
#print axioms Perennial.net.rpc.clientCodec.ReadResponseBody.wp
#print axioms Perennial.net.rpc.clientCodec.WriteRequest.wp
#print axioms Perennial.net.rpc.clientCodec.Close.wp
