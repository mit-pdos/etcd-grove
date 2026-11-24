/-
The results of the net/rpc model (`models/net/rpc`, project models-net; phase 5.2 of
`notes/dsverify-net-port-plan.md`, the Lean half): each proved spec with its callees' proofs
plugged in (the net extension's `Conn.Read` for the reads, Perennial's `sync.Mutex`), restated, with
`#print axioms` of each (none beyond Lean's; the translation's trusted code, `go/token.IsExported`
and the model's stuck point `stuck`, `Net/TrustedCode/net/rpc.lean`, is not an axiom: the proofs
show `stuck` is never reached).

* the wire's helpers: `putU64`, `getU64`, `putString`, `putFrame`, `getString`;
* the reads: `readFull` (gob's `recvMessage` errors: `io.EOF` between frames,
  `io.ErrUnexpectedEOF` within one, the connection's `*OpError`), `readFrame`, and the client
  codec's `ReadResponseHeader` (a frame of `respHdr seq sm e`, or `errFrame`, or a read error) and
  `ReadResponseBody` (a frame, decoded into the body unless it is `nil`);
* the client codec's `WriteRequest` (the sticky error, or `reqWire` written through the library's
  `sendTok`; a frame longer than `maxFrame`, the model's stuck point, excluded by the caller's
  bound) and `Close`;
* the codec registry: `SetCodec`, `getCodec` (`Codec.lean`: `CodecSpec`, `codecIs`, `codecSet`).

* the client (`ClientDefs.lean`, over the protocol `Proto.lean`): `newClientCodec`, `Call.done`,
  `Client.Close`, `Client.send`, `Client.Go`, `Client.Call` (dsverify-lab's statement), the reader
  `Client.input`, and `NewClientWithCodec`, `NewClient`, `Dial` (`net.Dial`'s proof).

* the server (`ServerDefs.lean`): the server codec's `ReadRequestHeader`, `ReadRequestBody`,
  `WriteResponse` (`respWire`, an error response's body not encoded) and `Close` (the `closed`
  flag), `newServerCodec`; `NewServer`, the free lists, `register` (the codec's `Receiver`, `rcvOk`)
  with `Register`, `RegisterName`, the package-level `Register` and `RegisterName` (on
  `DefaultServer`, `defaultServer`), and `go/token.IsExported` on an ASCII upper-case first byte.

* the request loop (`ServerGhost.lean`: a request read is a client's, taken once; an answer
  recorded at its response's write): `sendResponse`, `service.call`, `readRequestHeader`,
  `readRequest`, `ServeCodec` (Perennial's thread-token join for its runs), `ServeConn`, `Accept`
  (`log.Println`'s spec, `Net/Spec/log/Println.lean`; on a listener at a valid address or a
  wildcard, at the address each connection was dialed to; `Accept.wp_addr` at a valid address);
* the server's handler over HTTP, `ServeHTTP` (on a `CONNECT`, over the response's `hijackOk`,
  `Net/Proof/net/http/ServerDefs.lean`).

The HTTP client (`section http`): `DialHTTPPath`, `DialHTTP`, over net/http's `ReadResponse`
(`Net/Proof/net/http/Results.lean`) and the net extension's `Conn.Read` (`specLc`); pending, as
`ReadResponse`, on Perennial's `strings.Cut` and `strings.TrimLeft` (hypotheses `h_Cut`,
`h_TrimLeft`).
Not yet proved (the plan note, phase 5.2, lists what remains): `HandleHTTP` and net/http's server
up to the hijack (which gives `ServeHTTP` its `hijackOk`).
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
public import Net.Proof.net.rpc.Call__done
public import Net.Proof.net.rpc.Client__Close
public import Net.Proof.net.rpc.Client__send
public import Net.Proof.net.rpc.Client__Go
public import Net.Proof.net.rpc.Client__Call
public import Net.Proof.net.rpc.Client__CloseClosed
public import Net.Proof.net.rpc.Client__sendClosed
public import Net.Proof.net.rpc.Client__GoClosed
public import Net.Proof.net.rpc.Client__CallClosed
public import Net.Proof.net.rpc.newClientCodec
public import Net.Proof.net.rpc.Client__input
public import Net.Proof.net.rpc.NewClientWithCodec
public import Net.Proof.net.rpc.NewClient
public import Net.Proof.net.rpc.Dial
public import Net.Proof.net.Dial
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.rpc.DialHTTPPath
public import Net.Proof.net.rpc.DialHTTP
public import Proof.bufio.NewReader
public import Proof.bufio.NewReaderSize
public import Proof.bufio.NewReaderOk
public import Net.Proof.net.http.Results
public import Net.Proof.net.Conn__Read
public import Perennial.Proof.sync.Link
public import Net.Proof.net.rpc.serverCodec__ReadRequestHeader
public import Net.Proof.net.rpc.serverCodec__ReadRequestBody
public import Net.Proof.net.rpc.serverCodec__WriteResponse
public import Net.Proof.net.rpc.serverCodec__Close
public import Net.Proof.net.rpc.newServerCodec
public import Net.Proof.net.rpc.NewServer
public import Net.Proof.net.rpc.Server__getRequest
public import Net.Proof.net.rpc.Server__freeRequest
public import Net.Proof.net.rpc.Server__getResponse
public import Net.Proof.net.rpc.Server__freeResponse
public import Net.Proof.net.rpc.Server__register
public import Net.Proof.net.rpc.Server__Register
public import Net.Proof.net.rpc.Server__RegisterName
public import Net.Proof.net.rpc.Register
public import Net.Proof.net.rpc.RegisterName
public import Net.Proof.net.rpc.NewServerOwned
public import Net.Proof.net.rpc.Server__registerFresh
public import Net.Proof.net.rpc.Server__RegisterFresh
public import Net.Proof.net.rpc.Server__RegisterNameFresh
public import Net.Proof.net.rpc.RegisterFresh
public import Net.Proof.net.rpc.RegisterNameFresh
public import Net.Proof.net.rpc.Server__registerNone
public import Net.Proof.net.rpc.Server__RegisterNone
public import Net.Proof.net.rpc.RegisterNone
public import Net.Proof.go.token.IsExported
public import Net.Proof.net.rpc.Server__sendResponse
public import Net.Proof.net.rpc.service__call
public import Net.Proof.net.rpc.Server__readRequestHeader
public import Net.Proof.net.rpc.Server__readRequest
public import Net.Proof.net.rpc.Server__ServeCodec
public import Net.Proof.net.rpc.Server__ServeConn
public import Net.Proof.net.rpc.Server__ServeHTTP
public import Net.Proof.net.rpc.AcceptAddr
public import Net.Proof.net.rpc.Server__Accept
public import Net.Proof.net.Listener__Accept
public import Net.Proof.log.Println

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

theorem newClientCodec.wp : newClientCodec.spec (GF := GF) (hG := hG) := newClientCodec.wp_proof

end results

section client
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions]
variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [sync.Assumptions] [NetProtoGS]

theorem Call.done.wp : Call.done.spec (GF := GF) (hG := hG) := Call.done.wp_proof

theorem Client.Close.wp : Client.Close.spec (GF := GF) (hG := hG) :=
  Client.Close.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock clientCodec.Close.wp

theorem Client.send.wp : Client.send.spec (GF := GF) (hG := hG) :=
  Client.send.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock clientCodec.WriteRequest.wp
    Call.done.wp

theorem Client.Go.wp : Client.Go.spec (GF := GF) (hG := hG) := Client.Go.wp_proof Client.send.wp

theorem Client.Call.wp : Client.Call.spec (GF := GF) (hG := hG) := Client.Call.wp_proof Client.Go.wp

theorem Client.Close.wp_closed : Client.Close.spec_closed (GF := GF) (hG := hG) :=
  Client.Close.wp_proof_closed sync.Mutex.wp_Lock sync.Mutex.wp_Unlock clientCodec.Close.wp

theorem Client.send.wp_closed : Client.send.spec_closed (GF := GF) (hG := hG) :=
  Client.send.wp_proof_closed sync.Mutex.wp_Lock sync.Mutex.wp_Unlock Call.done.wp

theorem Client.Go.wp_closed : Client.Go.spec_closed (GF := GF) (hG := hG) :=
  Client.Go.wp_proof_closed Client.send.wp_closed

theorem Client.Call.wp_closed : Client.Call.spec_closed (GF := GF) (hG := hG) :=
  Client.Call.wp_proof_closed Client.Go.wp_closed

theorem Client.input.wp [errors.Assumptions] : Client.input.spec (GF := GF) (hG := hG) :=
  Client.input.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock clientCodec.ReadResponseHeader.wp
    clientCodec.ReadResponseBody.wp Call.done.wp

theorem NewClientWithCodec.wp [errors.Assumptions] : NewClientWithCodec.spec (GF := GF) (hG := hG) :=
  NewClientWithCodec.wp_proof Client.input.wp

theorem NewClient.wp [errors.Assumptions] : NewClient.spec (GF := GF) (hG := hG) :=
  NewClient.wp_proof newClientCodec.wp NewClientWithCodec.wp

theorem Dial.wp [errors.Assumptions] : Dial.spec (GF := GF) (hG := hG) :=
  Dial.wp_proof net.Dial.wp_proof NewClient.wp

end client


section server
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions]
variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [sync.Assumptions] [NetProtoGS]

theorem serverCodec.ReadRequestHeader.wp :
    serverCodec.ReadRequestHeader.spec (GF := GF) (hG := hG) :=
  serverCodec.ReadRequestHeader.wp_proof readFrame.wp getU64.wp_proof getString.wp

theorem serverCodec.ReadRequestBody.wp : serverCodec.ReadRequestBody.spec (GF := GF) (hG := hG) :=
  serverCodec.ReadRequestBody.wp_proof readFrame.wp getCodec.wp

theorem serverCodec.WriteResponse.wp : serverCodec.WriteResponse.spec (GF := GF) (hG := hG) :=
  serverCodec.WriteResponse.wp_proof getCodec.wp putU64.wp_proof putString.wp putFrame.wp
    net.Conn.Write.wp_proof

theorem serverCodec.Close.wp : serverCodec.Close.spec (GF := GF) (hG := hG) :=
  serverCodec.Close.wp_proof net.Conn.Close.wp_proof

theorem newServerCodec.wp : newServerCodec.spec (GF := GF) (hG := hG) := newServerCodec.wp_proof

theorem NewServer.wp : NewServer.spec (GF := GF) (hG := hG) := NewServer.wp_proof

theorem Server.getRequest.wp : Server.getRequest.spec (GF := GF) (hG := hG) :=
  Server.getRequest.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

theorem Server.freeRequest.wp : Server.freeRequest.spec (GF := GF) (hG := hG) :=
  Server.freeRequest.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

theorem Server.getResponse.wp : Server.getResponse.spec (GF := GF) (hG := hG) :=
  Server.getResponse.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

theorem Server.freeResponse.wp : Server.freeResponse.spec (GF := GF) (hG := hG) :=
  Server.freeResponse.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock

theorem go.token.IsExported.wp [go.token.Assumptions] :
    go.token.IsExported.spec (GF := GF) (hG := hG) := go.token.IsExported.wp_proof

theorem Server.register.wp [errors.Assumptions] [go.token.Assumptions] :
    Server.register.spec (GF := GF) (hG := hG) :=
  Server.register.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock getCodec.wp go.token.IsExported.wp

theorem Server.Register.wp [errors.Assumptions] [go.token.Assumptions] :
    Server.Register.spec (GF := GF) (hG := hG) := Server.Register.wp_proof Server.register.wp

theorem Server.RegisterName.wp [errors.Assumptions] [go.token.Assumptions] :
    Server.RegisterName.spec (GF := GF) (hG := hG) := Server.RegisterName.wp_proof Server.register.wp

theorem Register.wp [errors.Assumptions] [go.token.Assumptions] :
    Register.spec (GF := GF) (hG := hG) := Register.wp_proof Server.Register.wp

theorem RegisterName.wp [errors.Assumptions] [go.token.Assumptions] :
    RegisterName.spec (GF := GF) (hG := hG) := RegisterName.wp_proof Server.RegisterName.wp

theorem NewServer.wp_owned : NewServer.spec_owned (GF := GF) (hG := hG) := NewServer.wp_proof_owned

theorem Server.register.wp_fresh [errors.Assumptions] [go.token.Assumptions] :
    Server.register.spec_fresh (GF := GF) (hG := hG) :=
  Server.register.wp_proof_fresh sync.Mutex.wp_Lock sync.Mutex.wp_Unlock getCodec.wp
    go.token.IsExported.wp

theorem Server.Register.wp_fresh [errors.Assumptions] [go.token.Assumptions] :
    Server.Register.spec_fresh (GF := GF) (hG := hG) :=
  Server.Register.wp_proof_fresh Server.register.wp_fresh

theorem Server.RegisterName.wp_fresh [errors.Assumptions] [go.token.Assumptions] :
    Server.RegisterName.spec_fresh (GF := GF) (hG := hG) :=
  Server.RegisterName.wp_proof_fresh Server.register.wp_fresh

theorem Register.wp_fresh [errors.Assumptions] [go.token.Assumptions] :
    Register.spec_fresh (GF := GF) (hG := hG) := Register.wp_proof_fresh Server.Register.wp_fresh

theorem RegisterName.wp_fresh [errors.Assumptions] [go.token.Assumptions] :
    RegisterName.spec_fresh (GF := GF) (hG := hG) :=
  RegisterName.wp_proof_fresh Server.RegisterName.wp_fresh

theorem Server.sendResponse.wp : Server.sendResponse.spec (GF := GF) (hG := hG) :=
  Server.sendResponse.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock Server.getResponse.wp
    Server.freeResponse.wp serverCodec.WriteResponse.wp

theorem service.call.wp : service.call.spec (GF := GF) (hG := hG) :=
  service.call.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock Server.sendResponse.wp
    Server.freeRequest.wp

theorem Server.readRequestHeader.wp [errors.Assumptions] :
    Server.readRequestHeader.spec (GF := GF) (hG := hG) :=
  Server.readRequestHeader.wp_proof sync.Mutex.wp_Lock sync.Mutex.wp_Unlock Server.getRequest.wp
    serverCodec.ReadRequestHeader.wp

theorem Server.readRequest.wp [errors.Assumptions] : Server.readRequest.spec (GF := GF) (hG := hG) :=
  Server.readRequest.wp_proof Server.readRequestHeader.wp serverCodec.ReadRequestBody.wp

theorem Server.ServeCodec.wp [errors.Assumptions] : Server.ServeCodec.spec (GF := GF) (hG := hG) :=
  Server.ServeCodec.wp_proof Server.readRequest.wp Server.sendResponse.wp Server.freeRequest.wp
    service.call.wp serverCodec.Close.wp

theorem Server.ServeConn.wp [errors.Assumptions] : Server.ServeConn.spec (GF := GF) (hG := hG) :=
  Server.ServeConn.wp_proof newServerCodec.wp Server.ServeCodec.wp

theorem log.Println.wp [log.Assumptions] : _root_.Perennial.log.Println.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.log.Println.wp_proof

theorem Server.register.wp_none [errors.Assumptions] [go.token.Assumptions] [log.Assumptions] :
    Server.register.spec_none (GF := GF) (hG := hG) :=
  Server.register.wp_proof_none getCodec.wp go.token.IsExported.wp log.Println.wp

theorem Server.Register.wp_none [errors.Assumptions] [go.token.Assumptions] [log.Assumptions] :
    Server.Register.spec_none (GF := GF) (hG := hG) :=
  Server.Register.wp_proof_none Server.register.wp_none

theorem Register.wp_none [errors.Assumptions] [go.token.Assumptions] [log.Assumptions] :
    Register.spec_none (GF := GF) (hG := hG) := Register.wp_proof_none Server.Register.wp_none

theorem Server.Accept.wp [errors.Assumptions] [log.Assumptions] :
    Server.Accept.spec (GF := GF) (hG := hG) :=
  Server.Accept.wp_proof net.Listener.Accept.wp_proof log.Println.wp Server.ServeConn.wp

/-- `Server.Accept` at a valid address (`AcceptAddr.lean`), an instance of `Server.Accept.wp`. -/
theorem Server.Accept.wp_addr [errors.Assumptions] [log.Assumptions] :
    Server.Accept.specAddr (GF := GF) (hG := hG) :=
  Server.Accept.spec_addr Server.Accept.wp

theorem Server.ServeHTTP.wp [errors.Assumptions] [net.http.Assumptions] :
    Server.ServeHTTP.spec (GF := GF) (hG := hG) :=
  Server.ServeHTTP.wp_proof net.Conn.Write.wp_proof Server.ServeConn.wp

end server

section http
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions]
variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [sync.Assumptions] [NetProtoGS]

/-! The HTTP path (`DialHTTPPath`, `DialHTTP`), over net/http's `ReadResponse`
(`Net/Proof/net/http/Results.lean`). -/

-- Pending: Perennial's `strings.Cut` (`Net/Proof/net/http/Results.lean`, `links_pending`).
variable (h_Cut : EtcdGrove.strings.Cut.spec (GF := GF) (hG := hG))
-- Pending: Perennial's `strings.TrimLeft`.
variable (h_TrimLeft : EtcdGrove.strings.TrimLeft.spec (GF := GF) (hG := hG))

include h_Cut h_TrimLeft in
theorem DialHTTPPath.wp [errors.Assumptions] [_root_.Perennial.bufio.Assumptions] :
    DialHTTPPath.spec (GF := GF) (hG := hG) :=
  DialHTTPPath.wp_proof net.Dial.wp_proof net.Conn.Write.wp_proof net.Conn.Close.wp_proof
    (EtcdGrove.bufio.NewReader.wp_proof
      (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE))
    net.Conn.Read.wp_proofLc (net.http.ReadResponse.wp h_Cut h_TrimLeft) NewClient.wp

include h_Cut h_TrimLeft in
theorem DialHTTP.wp [errors.Assumptions] [_root_.Perennial.bufio.Assumptions] :
    DialHTTP.spec (GF := GF) (hG := hG) :=
  DialHTTP.wp_proof (DialHTTPPath.wp h_Cut h_TrimLeft)

end http


section results'

end results'

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
#print axioms Perennial.net.rpc.newClientCodec.wp
#print axioms Perennial.net.rpc.Call.done.wp
#print axioms Perennial.net.rpc.Client.Close.wp
#print axioms Perennial.net.rpc.Client.send.wp
#print axioms Perennial.net.rpc.Client.Go.wp
#print axioms Perennial.net.rpc.Client.Call.wp
#print axioms Perennial.net.rpc.Client.Close.wp_closed
#print axioms Perennial.net.rpc.Client.send.wp_closed
#print axioms Perennial.net.rpc.Client.Go.wp_closed
#print axioms Perennial.net.rpc.Client.Call.wp_closed
#print axioms Perennial.net.rpc.Client.input.wp
#print axioms Perennial.net.rpc.NewClientWithCodec.wp
#print axioms Perennial.net.rpc.NewClient.wp
#print axioms Perennial.net.rpc.Dial.wp
#print axioms Perennial.net.rpc.serverCodec.ReadRequestHeader.wp
#print axioms Perennial.net.rpc.serverCodec.ReadRequestBody.wp
#print axioms Perennial.net.rpc.serverCodec.WriteResponse.wp
#print axioms Perennial.net.rpc.serverCodec.Close.wp
#print axioms Perennial.net.rpc.newServerCodec.wp
#print axioms Perennial.net.rpc.NewServer.wp
#print axioms Perennial.net.rpc.Server.getRequest.wp
#print axioms Perennial.net.rpc.Server.freeRequest.wp
#print axioms Perennial.net.rpc.Server.getResponse.wp
#print axioms Perennial.net.rpc.Server.freeResponse.wp
#print axioms Perennial.net.rpc.go.token.IsExported.wp
#print axioms Perennial.net.rpc.Server.register.wp
#print axioms Perennial.net.rpc.Server.Register.wp
#print axioms Perennial.net.rpc.Server.RegisterName.wp
#print axioms Perennial.net.rpc.Register.wp
#print axioms Perennial.net.rpc.RegisterName.wp
#print axioms Perennial.net.rpc.NewServer.wp_owned
#print axioms Perennial.net.rpc.Server.register.wp_fresh
#print axioms Perennial.net.rpc.Server.Register.wp_fresh
#print axioms Perennial.net.rpc.Server.RegisterName.wp_fresh
#print axioms Perennial.net.rpc.Register.wp_fresh
#print axioms Perennial.net.rpc.RegisterName.wp_fresh
#print axioms Perennial.net.rpc.Server.register.wp_none
#print axioms Perennial.net.rpc.Server.Register.wp_none
#print axioms Perennial.net.rpc.Register.wp_none
#print axioms Perennial.net.rpc.Server.sendResponse.wp
#print axioms Perennial.net.rpc.service.call.wp
#print axioms Perennial.net.rpc.Server.readRequestHeader.wp
#print axioms Perennial.net.rpc.Server.readRequest.wp
#print axioms Perennial.net.rpc.Server.ServeCodec.wp
#print axioms Perennial.net.rpc.Server.ServeConn.wp
#print axioms Perennial.net.rpc.Server.Accept.wp
#print axioms Perennial.net.rpc.Server.Accept.wp_addr
#print axioms Perennial.net.rpc.Server.ServeHTTP.wp
#print axioms Perennial.net.rpc.DialHTTPPath.wp
#print axioms Perennial.net.rpc.DialHTTP.wp
