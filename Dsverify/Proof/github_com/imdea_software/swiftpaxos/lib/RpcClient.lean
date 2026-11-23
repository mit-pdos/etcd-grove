/-
`Net/Proof/net/rpc/Results.lean`'s client half (its compositions, copied), under this part's own
namespace: `Results` also imports the server's proofs, whose `Server__Accept` does not build on `lean`
`1b2fd95b30` (notes/dsv-swiftpaxos.md, "models-rpc-server"). To be dropped for `Results` once it builds.
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
public import Net.Proof.net.rpc.newClientCodec
public import Net.Proof.net.rpc.Client__input
public import Net.Proof.net.rpc.NewClientWithCodec
public import Net.Proof.net.rpc.NewClient
public import Net.Proof.net.rpc.Dial
public import Net.Proof.net.Dial
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__Read
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc.swiftClient

open net.rpc

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

end net.rpc.swiftClient

end Perennial
