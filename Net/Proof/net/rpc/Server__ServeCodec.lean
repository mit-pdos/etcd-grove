/-
The proof of `Server.ServeCodec` (`Net/Spec/net/rpc/Server__ServeCodec.lean`). `sending` is a new
mutex over `srvSendInv` (nothing written, no answer recorded); `wg` a new thread-token join
(`sync.tokJoin` at `srvWgN`, no lending: `lendLaw_false`). **The loop's invariant**: the reader's
resources (`rdrOwn`), the join's adder, the reader's thread token. **An iteration**
(`readRequest`): a read failure ends the loop; an error with the request taken is answered at once
(`sendResponse`, with `errCont`'s `Φ [] msg` for the error's message, not empty) and the request
freed; a request ready to run is added to the join (`Add(1)` with the thread token) and runs in a
goroutine (`service.call`, `wp_fork_tok_self`: the token of the `go` statement comes back to the
reader, the goroutine exits with the slot's). **After the loop**: `Wait`, then the codec's `Close`
(`close_au`, the end's `connIs` from its tokens).
-/
module

public import Net.Spec.net.rpc.Server__ServeCodec
public import Net.Spec.net.rpc.Server__readRequest
public import Net.Spec.net.rpc.Server__sendResponse
public import Net.Spec.net.rpc.Server__freeRequest
public import Net.Spec.net.rpc.service__call
public import Net.Spec.net.rpc.serverCodec__Close
public import Net.Proof.net.rpc.ServerGhost
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.ServeCodec.wp_proof
    (wp_readRequest : Server.readRequest.spec (GF := GF) (hG := hG))
    (wp_sendResponse : Server.sendResponse.spec (GF := GF) (hG := hG))
    (wp_freeRequest : Server.freeRequest.spec (GF := GF) (hG := hG))
    (wp_call : service.call.spec (GF := GF) (hG := hG))
    (wp_Close : serverCodec.Close.spec (GF := GF) (hG := hG)) :
    Server.ServeCodec.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra
  wp_start as ⟨%Hb, #Hsrv, #Hserves, #Henv, #Hset, #Hsc, Hown, Htok⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨#Hsync, -⟩
  iunfold srvCodecOwn at Hown
  icases Hown with ⟨Hwerr, Hrerr, Hclosed, Hacc⟩
  iunfold rpcAccepted at Hacc
  icases Hacc with ⟨Hsend, Hrecv, Hfresh⟩
  ihave #Hci := sendTok_connIs $$ Hsend
  wp_auto
  sorry

end proof

end net.rpc
end Perennial
