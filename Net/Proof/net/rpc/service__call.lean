/-
The proof of `service.call` (`Net/Spec/net/rpc/service__call.lean`): `wg.Done()` deferred (the
join's `ownDone`, `sync.tokJoin.WaitGroup.wp_Done`, which gives the slot's thread token back), the
counter incremented under the method's mutex, the method's call (`callReady`'s `WP`), the error's
message (`errMsg`'s `Error()`) or `""`, the response (`sendResponse`, whose `ansRes` is `callRet`'s
outcome), `req` freed.
-/
module

public import Net.Spec.net.rpc.service__call
public import Net.Spec.net.rpc.Server__sendResponse
public import Net.Spec.net.rpc.Server__freeRequest
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
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

theorem service.call.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_sendResponse : Server.sendResponse.spec (GF := GF) (hG := hG))
    (wp_freeRequest : Server.freeRequest.spec (GF := GF) (hG := hG)) :
    service.call.spec (GF := GF) (hG := hG) := by
  intro svc s γs C W a sc t cn la ra sending wg mt req rqv argv replyv k Φ
  wp_start as ⟨#Hsrv, #Henv, #Hset, #Hsc, #Hmu, Hreq, ⟨%Hseq, %Hwg⟩, Hpend, Hcall, Hdone⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨#Hsync, -⟩
  iunfold callReady at Hcall
  icases Hcall with ⟨%rcvr, %mm, %v, #Hrcvr, #Hm, #Hv, #Hmmu, Hwp⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_auto
  sorry

end proof

end net.rpc
end Perennial
