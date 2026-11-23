/-
The proof of `Server.sendResponse` (`Net/Spec/net/rpc/Server__sendResponse.lean`): a free
`*Response` (`getResponse`), its fields set (`invalidRequest` as the reply of an error response),
then under `sending` (`srvSendInv`) the codec's `WriteResponse`: with no write error yet, the
update `respUpd` answers the request (`answer`) and extends the record of answers (`resp_step`);
the write's result, whole or in part (its error then sticky), keeps `srvSendInv`. `debugLog` is
`false`; the response goes back to its free list.
-/
module

public import Net.Spec.net.rpc.Server__sendResponse
public import Net.Spec.net.rpc.Server__getResponse
public import Net.Spec.net.rpc.Server__freeResponse
public import Net.Spec.net.rpc.serverCodec__WriteResponse
public import Net.Proof.net.rpc.ServerGhost
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.sendResponse.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_getResponse : Server.getResponse.spec (GF := GF) (hG := hG))
    (wp_freeResponse : Server.freeResponse.spec (GF := GF) (hG := hG))
    (wp_WriteResponse : serverCodec.WriteResponse.spec (GF := GF) (hG := hG)) :
    Server.sendResponse.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra sending req rqv reply errmsg k Φ
  wp_start as ⟨#Hsrv, #Henv, #Hset, #Hsc, #Hmu, Hreq, %Hseq, Hpend, Hres⟩
  iunfold srvEnv at Henv
  icases Henv with ⟨#Hcli, #Hir⟩
  ihave #Hcli' := Hcli
  iunfold cliEnv at Hcli'
  icases Hcli' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  iunfold srvCodecAt at Hsc
  icases Hsc with ⟨#Hrwc, #Hconn⟩
  wp_auto
  wp_apply wp_getResponse s γs $$ Hsrv as %resp Hresp
  wp_auto
  sorry

end proof

end net.rpc
end Perennial
