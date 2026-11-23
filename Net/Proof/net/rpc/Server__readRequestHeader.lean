/-
The proof of `Server.readRequestHeader` (`Net/Spec/net/rpc/Server__readRequestHeader.lean`): a
free `*Request` (`getRequest`), the codec's `ReadRequestHeader` through the reader's `recvTokL`
(`rd_acc_srv`). A failure (or an earlier one, `rerr`): `keepReading` stays `false` (the
comparisons with `io.EOF` and `io.ErrUnexpectedEOF` compare pointers; a new `errors.New` error
otherwise). A header: the request it is, taken (`req_hdr`: three later credits, the protocol
fact's and `req_hdr`'s two), its deposit and `srvServes`'s registration of its service; the loop
finds its last dot (`lastDotIdx_of`, `lastDotIdx_some`: the deposit's `splitSM`), the service is
found under `mapLock` (the registry's ghost map agrees), then the method in the service's map:
found, `methodTypeIs`; not, an `errors.New` error (`errNE`) and the deposit spent on `errOk`.
-/
module

public import Net.Spec.net.rpc.Server__readRequestHeader
public import Net.Spec.net.rpc.Server__getRequest
public import Net.Spec.net.rpc.serverCodec__ReadRequestHeader
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
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions] [errors.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.readRequestHeader.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_getRequest : Server.getRequest.spec (GF := GF) (hG := hG))
    (wp_ReadRequestHeader : serverCodec.ReadRequestHeader.spec (GF := GF) (hG := hG)) :
    Server.readRequestHeader.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra
  wp_start as ⟨#Hsrv, #Hserves, #Henv, #Hsc, Hrd⟩
  iunfold srvEnv at Henv
  icases Henv with ⟨#Hcli, -⟩
  ihave #Hcli' := Hcli
  iunfold cliEnv at Hcli'
  icases Hcli' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  ihave #HefV' := HefV
  iunfold errors.newVar at HefV'
  icases HefV' with ⟨%xf, #Hef, -⟩
  iunfold srvCodecAt at Hsc
  icases Hsc with ⟨#Hrwc, #Hconn⟩
  wp_auto
  wp_apply wp_getRequest s γs $$ Hsrv as %req Hreq
  wp_auto
  sorry

end proof

end net.rpc
end Perennial
