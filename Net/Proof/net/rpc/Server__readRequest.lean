/-
The proof of `Server.readRequest` (`Net/Spec/net/rpc/Server__readRequest.lean`): the header
(`readRequestHeader`); after an error with the request taken, its body discarded
(`ReadRequestBody(nil)`: the reader advances by the frame, or its read fails, `rerr` then holding
the error); otherwise the method's `NewArg` (`methodOk`: an argument and its decoding), the body
decoded into it (`ReadRequestBody`, the request's argument bytes by `req_body`), and on a decoding
the deposit and the decoding turned into the call obligation, whose `NewReply` runs here
(`callObl`); a body that does not read or decode is an error (`rdErr`, `decErr`: messages not
empty) with the deposit spent on `errOk` (`errCont`). Two later credits: the body's protocol fact.
-/
module

public import Net.Spec.net.rpc.Server__readRequest
public import Net.Spec.net.rpc.Server__readRequestHeader
public import Net.Spec.net.rpc.serverCodec__ReadRequestBody
public import Net.Proof.net.rpc.ServerGhost

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
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.readRequest.wp_proof
    (wp_readRequestHeader : Server.readRequestHeader.spec (GF := GF) (hG := hG))
    (wp_ReadRequestBody : serverCodec.ReadRequestBody.spec (GF := GF) (hG := hG)) :
    Server.readRequest.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra
  wp_start as ⟨#Hsrv, #Hserves, #Henv, #Hsc, Hrd⟩
  ihave #Henv0 := Henv
  iunfold srvEnv at Henv0
  icases Henv0 with ⟨#Hcli, -⟩
  ihave #Hcli' := Hcli
  iunfold cliEnv at Hcli'
  icases Hcli' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  ihave #HefV' := HefV
  iunfold errors.newVar at HefV'
  icases HefV' with ⟨%xf, #Hef, -⟩
  ihave #Hsc0 := Hsc
  iunfold srvCodecAt at Hsc0
  icases Hsc0 with ⟨#Hrwc, #Hconn⟩
  wp_auto
  wp_apply wp_readRequestHeader s γs C W a sc t cn la ra $$ [$Hsrv $Hserves $Henv $Hsc $Hrd]
    as %svc %mt %req %keep %err Hres
  sorry

end proof

end net.rpc
end Perennial
