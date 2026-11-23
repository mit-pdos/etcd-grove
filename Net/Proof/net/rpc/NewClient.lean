/-
The proof of `NewClient` (`Net/Spec/net/rpc/NewClient.lean`): `newClientCodec`, then
`NewClientWithCodec`.
-/
module

public import Net.Spec.net.rpc.NewClient
public import Net.Spec.net.rpc.NewClientWithCodec
public import Net.Spec.net.rpc.newClientCodec

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

theorem NewClient.wp_proof (wp_newClientCodec : newClientCodec.spec (GF := GF) (hG := hG))
    (wp_NewClientWithCodec : NewClientWithCodec.spec (GF := GF) (hG := hG)) :
    NewClient.spec (GF := GF) (hG := hG) := by
  intro W a cn γ t la ra
  wp_start as ⟨%Hbound, #Henv, #Hconn, Hdial⟩
  wp_auto
  wp_apply wp_newClientCodec as %cc ⟨Hrwc, Hwerr⟩
  ipersist Hrwc
  wp_apply wp_NewClientWithCodec W a cn γ cc t la ra $$ [$Henv $Hrwc $Hwerr $Hconn $Hdial]
    as %c Hc
  · ipureintro; exact Hbound
  iapply HΦ $$ Hc

end proof

end net.rpc
end Perennial
