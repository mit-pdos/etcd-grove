/-
The proof of `Dial` (`Net/Spec/net/rpc/Dial.lean`): `net.Dial` with the library's `dial_au` (the
dialer's end and tokens, nothing for a failure), the connection registered in the world
(`rpc_register`, with the end's fresh token), then `NewClient`; a failure's error is an
`*OpError` (`errAny_resErr`).
-/
module

public import Net.Spec.net.rpc.Dial
public import Net.Spec.net.rpc.NewClient
public import Net.Spec.net.Dial
public import Net.Proof.net.rpc.ProtoGhost
public import Net.Proof.net.rpc.Errs

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
variable [π : NetProtoGS] [net.Assumptions]

theorem Dial.wp_proof (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_NewClient : NewClient.spec (GF := GF) (hG := hG)) :
    Dial.spec (GF := GF) (hG := hG) := by
  intro nw hnw W a
  wp_start as ⟨%Hbound, #Henv, #Haddr⟩
  iunfold rpcAddr at Haddr
  icases Haddr with ⟨#Hap, #Hreg⟩
  ihave %Hok := addrTok_ok $$ [Hap]
  · iapply addrProto_tok $$ Hap
  wp_auto
  wp_apply wp_Dial nw hnw a iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (reqProto W a) (respProto W a)
        [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn false)) $$ [Hap]
    as %c %err (⟨%Herr, %cn, #Hc, Hend, Hfresh⟩ | ⟨-, %x, -, #HE⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au $$ Hap
  · subst Herr
    iunfold net.isConn at Hc
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave Hr : (|={⊤}=> ∃ γ : RpcConnNames, isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
        monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗
        ghostMapAuth γ.nm 1 (∅ : GMap Nat (GName × GName × GName)) : IProp GF) $$ [Hfresh]
    · iapply rpc_register (Gg := hG.goose_globalGS) W a cn $$ [$Hreg $Hfresh]
    imod Hr with ⟨%γ, #Hrpc, Hreqs, Hnm⟩
    wp_auto
    wp_apply wp_NewClient W a cn γ t la ra $$ [$Henv $Hca Hrpc Hreqs Hnm Hsend Hrecv] as %cl Hcl
    · isplitr
      · ipureintro; exact Hbound
      iunfold rpcDialed
      iframe Hrpc Hreqs Hnm Hsend Hrecv
    iapply HΦ
    ileft
    iframe Hcl
    ipureintro; rfl
  · ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    have Hne' := Hne (by simp)
    obtain ⟨pe, rfl⟩ := Hne'
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iapply errAny_resErr $$ HE

end proof

end net.rpc
end Perennial
