/-
transport/netrpc: `NewNodeClient`, `NewCoordinatorClient` and the factory
(`netrpc.wp_NewNodeClient.spec`, `netrpc.factory.spec`, `netrpc.wp_NewCoordinatorClient.spec`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.NodeClient
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.CoordClient
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.Connect
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace netrpcP

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]
variable [rd : RpcHttpDial GF] [rc : RpcCallReply GF]


/-- The promoted `Connect` of a `*NodeClient`. -/
theorem wp_NodeClient_Connect (cfg : Cfg GF) (c cl : Loc) (a : GoString)
    (ha : a ∈ cfg.cAddr :: cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.NodeClient.mk cl ∗ cl ↦ transport.netrpc.Client.mk null ⊢
    ∀ Φ : val → IProp GF,
      ▷ (∀ err : GoInterface, ((⌜err = interface.nil⌝ ∗ connected cfg cl a) ∨
          models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.NodeClient.ty) go!"Connect" #c))
        (Val #a)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, Hcl⟩ %Φ HΦ
  iStructNamed Hc
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc $$ [Henv]
  · unfold env; icases Henv with ⟨H, -⟩; iexact H
  wp_method_call
  wp_call
  wp_auto
  ihave Hw := wp_Client_Connect cfg cl a ha $$ [Hcl]
  · isplitr
    · iexact Henv
    · iexact Hcl
  iapply Hw
  inext; iexact HΦ

theorem wp_NewNodeClient (HencE : enc_EmptyArgs.spec (GF := GF)) (HencW : enc_WriteArgs.spec (GF := GF))
    (HencC : enc_CommitArgs.spec (GF := GF)) (HencS : enc_string.spec (GF := GF))
    (HencM : enc_NodeMeta.spec (GF := GF)) (HencP : enc_PropagateRequest.spec (GF := GF))
    (HdecE : dec_EmptyReply.spec (GF := GF)) (HdecV : dec_VersionResponse.spec (GF := GF))
    (HdecI : dec_Item.spec (GF := GF)) (HdecP : dec_PropagateResponse.spec (GF := GF)) :
    netrpc.wp_NewNodeClient.spec (GF := GF) := by
  intro cfg
  wp_start as ⟨Hready, #Hctx⟩
  unfold rpcReady
  icases Hready with ⟨#Hrpkg, #Hcs⟩
  iapply wp_fupd
  wp_auto
  wp_alloc c as Hc
  wp_auto
  ipersist Hc
  imodintro
  iapply HΦ
  unfold freshNodeClient
  iexists ⟨go.GoType.PointerType transport.netrpc.NodeClient.ty, #c⟩
  isplitr
  · ipureintro; rfl
  iintro %a %Φ' %ha HΦ'
  rw [show (zero_val transport.netrpc.Client) = transport.netrpc.Client.mk null from rfl]
  ihave #Henv : env cfg $$ []
  · unfold env rpcReady
    isplitr
    · iexact Hpkg
    isplitr
    · isplitr
      · iexact Hrpkg
      · iexact Hcs
    · iexact Hctx
  ihave Hw := wp_NodeClient_Connect cfg c «$v0_ptr» a (List.mem_cons_of_mem _ ha) $$ [«$v0»]
  · isplitr
    · iexact Henv
    isplitr
    · iexact Hc
    · iexact «$v0»
  iapply Hw
  inext
  iintro %err Hres
  iapply HΦ'
  icases Hres with (⟨%He, #Hcon⟩ | #Hany)
  · ileft
    isplitr
    · ipureintro; exact He
    iapply isNodeClient_of HencE HencW HencC HencS HencM HencP HdecE HdecV HdecI HdecP cfg c
      «$v0_ptr» a ha
    isplitr
    · iexact Henv
    isplitr
    · iexact Hc
    · iexact Hcon
  · iright; iexact Hany

theorem factory (HencE : enc_EmptyArgs.spec (GF := GF)) (HencW : enc_WriteArgs.spec (GF := GF))
    (HencC : enc_CommitArgs.spec (GF := GF)) (HencS : enc_string.spec (GF := GF))
    (HencM : enc_NodeMeta.spec (GF := GF)) (HencP : enc_PropagateRequest.spec (GF := GF))
    (HdecE : dec_EmptyReply.spec (GF := GF)) (HdecV : dec_VersionResponse.spec (GF := GF))
    (HdecI : dec_Item.spec (GF := GF)) (HdecP : dec_PropagateResponse.spec (GF := GF)) :
    netrpc.factory.spec (GF := GF) := by
  intro cfg
  iintro ⟨#Hpkg, Hready, #Hctx⟩
  unfold rpcReady
  icases Hready with ⟨#Hrpkg, #Hcs⟩
  unfold isFactory
  imodintro
  iintro %Φ HΦ
  wp_apply (wp_NewNodeClient HencE HencW HencC HencS HencM HencP HdecE HdecV HdecI HdecP cfg)
    as %c Hc
  · unfold rpcReady
    isplitr
    · isplitr
      · iexact Hrpkg
      · iexact Hcs
    · iexact Hctx
  iapply HΦ $$ Hc

/-- The promoted `Connect` of a `*CoordinatorClient`. -/
theorem wp_CoordClient_Connect (cfg : Cfg GF) (c cl : Loc) (a : GoString)
    (ha : a ∈ cfg.cAddr :: cfg.chain) :
    env cfg ∗ c ↦□ transport.netrpc.CoordinatorClient.mk cl ∗
      cl ↦ transport.netrpc.Client.mk null ⊢
    ∀ Φ : val → IProp GF,
      ▷ (∀ err : GoInterface, ((⌜err = interface.nil⌝ ∗ connected cfg cl a) ∨
          models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.CoordinatorClient.ty) go!"Connect" #c))
        (Val #a)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, Hcl⟩ %Φ HΦ
  iStructNamed Hc
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.transport.netrpc $$ [Henv]
  · unfold env; icases Henv with ⟨H, -⟩; iexact H
  wp_method_call
  wp_call
  wp_auto
  ihave Hw := wp_Client_Connect cfg cl a ha $$ [Hcl]
  · isplitr
    · iexact Henv
    · iexact Hcl
  iapply Hw
  inext; iexact HΦ

theorem wp_NewCoordinatorClient (HencS : enc_string.spec (GF := GF))
    (HencCW : enc_ClientWriteArgs.spec (GF := GF)) (HdecM : dec_NodeMeta.spec (GF := GF))
    (HdecE : dec_EmptyReply.spec (GF := GF)) :
    netrpc.wp_NewCoordinatorClient.spec (GF := GF) := by
  intro cfg
  wp_start as ⟨Hready, #Hctx⟩
  unfold rpcReady
  icases Hready with ⟨#Hrpkg, #Hcs⟩
  iapply wp_fupd
  wp_auto
  wp_alloc c as Hc
  wp_auto
  ipersist Hc
  imodintro
  iapply HΦ
  unfold freshCoordClient
  iexists ⟨go.GoType.PointerType transport.netrpc.CoordinatorClient.ty, #c⟩
  isplitr
  · ipureintro; rfl
  iintro %Φ' HΦ'
  rw [show (zero_val transport.netrpc.Client) = transport.netrpc.Client.mk null from rfl]
  ihave #Henv : env cfg $$ []
  · unfold env rpcReady
    isplitr
    · iexact Hpkg
    isplitr
    · isplitr
      · iexact Hrpkg
      · iexact Hcs
    · iexact Hctx
  ihave Hw := wp_CoordClient_Connect cfg c «$v0_ptr» cfg.cAddr List.mem_cons_self $$ [«$v0»]
  · isplitr
    · iexact Henv
    isplitr
    · iexact Hc
    · iexact «$v0»
  iapply Hw
  inext
  iintro %err Hres
  iapply HΦ'
  icases Hres with (⟨%He, #Hcon⟩ | #Hany)
  · ileft
    isplitr
    · ipureintro; exact He
    iapply isCoordClient_of HencS HencCW HdecM HdecE cfg c «$v0_ptr»
    isplitr
    · iexact Henv
    isplitr
    · iexact Hc
    · iexact Hcon
  · iright; iexact Hany

end proofs
end netrpcP
end github_com.despreston.go_craq
end Perennial
