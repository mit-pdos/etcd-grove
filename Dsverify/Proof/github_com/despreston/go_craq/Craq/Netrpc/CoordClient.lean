/-
transport/netrpc: the methods of a connected `*CoordinatorClient`. `Write` is proved in the
corrected form of hub request H2 (`notes/hub-requests.md`): `wp_CWrite_fixed`.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.Defs

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
variable [rcs : RpcClientSpecs GF]


theorem wp_AddNode (Henc : enc_string.spec (GF := GF)) (Hdec : dec_NodeMeta.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) :
    env cfg ∗ c ↦□ transport.netrpc.CoordinatorClient.mk cl ∗ connected cfg cl cfg.cAddr ⊢
    ∀ (a : GoString) (Φ : val → IProp GF), ⌜a ∈ cfg.chain⌝ -∗ joinTicket cfg.γ a -∗
      ▷ (∀ (p : Loc) (err : GoInterface), (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗
          Φ (PairV #p #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.CoordinatorClient.ty) go!"AddNode" #c)) (Val #a)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %a %Φ %ha Htk HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  rw [show zero_val transport.NodeMeta = transport.NodeMeta.mk false false go!"" go!"" go!"" from rfl]
  wp_apply (wp_Call_tag (HT := fun rep => BI.pure_mono (fun h => h rfl)) (tagOk go!"github.com/despreston/go-craq/transport.NodeMeta")
    r cfg.W cfg.cAddr go!"RPC.AddNode" go!"RPC" go!"AddNode"
    (coordSpec cfg.γ cfg.chain) _ _ (fun rep msg => iprop(⌜msg = [] → tagOk go!"github.com/despreston/go-craq/transport.NodeMeta" rep⌝)) iprop(True)
    (metaPtr «$r0_ptr» (DFrac.own 1) ⟨false, false, go!"", go!"", go!""⟩)
    (fun _ _ => iprop(∃ m : MetaV, metaPtr «$r0_ptr» (DFrac.own 1) m))) $$ [Htk «$r0»]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_coord cfg Hss.1, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [Htk]
    · iapply Henc a
      rw [coordSpec_AddNode]
      isplitl
      · iexists a
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, ha⟩
        isplit
        · iintro %md; ipureintro; intro _; exact tagOk_Meta md
        · unfold errOk; iintro %_ %_; ipureintro; intro _; exact tagOk_nil _
      · ipureintro; trivial
    isplitl [«$r0»]
    · unfold metaPtr; iexact «$r0»
    · imodintro
      iintro Hrp %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hok
      iexact Hok
  iintro %err Hpost
  icases Hpost with (⟨%Herr, -⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -⟩ | ⟨%Herr, #Hany, -⟩)
  · wp_auto
    iapply HΦ; ileft; ipureintro; exact Herr
  · wp_auto
    iapply HΦ; iright; iapply errMsg_errAny; iexact Hmsg
  · wp_auto
    iapply HΦ; iright; iexact Hany

/-- The coordinator client's `Write`, H2's form. -/
theorem wp_CWrite_fixed (Henc : enc_ClientWriteArgs.spec (GF := GF))
    (Hdec : dec_EmptyReply.spec (GF := GF)) (cfg : Cfg GF) (c cl : Loc) :
    env cfg ∗ c ↦□ transport.netrpc.CoordinatorClient.mk cl ∗ connected cfg cl cfg.cAddr ⊢
    ∀ (k : GoString) (sl : GoSlice) (dq : DFrac) (x : GoString)
        (Q : KvM.Output → IProp GF) (Φ : val → IProp GF),
      sl ↦*{dq} x -∗ opAU cfg.γ (.put k x) Q -∗
      ▷ (∀ err : GoInterface,
          (⌜err = interface.nil⌝ ∗ sl ↦*{dq} x ∗ putReceipt k x Q) ∨ models_lab.errAny err -∗
          Φ #err) -∗
      WP (App (App (Val #(methods (go.GoType.PointerType transport.netrpc.CoordinatorClient.ty) go!"Write" #c)) (Val #k)) (Val #sl)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %k %sl %dq %x %Q %Φ Hsl HAU HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_alloc pr as Hpr
  wp_auto
  wp_apply (wp_Call_tag (HT := fun rep => by iintro ⟨%h, -⟩; ipureintro; exact h rfl) (tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply")
    r cfg.W cfg.cAddr go!"RPC.Write" go!"RPC" go!"Write"
    (coordSpec cfg.γ cfg.chain) _ _
    (fun rep msg => iprop(⌜msg = [] → tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply" rep⌝ ∗ (⌜msg = []⌝ -∗ putReceipt k x Q)))
    (sl ↦*{dq} x)
    (pr ↦ transport.netrpc.EmptyReply.mk) (fun _ _ => pr ↦ transport.netrpc.EmptyReply.mk))
    $$ [args Hsl HAU Hpr]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_coord cfg Hss.1, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitl [args Hsl HAU]
    · iapply Henc args_ptr (DFrac.own 1) k sl dq x
      iframe
      iintro _ Hsl
      iframe
      rw [coordSpec_Write]
      iexists k, x, Q
      iframe
      isplitr
      · ipureintro; rfl
      isplit
      · iintro Hrc
        isplitr
        · ipureintro; intro _; exact tagOk_EmptyReply
        iintro %_; iexact Hrc
      · unfold errOk; iintro %_ %Hne
        isplitr
        · ipureintro; intro _; exact tagOk_nil _
        iintro %Heq; exact absurd Heq Hne
    isplitl [Hpr]
    · iexact Hpr
    · imodintro
      iintro Hpr %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hpr
      iexact Hpr
  iintro %err Hpost
  icases Hpost with (⟨%Herr, Hsl, %rep, ⟨-, Hrc⟩, -⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -⟩ | ⟨%Herr, #Hany, -⟩)
  · wp_auto
    iapply HΦ; ileft
    isplitr
    · ipureintro; exact Herr
    iframe
    iapply Hrc; ipureintro; rfl
  · wp_auto
    iapply HΦ; iright; iapply errMsg_errAny; iexact Hmsg
  · wp_auto
    iapply HΦ; iright; iexact Hany

/-- The coordinator client's `RemoveNode` (any address; the caller learns nothing). -/
theorem wp_CRemoveNode (Henc : enc_string.spec (GF := GF)) (Hdec : dec_EmptyReply.spec (GF := GF))
    (cfg : Cfg GF) (c cl : Loc) :
    env cfg ∗ c ↦□ transport.netrpc.CoordinatorClient.mk cl ∗ connected cfg cl cfg.cAddr ⊢
    ∀ (a : GoString) (Φ : val → IProp GF),
      ▷ (∀ err : GoInterface, (⌜err = interface.nil⌝ ∨ models_lab.errAny err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.CoordinatorClient.ty) go!"RemoveNode" #c)) (Val #a)) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %a %Φ HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_alloc pr as Hpr
  wp_auto
  wp_apply (wp_Call_tag (HT := fun rep => BI.pure_mono (fun h => h rfl)) (tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply")
    r cfg.W cfg.cAddr go!"RPC.RemoveNode" go!"RPC" go!"RemoveNode"
    (coordSpec cfg.γ cfg.chain) _ _ (fun rep msg => iprop(⌜msg = [] → tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply" rep⌝)) iprop(True)
    (pr ↦ transport.netrpc.EmptyReply.mk) (fun _ _ => pr ↦ transport.netrpc.EmptyReply.mk))
    $$ [Hpr]
  · isplitr
    · iexact Hr
    isplitr
    · ipureintro; exact ⟨by decide, ss_coord cfg Hss.1, by intro h; cases h⟩
    isplitr
    · iexact Hcs
    isplitr
    · iapply Henc a
      rw [coordSpec_RemoveNode]
      isplitl
      · iexists a
        isplitr
        · ipureintro; rfl
        isplit
        · ipureintro; intro _; exact tagOk_EmptyReply
        · iintro %_; ipureintro; intro _; exact tagOk_nil _
      · ipureintro; trivial
    isplitl [Hpr]
    · iexact Hpr
    · imodintro
      iintro Hpr %rep %HT
      iapply Hdec
      isplitr
      · ipureintro; exact HT
      iframe
      iintro %ok Hpr
      iexact Hpr
  iintro %err Hpost
  icases Hpost with (⟨%Herr, -⟩ | ⟨%msg, ⟨%Hne, %Herr⟩, #Hmsg, -⟩ | ⟨%Herr, #Hany, -⟩)
  · wp_auto
    iapply HΦ; ileft; ipureintro; exact Herr
  · wp_auto
    iapply HΦ; iright; iapply errMsg_errAny; iexact Hmsg
  · wp_auto
    iapply HΦ; iright; iexact Hany

/-- The coordinator client's `Close`. -/
theorem wp_CClose (cfg : Cfg GF) (c cl : Loc) :
    env cfg ∗ c ↦□ transport.netrpc.CoordinatorClient.mk cl ∗ connected cfg cl cfg.cAddr ⊢
    ∀ Φ : val → IProp GF, ▷ (∀ err : GoInterface, Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType transport.netrpc.CoordinatorClient.ty) go!"Close" #c)) (Val #())) {{ Φ }} := by
  iintro ⟨#Henv, #Hc, #Hcl⟩ %Φ HΦ
  unfold connected
  icases Hcl with ⟨%r, #Hcl, #Hr⟩
  iStructNamed Hc
  unfold env rpcReady craqCtx
  icases Henv with ⟨#Hpkg, ⟨#Hrpkg, #Hcs, -⟩, #Hcraq, %Hss, #Haddrs⟩
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply rcs.close r cfg.W cfg.cAddr $$ [Hrpkg Hr] as %err -
  · iexact Hr
  iapply HΦ

/-- A connected coordinator client meets `isCoordClient` (its `Write` clause is netrpc-H2's text, applied on main 3a5198e). -/
theorem isCoordClient_of (HencS : enc_string.spec (GF := GF))
    (HencCW : enc_ClientWriteArgs.spec (GF := GF)) (HdecM : dec_NodeMeta.spec (GF := GF))
    (HdecE : dec_EmptyReply.spec (GF := GF)) (cfg : Cfg GF) (c cl : Loc) :
    env cfg ∗ c ↦□ transport.netrpc.CoordinatorClient.mk cl ∗ connected cfg cl cfg.cAddr ⊢
    isCoordClient cfg (interface.mkOk (go.GoType.PointerType transport.netrpc.CoordinatorClient.ty) #c) := by
  iintro #H
  unfold isCoordClient
  iexists ⟨go.GoType.PointerType transport.netrpc.CoordinatorClient.ty, #c⟩
  isplitr
  · ipureintro; rfl
  imodintro
  isplit
  · iapply wp_AddNode HencS HdecM cfg c cl $$ H
  isplit
  · iapply wp_CWrite_fixed HencCW HdecE cfg c cl $$ H
  isplit
  · iapply wp_CClose cfg c cl $$ H
  · iapply wp_CRemoveNode HencS HdecE cfg c cl $$ H

end proofs
end netrpcP
end github_com.despreston.go_craq
end Perennial
