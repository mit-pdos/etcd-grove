module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Ping
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.LatestVersion
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Read
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Write
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Propagate
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.ReqProp
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Update
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.New
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Start

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section svc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

theorem sendCommitToPrev_ok : sendCommitToPrev.spec (GF := GF) (hG := hG) := by
  intro cfg n a st γs nbM latM prev k v hk
  iintro %Φ ⟨#Hpkg, #Hctx, #Hf, #Hnb, #Hcv⟩ HΦ
  iunfold nodeFields at Hf
  icases Hf with ⟨%f, %lg, %ch, -, -, -, -, -, -, -, #Hlog, -, %Hch, -⟩
  wp_apply wp_sendCommitToPrev cfg n lg Hch.2 prev k v hk $$ Hpkg Hlog Hnb Hcv
  iintro %err -
  iapply HΦ

theorem wp_Update (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (ptr : Loc) (dq : DFrac) (m : MetaV) (r : Role) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ ⌜metaAddrsOk cfg.chain m⌝ -∗ metaPtr ptr dq m -∗ roleHalf cfg.γ a r -∗
      updDep cfg.γ r m -∗
      ▷ (∀ err : GoInterface, metaPtr ptr dq m -∗
          (⌜err = interface.nil⌝ ∗ updPost cfg.γ a r m ∨ errNE err) -∗ Φ #err) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"Update" #n)) (Val #ptr))
        {{ Φ }} := by
  iintro #Hpkg #Hn %Hm Hmp Hr Hdep HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_update HL sendCommitToPrev_ok (wp_requestFwdPropagation HL)
    (wp_requestBackPropagation HL) cfg n a ptr dq m r) $$ [Hmp Hr Hdep]
    as %err Hmp Hres
  · iframe; iframe #; ipureintro; exact Hm
  icases Hres with (⟨%Herr, Hpost⟩ | #Herr)
  · subst Herr
    wp_auto
    iapply HΦ $$ Hmp
    ileft; iframe; ipureintro; rfl
  · ihave %Hok := errAny_ok err $$ Herr
    obtain ⟨ei, rfl⟩ := Hok
    wp_auto
    unfold models_lab.errAny
    icases Herr with ⟨%ei', %Hei, -, #HE⟩
    cases Hei
    wp_apply HE
    iintro %msg
    wp_auto
    wp_apply wp_errorsNew_NE _ (by simp)
    iintro %err' Herr'
    wp_auto
    iapply HΦ $$ Hmp
    iright; iexact Herr'

end svc

end NodeP

section final
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- The node is its service (every clause of `isNodeSvc`). -/
theorem node.node_svc (HL : NodeP.Laws (GF := GF)) : node.node_svc.spec (GF := GF) (hG := hG) := by
  intro cfg n a
  iintro ⟨#Hpkg, #Hn⟩
  unfold isNodeSvc ptrIface
  iexists _
  isplit
  · ipureintro; rfl
  imodintro
  dsimp only
  isplit
  · iintro %Φ HΦ
    iapply NodeP.wp_Ping n Φ $$ Hpkg HΦ
  isplit
  · iintro %ptr %dq %m %r %Φ %Hm Hmp Hr Hdep HΦ
    iapply NodeP.wp_Update HL cfg n a ptr dq m r Φ $$ Hpkg Hn [] Hmp Hr Hdep HΦ
    ipureintro; exact Hm
  isplit
  · iintro %k %sl %x %v %Φ #Hsl #Hve HΦ
    iapply NodeP.wp_Write HL cfg n a k sl x v Φ $$ Hpkg Hn Hsl Hve HΦ
  isplit
  · iintro %k %v %Φ #Hcv HΦ
    iapply NodeP.wp_Commit HL cfg n a k v Φ $$ Hpkg Hn Hcv HΦ
  isplit
  · iintro %k %Q %Φ Hau HΦ
    iapply NodeP.wp_LatestVersion HL.read cfg n a k Q Φ $$ Hpkg Hn Hau HΦ
  isplit
  · iintro %k %Q %Φ %hk Hau HΦ
    iapply NodeP.wp_Read HL cfg n a k Q Φ hk $$ Hpkg Hn Hau HΦ
  isplit
  · iintro %ptr %dq %req %Φ Hreq HΦ
    iapply NodeP.wp_FwdPropagate HL cfg n a ptr dq req Φ $$ Hpkg Hn Hreq HΦ
  · iintro %ptr %dq %req %L %Φ Hreq #Hcov HΦ
    iapply NodeP.wp_BackPropagate HL cfg n a ptr dq req L Φ $$ Hpkg Hn Hreq Hcov HΦ

end final

end github_com.despreston.go_craq

end Perennial
