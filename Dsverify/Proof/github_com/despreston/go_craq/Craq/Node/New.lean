module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section newp
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

theorem node.wp_New : node.wp_New.spec (GF := GF) (hG := hG) := by
  intro cfg a st γs f cc
  wp_start as ⟨#Hctx, %Ha, Hres, #Hst, HS, #Hfac, Hcc⟩
  wp_auto
  wp_apply LogHyp.wp_Default as %lg -
  wp_apply (wp_map_make1 (K := GoString) (V := w64)) as %latM Hlatm
  wp_apply +noauto (wp_map_make2 (K := w64) (V := node.neighbor)) as %nbM Hnbm
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  ipersist neighbors
  ipersist store
  ipersist latest
  ipersist committed
  ipersist cdrAddress
  ipersist address
  ipersist pubAddr
  ipersist cdr
  ipersist transport
  ipersist log
  unfold nodeRes
  icases Hres with ⟨Hrole, Hnlog⟩
  unfold storeOwn
  icases (ghostVar_split_half γs (1 : Qp).half ([] : StoreS)).1 $$ HS with ⟨HS1, HS2⟩
  imod inv_alloc NodeP.nodeN ⊤ (NodeP.nodeInv cfg a γs) $$ [HS1 Hnlog] with #Hinv
  · inext
    unfold NodeP.nodeInv
    iexists [], []
    unfold storeOwn
    iframe
    isplitr
    · ipureintro; intro k; rfl
    unfold NodeP.itemFacts
    iapply (BI.BigSepL.bigSepL_nil_intro (P := iprop(True)))
    itrivial
  imod sync.init_Mutex (NodeP.lockInv cfg a γs «$r0_ptr» nbM latM) ⊤ _ $$ [mu] [HS2 Hrole Hlatm Hnbm IsHead IsTail] with #Hmu
  · iexact mu
  · inext
    unfold NodeP.lockInv NodeP.lockedState
    iexists false, false, ∅, ∅, []
    unfold storeOwn
    have hn : NodeP.nextAddr (∅ : GMap w64 node.neighbor) = go!"" := rfl
    rw [hn]
    iframe
    isplitr
    · iapply (BI.BigSepM.bigSepM_empty_intro (P := iprop(True)))
      itrivial
    isplitr
    · ipureintro; intro k; rfl
    unfold NodeP.tailRes; simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  imodintro
  iapply HΦ
  unfold isNode nodeStartRes NodeP.isNodeDef NodeP.nodeFields NodeP.startResDef
  iframe; iframe #
  ipureintro; exact ⟨Ha, rfl⟩
  done

end newp

end github_com.despreston.go_craq

end Perennial
