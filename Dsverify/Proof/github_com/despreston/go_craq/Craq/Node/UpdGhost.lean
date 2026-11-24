module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.UpdSpecs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Conn

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

section updghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem meta_noErr :
    go.typeSetContains (go.GoType.PointerType transport.NodeMeta.ty) go.error = false := by
  go_type_set

theorem meta_noStr :
    go.typeSetContains (go.GoType.PointerType transport.NodeMeta.ty) fmt.Stringer.ty = false := by
  go_type_set

theorem item_noErr :
    go.typeSetContains (go.GoType.PointerType store.Item.ty) go.error = false := by
  go_type_set

theorem item_noStr :
    go.typeSetContains (go.GoType.PointerType store.Item.ty) fmt.Stringer.ty = false := by
  go_type_set

instance itemPtr_persistent_u (p : Loc) (k : GoString) (v : w64) (x : GoString) :
    Persistent (itemPtr (hG := hG) p k v x) := by
  unfold itemPtr; infer_instance

theorem storeOwn_agree' (γs : GName) (q1 q2 : Qp) (S1 S2 : StoreS) :
    storeOwn (hG := hG) γs q1 S1 ∗ storeOwn γs q2 S2 ⊢ ⌜S1 = S2⌝ := by
  unfold storeOwn
  iintro ⟨H1, H2⟩
  iapply ghostVar_agree $$ H1 H2

/-- The fence: the active tail's token, with its cover by the node's log. -/
theorem fence_shift (HL : Laws (GF := GF)) (cfg : Cfg GF) (a : GoString) (γs : GName)
    (lat : GMap GoString w64) (S : StoreS) (HlatS : ∀ k, latOf lat k = S.maxCommitted k) :
    ⊢ inv nodeN (nodeInv cfg a γs) -∗ storeOwn γs (1 : Qp).half S -∗ tailRes cfg true lat -∗
      |={⊤}=> storeOwn γs (1 : Qp).half S ∗ ∃ L : CLog, tailTok cfg.γ L ∗ covers cfg.γ a L := by
  iintro #Hinv HS Htail
  unfold tailRes
  simp only [↓reduceIte]
  icases Htail with ⟨%L, HL', %HlatL⟩
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S', %Ln, HS', Hln, %HLn, #Hf⟩
  ihave %Heq := storeOwn_agree' γs _ _ S S' $$ [HS HS']
  · iframe
  subst Heq
  ihave ⟨Hln, #Hcov⟩ := HL.nlog_covers cfg.γ a Ln $$ Hln
  ihave #Hcov' := HL.covers_mono cfg.γ a Ln L (fun k => by rw [← HlatL k, HlatS k, HLn k]; omega)
    $$ Hcov
  imod Hclose $$ [HS' Hln] with -
  · inext
    iexists S, Ln
    iframe; iframe #
    ipureintro; exact HLn
  imodintro
  iframe HS
  iexists L
  iframe HL'
  iexact Hcov'

/-- With the tail token, the store's committed versions are at most the token's. -/
theorem tail_ub (HL : Laws (GF := GF)) (cfg : Cfg GF) (a : GoString) (γs : GName)
    (L : CLog) (S : StoreS) :
    ⊢ inv nodeN (nodeInv cfg a γs) -∗ storeOwn γs (1 : Qp).half S -∗ tailTok cfg.γ L -∗
      |={⊤}=> storeOwn γs (1 : Qp).half S ∗ tailTok cfg.γ L ∗
        ⌜∀ k, uint.Z (S.maxCommitted k) ≤ uint.Z (cvOf L k)⌝ := by
  iintro #Hinv HS HL'
  iinv Hinv with Hi Hclose
  unfold nodeInv
  imod Hi with ⟨%S', %Ln, HS', Hln, %HLn, #Hf⟩
  ihave %Heq := storeOwn_agree' γs _ _ S S' $$ [HS HS']
  · iframe
  subst Heq
  ihave %Hub : ⌜∀ k, uint.Z (S.maxCommitted k) ≤ uint.Z (cvOf L k)⌝ $$ [HL']
  · iintro %k
    rcases StoreS.maxCommitted_mem S k with h0 | ⟨x, hx⟩
    · ipureintro; rw [h0]; word
    · ihave #Hx := itemFacts_lookup cfg.γ S _ hx $$ Hf
      unfold itemFact
      icases Hx with ⟨-, #Hcv⟩
      simp only [↓reduceIte]
      iapply HL.tailTok_cvLb cfg.γ L k _ $$ [HL' Hcv]
      iframe HL' Hcv
  imod Hclose $$ [HS' Hln] with -
  · inext
    iexists S, Ln
    iframe; iframe #
    ipureintro; exact HLn
  imodintro
  iframe
  ipureintro; exact Hub

end updghost

end NodeP

end github_com.despreston.go_craq

end Perennial
