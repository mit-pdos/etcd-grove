module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.seedOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.encodeV0
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.setItem
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem seedOne.wp_proof (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_encodeV0 : encodeV0.spec (GF := GF) (hG := hG))
    (wp_setItem : setItem.spec (GF := GF) (hG := hG)) :
    seedOne.spec (GF := GF) (hG := hG) := by
  intro _ _ cl x V γs s0 g k σ hAs hk hg
  wp_start as ⟨#Hnc, #Hwo, #Hregs, #Hsi, Hs, #Hst⟩
  wp_auto
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  (try wp_auto)
  wp_apply wp_storeKey
  (try wp_auto)
  wp_apply wp_encodeV0 as %vsl Hvsl
  (try wp_auto)
  wp_apply wp_bytes_to_string vsl _ _ $$ [Hvsl] as Hvsl
  · iexact Hvsl
  (try wp_auto)
  imod (client.srvStart_alloc (GF := GF) [x]) with #Hss
  ihave #Hidx := client.srvStart_idx [x] $$ Hss
  ihave #Hnil := EtcdGrove.optsAt_nil (GF := GF)
  ihave Hau : ([∧list] y ∈ [x], kvOpAu1 y.γr.kv
      (.put (linkv.putOp (go!"/registry" ++ storeKeyL k) (encodeWith tagV0 k go!"x")))
      (fun σ' => iprop(ghostVar γs (1 : Qp).half (kvOpStep
        (.put (linkv.putOp (go!"/registry" ++ storeKeyL k) (encodeWith tagV0 k go!"x"))) σ) ∗
        ⌜σ' = σ⌝))) $$ [Hs]
  · iapply BigAndL.bigAndL_singleton.2
    iapply seed_au γs x.γr.kv _ σ
    iframe Hsi Hs
  ihave #Hregs' : ([∗list] y ∈ [x], client.kvRegsAt y) $$ []
  · iapply BigSepL.bigSepL_singleton.2
    iexact Hregs
  ihave #Hput := client.kvRegs_put [x] $$ Hregs'
  wp_apply (client.client_Put_st cl [x] V context.backgroundCtxVal cd
      (go!"/registry" ++ storeKeyL k) (encodeWith tagV0 k go!"x") slice.nil
      (fun σ' => iprop(ghostVar γs (1 : Qp).half (kvOpStep
        (.put (linkv.putOp (go!"/registry" ++ storeKeyL k) (encodeWith tagV0 k go!"x"))) σ) ∗
        ⌜σ' = σ⌝))
      (opSizeOk_opPutModel (K := 2 ^ 28) (E := 0) (V := 2 ^ 28) (optsKeep_nil _ _ _)
        (by simp [storeKeyL]; omega) (by simp [encodeWith]; omega) (by decide)))
    $$ [Hau] as %resp %err Hout
  · simp only [List.map_cons, List.map_nil]
    iframe #
    iexact Hau
  icases Hout with (⟨%Herr, %m, %σ', #Hm, ⟨Hs, %Hσ'⟩, %Hrev⟩ | ⟨%Herr, -⟩)
  · subst Herr
    subst Hσ'
    iunfold putRespMsg at Hm
    icases Hm with ⟨%Hrn, %h, %pk, #Hhf, #Hh, #Hpk, -⟩
    iunfold hdrFull at Hh
    icases Hh with ⟨%Hhn, -, -, #Hrevf, -, -⟩
    wp_auto
    iunfold storeOwn at Hst
    icases Hst with ⟨#Hits, %Hrv⟩
    wp_apply wp_setItem _ _ _ _ $$ [] as %out ⟨-, Hout, -⟩
    · iframe #
      ipureintro; exact hg
    imod ownSlice_persist _ _ _ $$ Hout with #Hout
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    isplitl [Hs]
    · iExactEq Hs; rfl
    isplitr
    · iunfold storeOwn
      simp only
      rw [← Hrev.1]
      iframe Hout
      ipureintro; rfl
    ipureintro; exact Hrev.2
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      ileft
      ipureintro; rfl

end proof

end k8setcd3
end EtcdGrove
end Perennial
