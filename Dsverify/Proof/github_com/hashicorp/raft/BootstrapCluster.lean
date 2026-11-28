/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/BootstrapCluster.lean (241f27e).
-/
/-
The proof of `raft.BootstrapCluster`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.BootstrapCluster
public import Dsverify.Spec.github_com.hashicorp.raft.ValidateConfig
public import Dsverify.Spec.github_com.hashicorp.raft.checkConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.HasExistingState
public import Dsverify.Spec.github_com.hashicorp.raft.EncodeConfiguration
public import Dsverify.Proof.github_com.hashicorp.raft.EncodingLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.BootstrapCluster.wp_proof
    (wp_ValidateConfig : github_com.hashicorp.raft.ValidateConfig.spec (GF := GF) (hG := hG))
    (wp_checkConfiguration : github_com.hashicorp.raft.checkConfiguration.spec (GF := GF) (hG := hG))
    (wp_HasExistingState : github_com.hashicorp.raft.HasExistingState.spec (GF := GF) (hG := hG))
    (wp_EncodeConfiguration :
      github_com.hashicorp.raft.EncodeConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.BootstrapCluster.spec (GF := GF) (hG := hG) := by
  intro Wl Ws Qc cp c logsI stableI snapsI trans cfgv ss dq γ i ownL ownS ownSS eof sst tid
  wp_start as ⟨Hcp, %Hcfg, #Hlog, #Hst, #Hsn, Hss, %Hsrv, HL, HS, %Hct, HSS, HWs, HWl, Htok⟩
  ihave #Hglob := pkgGlobals_of_isPkgInit $$ Hpkg
  unfold pkgGlobals
  icases Hglob with ⟨-, ⟨%kCT, #HkCT, #HkCTs⟩, -, -, -⟩
  wp_auto
  wp_apply wp_ValidateConfig $$ [$Hcp] as Hcp
  · ipureintro; exact Hcfg
  obtain ⟨⟨Hids, -, Hall, Hvne, -⟩, -, -⟩ := Hsrv
  wp_apply wp_checkConfiguration $$ [$Hss] as %err ⟨Hss, Herr⟩
  · ipureintro
    exact ⟨fun s hs => ⟨(Hall s hs).2.1, (Hall s hs).2.2.1⟩, Hids⟩
  ihave %Herr' : (⌜err = interface.nil⌝ : IProp GF) $$ [Herr]
  · icases Herr with (%Herr | ⟨%Hv, -⟩)
    · ipureintro; exact Herr.1
    · exact absurd Hv Hvne
  subst Herr'
  wp_auto
  wp_apply (wp_HasExistingState Wl Ws Qc logsI stableI snapsI γ i ownL ownS ownSS eof sst tid)
    $$ [$HL $HS $HSS $Htok] as ⟨HL, HS, HSS, Htok⟩
  · iframe #; ipureintro; exact Hct
  unfold isStableStore
  icases Hst with ⟨-, #HSetU, -, -⟩
  wp_bind (App (App (Val #(methods _ _ _)) _) _)
  iapply HSetU $$ HkCTs HWs
  iintro HWs
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  inext
  iexists sst
  iframe HS
  iintro HS
  imod Hclose
  imodintro
  wp_auto
  rw [decide_eq_false (by rw [Hcfg.1]; decide)]
  wp_auto
  simp only [LogConfiguration]
  wp_auto
  wp_apply wp_EncodeConfiguration $$ [$Hss] as %bs ⟨Hss, Hbs⟩
  irename «$r0» => He
  imod ownSlice_persist $$ Hbs with #Hbs
  ipersist He
  unfold isLogStore
  icases Hlog with ⟨-, -, -, -, #HStoreLog, -⟩
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HStoreLog $$ %«$r0_ptr» %1 %(genesisOf ss) [] [] HWl
  · ipureintro; omega
  · unfold logPtr
    iexists _
    iframe #
    unfold logIs
    isplitr
    · ipureintro; simp [genesisOf, kConfig]
    isplitr
    · simp only [genesisOf]; iexact Hbs
    · iexists []
      iapply ownSlice_nil
  iintro HWl
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  inext
  iexists LogAbs.empty
  iframe HL
  iintro HL
  imod Hclose
  imodintro
  wp_auto
  iapply HΦ
  iframe

end proof

end Perennial
