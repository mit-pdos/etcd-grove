/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__processConfigurationLogEntry.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).processConfigurationLogEntry`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processConfigurationLogEntry
public import Dsverify.Spec.github_com.hashicorp.raft.DecodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration

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

theorem github_com.hashicorp.raft.Raft.processConfigurationLogEntry.wp_proof
    (wp_DecodeConfiguration : github_com.hashicorp.raft.DecodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_setCommittedConfiguration :
      github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration :
      github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.processConfigurationLogEntry.spec (GF := GF) (hG := hG) := by
  intro b r γ p lv dq c0 l i0 li p0
  wp_start as ⟨Hp, %Hty, Hc, Hcase⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hnn⟩
  iStructNamed Hp
  wp_auto
  wp_if_destruct
  · -- a configuration entry
    icases Hcase with (%Hne | ⟨⟨%ss, #Hd, %Hss⟩, Hb⟩)
    · exact absurd Hif Hne
    wp_apply wp_setCommittedConfiguration r c0 l i0 li l li $$ [$Hc] as Hc
    wp_apply wp_DecodeConfiguration lv.Data' ss DFrac.discard $$ [$Hd] as %c ⟨-, Hcs⟩
    cases b
    · wp_apply wp_setLatestConfiguration false r γ l l li li c lv.Index' ss (DFrac.own 1) p0 $$ [$Hc $Hcs Hb]
        as ⟨Hc, Hcs, -⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iframe Hb; ipureintro; exact Or.inr Hss
      iapply HΦ
      isplitl [Index Term Type' Data Extensions AppendedAt]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iright
      iexists c, ss
      iframe Hc Hcs Hd
      simp only [Bool.false_eq_true, ↓reduceIte]
      ipureintro; exact ⟨⟨Hif, Hss⟩, trivial⟩
    · wp_apply wp_setLatestConfiguration true r γ l l li li c lv.Index' ss (DFrac.own 1) p0 $$ [$Hc $Hcs Hb]
        as ⟨Hc, Hcs, Hb⟩
      · simp only [↓reduceIte]; iframe Hb
      iapply HΦ
      isplitl [Index Term Type' Data Extensions AppendedAt]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      iright
      iexists c, ss
      iframe Hc Hcs Hd
      isplitr; · ipureintro; exact ⟨Hif, Hss⟩
      simp only [↓reduceIte]; iframe Hb
  · repeat' wp_if_destruct
    · exact absurd Hif Hty.2
    · exact absurd Hif Hty.1
    · iapply HΦ
      isplitl [Index Term Type' Data Extensions AppendedAt]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ileft
      iframe Hc
      ipureintro; assumption

end proof

end Perennial
