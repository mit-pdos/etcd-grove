/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__prepareLog.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).prepareLog`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__prepareLog

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

theorem github_com.hashicorp.raft.Raft.prepareLog.wp_proof :
    github_com.hashicorp.raft.Raft.prepareLog.spec (GF := GF) (hG := hG) :=
  fun r l fp k e => by
  wp_start as ⟨#Hpv, #Hl, %Hk⟩
  unfold logPtr logIs
  icases Hl with ⟨%lv, #Hlv, %Hlv, #Hdata⟩
  iStructNamed Hlv
  have hT : lv.Type' = W8 0 ∧ e.kind = kCommand ∨ lv.Type' = W8 1 ∧ e.kind = kNoop ∨
      lv.Type' = W8 5 ∧ e.kind = kConfig ∨ lv.Type' = W8 4 ∧ e.kind = kBarrier := by
    obtain ⟨-, -, h⟩ := Hlv
    unfold kCommand kNoop kConfig kBarrier at Hk ⊢
    rcases Hk with h' | h' | h' | h' <;> rw [h'] at h
    · left; exact ⟨by word, h'⟩
    · right; left; exact ⟨by word, h'⟩
    · right; right; left; exact ⟨by word, h'⟩
    · right; right; right; exact ⟨by word, h'⟩
  rcases hT with ⟨hT, hk⟩ | ⟨hT, hk⟩ | ⟨hT, hk⟩ | ⟨hT, hk⟩ <;> simp only [hT]
  · wp_auto
    iapply HΦ; iright; iframe; ipureintro; left; exact hk
  · wp_auto
    iapply HΦ; ileft; ipureintro; exact ⟨hk, rfl⟩
  · wp_auto
    iapply HΦ; iright; iframe; ipureintro; right; left; exact hk
  · wp_auto
    iapply HΦ; iright; iframe; ipureintro; right; right; exact hk

end proof

end Perennial
