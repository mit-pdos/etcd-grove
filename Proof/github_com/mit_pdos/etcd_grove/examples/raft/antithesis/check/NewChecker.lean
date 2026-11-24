/-
Lean-first (no Rocq counterpart). #33 S3b W7 (2026-11-23): the proof of `NewChecker` (`check.go`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.NewChecker
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem NewChecker.wp_proof (wp_Init0 : Init0.spec (GF := GF) (hG := hG)) :
    NewChecker.spec (GF := GF) (hG := hG) := by
  intro cp cfg s
  wp_start as ⟨#Hc, %Hb, %Hs⟩
  wp_auto
  wp_apply wp_Init0 cp cfg s $$ [Hc] as %sp #Hsp
  · iframe Hc; ipureintro; exact ⟨Hs, Hb⟩
  try wp_auto
  iapply HΦ
  iunfold checkerOwn
  iexists _
  iframe «$r0»
  isplitr
  · iexact Hsp
  isplitl
  · iunfold verdictRO
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    · iapply Init0_strsNil
  · ipureintro; rfl

end proof

end AntCheck
end EtcdGrove
end Perennial
