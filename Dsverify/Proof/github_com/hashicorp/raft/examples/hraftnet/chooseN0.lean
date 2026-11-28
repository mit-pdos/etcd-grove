/-
`hraftnet.chooseN0`'s proof: `3 + 2*rnd(2)`; its multiplication and addition are counted steps, each
with a receipt (`wp_go_step_receipt'`).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.chooseN0
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rnd

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem chooseN0.wp_proof (wp_rnd : rnd.spec (GF := GF)) : chooseN0.spec (GF := GF) := by
  wp_start as -
  wp_auto
  wp_apply +noauto (wp_rnd (W64 2) (by decide)) as %x %Hx
  wp_pure
  wp_bind (App (Val (GoInstruction (GoOp GoMul go.uint64))) (Val _))
  iapply wp_go_step_receipt'
  · rfl
  inext
  iintro Hr1 -
  iapply wp_value'
  wp_pure
  wp_bind (App (Val (GoInstruction (GoOp GoPlus go.uint64))) (Val _))
  iapply wp_go_step_receipt'
  · rfl
  inext
  iintro Hr2 -
  iapply wp_value'
  wp_auto
  iapply HΦ
  have hx : x = W64 0 ∨ x = W64 1 := by
    have : uint.Z x < 2 := Hx
    rcases (show uint.Z x = 0 ∨ uint.Z x = 1 by have := uint_Z_nonneg x; omega) with h | h
    · left; word
    · right; word
  iexists (if x = W64 0 then 3 else 5)
  isplitr
  · ipureintro
    rcases hx with rfl | rfl
    · exact ⟨by decide, Or.inl rfl⟩
    · exact ⟨by decide, Or.inr rfl⟩
  iapply (receipt_add 1 1).2
  iframe Hr1 Hr2
