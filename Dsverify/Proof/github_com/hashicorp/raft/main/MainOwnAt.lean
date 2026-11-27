/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/main/MainOwnAt.lean (241f27e).
-/
/-
`mainOwnAt` is now defined in core/Defs.lean (review R1); this file keeps the two lemmas
`mainOwn_unfold : mainOwn = ∃ s st, mainOwnAt s st` and `mainOwnAt_mainOwn`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Defs

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

theorem mainOwn_unfold (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) :
    mainOwn r γ rc i ⊣⊢ ∃ (s : SState) (st : w32), mainOwnAt r γ rc i s st ∗
      (⌜st ≠ stLeader⌝ ∨ len0Is γ s.term s.log.length ∗ ccfgOwn γ i s.term (lastCfgIdx s.log)) := by
  unfold mainOwn
  exact .rfl

theorem mainOwn_intro (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState)
    (st : w32) : mainOwnAt r γ rc i s st ∗
      (⌜st ≠ stLeader⌝ ∨ len0Is γ s.term s.log.length ∗ ccfgOwn γ i s.term (lastCfgIdx s.log)) ⊢
      mainOwn r γ rc i := by
  iintro H
  iapply (mainOwn_unfold r γ rc i).2
  iexists s, st
  iexact H

/-- Outside the state `Leader`. -/
theorem mainOwnAt_mainOwn (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState)
    (st : w32) (h : st ≠ stLeader) : mainOwnAt r γ rc i s st ⊢ mainOwn r γ rc i := by
  iintro H
  iapply mainOwn_intro r γ rc i s st
  iframe
  ileft; ipureintro; exact h

end defs

end github_com.hashicorp.raft

end Perennial
