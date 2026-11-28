/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__setLastLog.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).setLastLog` (called through `*Raft`): writes under `lastLock`,
updating both halves of its ghost variable.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastLog
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers
public import Dsverify.Proof.github_com.hashicorp.raft.core.LastLock

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

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.raftState.setLastLog.wp_proof :
    github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG) := by
  intro r γ rc i p a x y
  wp_start as ⟨#His, Hg, Ha, %Hax⟩
  ihave #Hm := isRaft_lastLock r γ rc i $$ His
  wp_method_call; wp_call
  wp_auto
  wp_apply (sync.Mutex.wp_Lock _ (lastLockInv r γ rc i)) $$ [$Hm] with ⟨Hown, HL⟩
  iunfold lastLockInv at HL
  icases HL with ⟨%x0, %y0, %si, %st, Hx, Hy, Hsi, Hst, Hg', #Hsnap⟩
  ihave #Hs2 := Hsnap
  icases Hs2 with (%H0 | ⟨%e, -, -, #Hlb, -⟩)
  · have Hsia : uint.nat si ≤ a := by subst H0; simp
    imod ghostVar_update_halves (uint.nat x, uint.nat y) _ _ _ $$ Hg Hg' with ⟨Hg, Hg'⟩
    wp_auto
    wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hm Hown Hx Hy Hsi Hst Hg']
    · iframe #; iframe; inext; iunfold lastLockInv; iexists x, y, si, st
      rw [if_neg (by omega)]
      iframe; iexact Hsnap
    iapply HΦ
    iframe
  · ihave %Hsia := applLb_le rc _ a (uint.nat si) $$ [$Ha $Hlb]
    imod ghostVar_update_halves (uint.nat x, uint.nat y) _ _ _ $$ Hg Hg' with ⟨Hg, Hg'⟩
    wp_auto
    wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hm Hown Hx Hy Hsi Hst Hg']
    · iframe #; iframe; inext; iunfold lastLockInv; iexists x, y, si, st
      rw [if_neg (by omega)]
      iframe; iexact Hsnap
    iapply HΦ
    iframe

end proof

end Perennial
