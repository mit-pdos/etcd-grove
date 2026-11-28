/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__getLastIndex.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).getLastIndex` (called through `*Raft`): reads under
`lastLock` (no snapshot: the last log index).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.max
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.LastLock
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers

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
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.raftState.getLastIndex.wp_proof
    (wp_max : github_com.hashicorp.raft.max.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG) := by
  constructor
  · intro r γ rc i s a
    wp_start as ⟨#His, Hg, Hsrv, Ha, %Hale⟩
    ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ His
    ihave #Hdur := isRaft_durInv r γ rc i $$ His
    ihave #Hm := isRaft_lastLock r γ rc i $$ His
    wp_method_call; wp_call
    wp_auto
    wp_apply (lc := 0) wp_with_defer as %defer Hdefer
    wp_apply (sync.Mutex.wp_Lock _ (lastLockInv r γ rc i)) $$ [$Hm] with ⟨Hown, HL⟩
    iunfold lastLockInv at HL
    icases HL with ⟨%x, %y, %si, %st, Hx, Hy, Hsi, Hst, Hg', #Hsnap, Hllb⟩
    ihave %he := ghostVar_agree _ _ _ _ _ $$ Hg Hg'
    wp_auto
    wp_apply wp_max
    (try wp_auto)
    wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hm Hown Hx Hy Hsi Hst Hg' Hllb]
    · iframe #; iframe; inext; iunfold lastLockInv; iexists x, y, si, st; iframe Hx Hy Hsi Hst Hg' Hllb; iexact Hsnap
    iapply HΦ
    iframe
    ipureintro
    split at he <;> simp only [Prod.mk.injEq] at he <;> split <;> word
  · intro r γ rc i
    wp_start as #His
    ihave #Hm := isRaft_lastLock r γ rc i $$ His
    wp_method_call; wp_call
    wp_auto
    wp_apply (lc := 0) wp_with_defer as %defer Hdefer
    wp_apply (sync.Mutex.wp_Lock _ (lastLockInv r γ rc i)) $$ [$Hm] with ⟨Hown, HL⟩
    iunfold lastLockInv at HL
    icases HL with ⟨%x, %y, %si, %st, Hx, Hy, Hsi, Hst, Hg', #Hsnap, Hllb⟩
    wp_auto
    wp_apply wp_max
    (try wp_auto)
    wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hm Hown Hx Hy Hsi Hst Hg' Hllb]
    · iframe #; iframe; inext; iunfold lastLockInv; iexists x, y, si, st; iframe Hx Hy Hsi Hst Hg' Hllb; iexact Hsnap
    iapply HΦ
    itrivial

end proof

end Perennial
