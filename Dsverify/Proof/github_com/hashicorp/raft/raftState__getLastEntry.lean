/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/raftState__getLastEntry.lean (241f27e).
-/
/-
The proof of `raft.(*raftState).getLastEntry` (called through `*Raft`): reads under
`lastLock` (no snapshot: the last log entry).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastEntry
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

theorem github_com.hashicorp.raft.raftState.getLastEntry.wp_proof :
    github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG) := by
  intro r γ rc i s a
  wp_start as ⟨#His, Hg, Hsrv, Ha, %Hale⟩
  ihave ⟨#HInv, -⟩ := isRaft_proto r γ rc i $$ His
  ihave #Hdur := isRaft_durInv r γ rc i $$ His
  ihave #Hm := isRaft_lastLock r γ rc i $$ His
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (sync.Mutex.wp_Lock _ (lastLockInv r γ rc i)) $$ [$Hm] with ⟨Hown, HL⟩
  iunfold lastLockInv at HL
  icases HL with ⟨%x, %y, %si, %st, Hx, Hy, Hsi, Hst, Hg', #Hsnap, Hllb⟩
  ihave %he := ghostVar_agree _ _ _ _ _ $$ Hg Hg'
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  ihave Hr := durRead γ rc i (E := ⊤) (fun _ _ => CoPset.mem_full) s
      iprop(monoNatAuthOwn rc.dur.applied (1 : Qp).half a)
      iprop(monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜uint.nat si ≤ s.log.length⌝) $$ [Hsrv Ha]
  · iframe #; iframe
    iintro Ho Ha
    iapply lastLock_snap_le _ gprotN_diff_durN γ rc i s _ a si st $$ [$HInv $Ho $Ha $Hsnap]
    ipureintro; exact Hale
  imod Hr $$ Hnc with ⟨Hnc, Hsrv, Ha, %Hsi⟩
  iframe Hnc
  imodintro
  wp_auto
  wp_if_destruct
  · (try wp_auto)
    wp_apply (sync.Mutex.wp_Unlock _ (lastLockInv r γ rc i)) $$ [Hm Hown Hx Hy Hsi Hst Hg' Hllb]
    · iframe #; iframe; inext; iunfold lastLockInv; iexists x, y, si, st; iframe Hx Hy Hsi Hst Hg' Hllb; iexact Hsnap
    iapply HΦ
    iframe
    ipureintro; simp only [Prod.mk.injEq] at he; omega
  · exfalso
    simp only [Prod.mk.injEq] at he
    have : uint.nat si ≤ uint.nat x := by omega
    word

end proof

end Perennial
