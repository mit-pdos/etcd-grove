/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__LeaderWithID.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).LeaderWithID`: a read under `leaderLock` (a reader token borrowed from
the lock's thread pool with the thread token).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LeaderWithID
public import Perennial.Proof.sync.Results

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

theorem github_com.hashicorp.raft.Raft.LeaderWithID.wp_proof :
    github_com.hashicorp.raft.Raft.LeaderWithID.spec (GF := GF) (hG := hG) := by
  intro r γ rc i tid
  wp_start as ⟨#His, Htok⟩
  ihave #Hl := isRaft_locks r γ rc i $$ His
  unfold raftLocks rwLock
  icases Hl with ⟨-, ⟨%γp, -, #Hpool⟩, -⟩
  iapply wp_fupd
  wp_auto_lc 1
  imod qpool.borrow_lc leaderLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ (leaderLockP r)) $$ [$Hown] as ⟨Hrl, HP⟩
  iunfold leaderLockP at HP
  icases HP with ⟨%a, %id, Ha, Hid⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock _ (leaderLockP r)) $$ [$Hrl Ha Hid] as Hown
  · inext; iunfold leaderLockP; iexists a, id; iframe
  imod qpool.giveBack leaderLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
    with Htok
  imodintro
  iapply HΦ $$ Htok

end proof

end Perennial
