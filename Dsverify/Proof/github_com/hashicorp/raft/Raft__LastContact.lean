/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__LastContact.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).LastContact`: a read of `lastContact` under `lastContactLock` (read)
(a reader token borrowed from the lock's thread pool with the thread token).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__LastContact
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

theorem github_com.hashicorp.raft.Raft.LastContact.wp_proof :
    github_com.hashicorp.raft.Raft.LastContact.spec (GF := GF) (hG := hG) := by
  intro r γ rc i tid
  wp_start as ⟨#His, Htok⟩
  ihave #Hl := isRaft_locks r γ rc i $$ His
  unfold raftLocks rwLock
  icases Hl with ⟨-, -, ⟨%γp, -, #Hpool⟩, -⟩
  iapply wp_fupd
  wp_auto_lc 1
  imod qpool.borrow_lc lastContactLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hpool $Htok]
    with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ (lastContactP r)) $$ [$Hown] as ⟨Hrl, HP⟩
  iunfold lastContactP at HP
  icases HP with ⟨%t, Ht⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_RUnlock _ (lastContactP r)) $$ [$Hrl Ht] as Hown
  · inext; iunfold lastContactP; iexists t; iframe
  imod qpool.giveBack lastContactLockN γp _ ⊤ (by solve_ndisj) tid $$ [$Hpool $Hloan $Hown]
    with Htok
  imodintro
  iapply HΦ $$ Htok

end proof

end Perennial
