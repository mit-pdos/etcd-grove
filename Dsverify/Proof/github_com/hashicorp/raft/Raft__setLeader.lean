/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setLeader.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setLastContact`: a write under `leaderLock` (the writers' guard), then an observation if the leader changed.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLeader
public import Perennial.Proof.sync.Results
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__observe
public import Dsverify.Proof.github_com.hashicorp.raft.core.ObsHelpers

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

theorem github_com.hashicorp.raft.Raft.setLeader.wp_proof
    (wp_observe : github_com.hashicorp.raft.Raft.observe.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setLeader.spec (GF := GF) (hG := hG) := by
  intro r γ rc i a id tid
  -- the observation is no `RaftState`: `obsArg`'s state index is irrelevant
  let sNone : SState := { term := 0, log := [], vterm := 0, vcand := [], dur := (0, 0), cidx := 0 }
  wp_start as ⟨#His, Htok⟩
  ihave #Hl := isRaft_locks r γ rc i $$ His
  unfold raftLocks rwLock
  icases Hl with ⟨-, ⟨%γp, #Hguard, -⟩, -⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_Lock_guard _ (leaderLockP r)) $$ [] as ⟨Hlk, HP⟩
  · iframe #
  iunfold leaderLockP at HP
  icases HP with ⟨%a0, %id0, Ha, Hid⟩
  wp_auto
  wp_apply (sync.RWMutex.wp_Unlock_guard _ (leaderLockP r)) $$ [Hlk Ha Hid]
  · iframe Hlk
    inext
    iunfold leaderLockP
    iexists a, id
    iframe
  wp_if_destruct
  · wp_if_destruct
    · iapply HΦ $$ Htok
    · wp_apply (wp_observe r γ rc i sNone) $$ [$Htok] as ⟨-, Htok⟩
      · iframe #
        iapply obsArg_other
        · exact mkOk_ne_leaderObs _ _ leaderObservation_ty_ne
        · exact mkOk_not_raftState _ _ leaderObservation_ty_ne
      iapply HΦ $$ Htok
  · wp_apply (wp_observe r γ rc i sNone) $$ [$Htok] as ⟨-, Htok⟩
    · iframe #
      iapply obsArg_other
      · exact mkOk_ne_leaderObs _ _ leaderObservation_ty_ne
      · exact mkOk_not_raftState _ _ leaderObservation_ty_ne
    iapply HΦ $$ Htok

end proof

end Perennial
