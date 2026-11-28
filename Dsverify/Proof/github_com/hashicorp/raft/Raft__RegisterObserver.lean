/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__RegisterObserver.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).RegisterObserver`: an insertion into the observers map under `observersLock` (the writers' guard).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__RegisterObserver
public import Perennial.Proof.sync.Results
public import Perennial.Golang.Theory.Map

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

theorem github_com.hashicorp.raft.Raft.RegisterObserver.wp_proof :
    github_com.hashicorp.raft.Raft.RegisterObserver.spec (GF := GF) (hG := hG) := by
  intro r γ rc i o
  wp_start as ⟨#His, #Ho⟩
  ihave #Hl := isRaft_locks r γ rc i $$ His
  unfold raftLocks rwLock
  icases Hl with ⟨-, -, -, ⟨%γp, #Hguard, -⟩, -⟩
  ihave #Ho' := Ho
  unfold obsOk
  icases Ho' with ⟨%fl, %id, #Hch, #Hbl, #Hf, #Hid, -⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (sync.RWMutex.wp_Lock_guard _ (observersP γ rc i r)) $$ [] as ⟨Hlk, HP⟩
  · iframe #
  iunfold observersP at HP
  icases HP with ⟨%m, %mv, Hm, Hmv, Hobs⟩
  wp_auto
  wp_apply (wp_mapInsert go.uint64 m mv id o) $$ [$Hmv] as Hmv
  wp_apply (sync.RWMutex.wp_Unlock_guard _ (observersP γ rc i r)) $$ [Hlk Hm Hmv Hobs]
  · iframe Hlk
    inext
    iunfold observersP
    iexists m, _
    iframe Hm Hmv
    iapply (BigSepM.bigSepM_insert_elim) $$ [] [Hobs]
    · unfold obsOk; iexact Ho
    · iexact Hobs
  iapply HΦ
  itrivial

end proof

end Perennial
