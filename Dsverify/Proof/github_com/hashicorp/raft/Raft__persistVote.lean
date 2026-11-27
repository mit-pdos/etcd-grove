/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__persistVote.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).persistVote`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__persistVote
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base

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

theorem github_com.hashicorp.raft.Raft.persistVote.wp_proof :
    github_com.hashicorp.raft.Raft.persistVote.spec (GF := GF) (hG := hG) :=
  fun r γ rc i sst t cs cb => by
  wp_start as ⟨#Hr, Hs, #Hcs⟩
  ihave #Hg := pkgGlobals_access $$ Hpkg
  unfold pkgGlobals
  icases Hg with ⟨-, -, ⟨%k1, #Hk1, #Hk1s⟩, ⟨%k2, #Hk2, #Hk2s⟩, -⟩
  ihave ⟨%x, #Hst, #Hss⟩ := isRaft_stableStore r γ rc i $$ Hr
  unfold isStableStore
  icases Hss with ⟨#HgetU, #HsetU, #Hget, #Hset⟩
  wp_auto
  wp_apply HsetU $$ Hs Hk1s
  iintro Hs
  wp_auto
  wp_apply Hset $$ Hs Hk2s Hcs
  iintro Hs
  wp_auto
  wp_end
