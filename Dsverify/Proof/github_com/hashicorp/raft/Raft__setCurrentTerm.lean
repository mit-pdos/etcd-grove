/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__setCurrentTerm.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).setCurrentTerm`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setCurrentTerm
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

theorem github_com.hashicorp.raft.Raft.setCurrentTerm.wp_proof
    (wp_rs_setCurrentTerm : github_com.hashicorp.raft.raftState.setCurrentTerm.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG) :=
  fun r γ rc i sst t Q => by
  wp_start as ⟨#Hr, Hs, Hupd⟩
  ihave #Hg := pkgGlobals_access $$ Hpkg
  unfold pkgGlobals
  icases Hg with ⟨-, ⟨%k0, #Hk0, #Hk0s⟩, -, -, -⟩
  ihave ⟨%x, #Hst, #Hss⟩ := isRaft_stableStore r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  unfold isStableStore
  icases Hss with ⟨#HgetU, #HsetU, #Hget, #Hset⟩
  wp_auto
  wp_apply HsetU $$ Hs Hk0s
  iintro Hs
  wp_auto
  wp_apply wp_rs_setCurrentTerm r γ i t Q $$ [$Htc $Hupd] as HQ
  wp_end
