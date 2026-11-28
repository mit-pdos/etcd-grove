/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__RemoveServer.lean (241f27e).
-/
/-
The proof of `raft.Raft.RemoveServer` (stage 4 interface: a new spec, to be proved).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__RemoveServer
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__requestConfigChange

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

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

theorem github_com.hashicorp.raft.Raft.RemoveServer.wp_proof
    (wp_requestConfigChange :
      github_com.hashicorp.raft.Raft.requestConfigChange.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.RemoveServer.spec (GF := GF) (hG := hG) := by
  intro r γ rc i id prev tmo
  wp_start as ⟨#Hr, %Hpre⟩
  obtain ⟨hid, hok⟩ := Hpre
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨#Hpv, -⟩
  wp_auto
  wp_apply wp_requestConfigChange $$ [$Hr] as %fi Hfut
  · ipureintro; refine ⟨Or.inr (Or.inr (Or.inr rfl)), hid, fun h => by rcases h with h | h <;> (simp only at h; revert h; word), hok⟩
  iapply HΦ $$ Hfut

end proof

end Perennial
