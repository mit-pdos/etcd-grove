/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/core/ObsHelpers.lean (241f27e).
-/
/-
Helper lemmas for the observer proofs (agent CORE, group C): an observation that is not the
`RaftState` `Leader` value (Q4 of notes/raft-iface-lean.md).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A value of a named type other than `RaftState` is not `leaderObs`. -/
theorem mkOk_ne_leaderObs (t : go.GoType) (v : val) (h : t ≠ RaftState.ty) :
    interface.mkOk t v ≠ leaderObs := by
  unfold leaderObs
  simp only [Ne, interface.mkOk]
  intro h'
  simp_all

/-- A value of another named type is never a `RaftState` interface value. -/
theorem mkOk_not_raftState (t : go.GoType) (x : val) (h : t ≠ RaftState.ty) :
    ∀ v, interface.mkOk t x = interface.mkOk RaftState.ty v → ∃ st : w32, v = #st := by
  intro v hv
  simp only [interface.mkOk] at hv
  simp_all

theorem leaderObservation_ty_ne : LeaderObservation.ty ≠ RaftState.ty := by
  unfold LeaderObservation.ty RaftState.ty; simp

end

end github_com.hashicorp.raft

end Perennial
