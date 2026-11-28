/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__preElectSelf.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).preElectSelf` (and of its `askPeer` closure and goroutines).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__preElectSelf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Perennial.Spec.strings.Contains
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Elect

@[expose] public section

set_option linter.deprecated false

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

theorem chan_start_ok {V : Type} (cap : w64) :
    match (if cap = W64 0 then ChanState.Idle else ChanState.Buffered ([] : List V)) with
    | .Idle | .Buffered [] => True | _ => False := by
  by_cases h : cap = W64 0
  · rw [if_pos h]; trivial
  · rw [if_neg h]; trivial

set_option maxHeartbeats 1000000 in
theorem github_com.hashicorp.raft.Raft.preElectSelf.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastEntry : github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_Contains : strings.Contains.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.preElectSelf.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
