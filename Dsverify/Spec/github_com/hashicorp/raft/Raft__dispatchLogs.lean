/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__dispatchLogs.lean (241f27e).
-/
/-
`raft.(*Raft).dispatchLogs`'s spec (internal to the leader part of the main goroutine, MAIN-L).
The leader `i` of term `s.term` appends the futures' entries to its log (`leaderAppendCmd_upd` at
the log store's `StoreLogs`), acknowledges them in its commitment and wakes its replicators; the
futures become inflight.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).dispatchLogs(sl)`: the leader of term `s.term` dispatches the futures `fs` (at least
one): they get the next indexes, are stored in the log and become inflight. -/
abbrev github_com.hashicorp.raft.Raft.dispatchLogs.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (sl : GoSlice) (dq : DFrac)
    (fs : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s stLeader ∗ leaderOwnC r γ rc i s.term s.log ∗
     sl ↦*{dq} fs ∗ ⌜fs ≠ []⌝ ∗ ([∗list] f ∈ fs, dispP γ rc i f) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"dispatchLogs")) (Val #sl))
  {{ RET #(); ∃ s' : SState, mainOwnAt r γ rc i s' stLeader ∗
      ⌜s'.term = s.term ∧ s.log.length < s'.log.length⌝ ∗
      leaderOwnC r γ rc i s.term s'.log ∗ sl ↦*{dq} fs }}

end spec

end Perennial
