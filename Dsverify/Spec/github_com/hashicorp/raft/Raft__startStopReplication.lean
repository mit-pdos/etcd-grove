/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__startStopReplication.lean (241f27e).
-/
/-
`raft.(*Raft).startStopReplication`'s spec (internal to the leader part of the main goroutine, MAIN-L). Starts a replication goroutine (`replicate`, through `goFunc`) for every other voter of the (fixed) configuration; the replication map was empty, so no goroutine is stopped.
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

/-- `(*Raft).startStopReplication` (stage 4; stage 3: only at `runLeader`'s start, the replication map
empty, every other voter of the fixed configuration started): makes the replication map's keys the
servers but `i` of the latest configuration (of the leader's log `s.log`, `leaderOwnC`): starts a
replication goroutine (`replicate`, through `goFunc`) for each new one, possibly rewrites a kept one's
peer (under `peerLock`), and stops each removed one's (`stopCh <- lastIdx; close(stopCh)`). -/
abbrev github_com.hashicorp.raft.Raft.startStopReplication.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s stLeader ∗ leaderOwnM r γ rc i s.term (fun _ => True) s.log.length ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"startStopReplication")) (Val #()))
  {{ RET #(); mainOwnAt r γ rc i s stLeader ∗ leaderOwnC r γ rc i s.term s.log ∗ rtok tid }}

end spec

end Perennial
