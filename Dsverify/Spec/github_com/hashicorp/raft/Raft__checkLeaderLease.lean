/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__checkLeaderLease.lean (241f27e).
-/
/-
`raft.(*Raft).checkLeaderLease`'s spec (internal to the leader part of the main goroutine, MAIN-L). Counts the voters contacted within the lease (itself and the followers whose replication goroutine reports a recent contact); steps down (`Follower`) without a quorum.
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

/-- `(*Raft).checkLeaderLease`: Counts the voters contacted within the lease (itself and the followers whose replication goroutine reports a recent contact); steps down (`Follower`) without a quorum. -/
abbrev github_com.hashicorp.raft.Raft.checkLeaderLease.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s stLeader ∗ leaderOwnC r γ rc i s.term s.log ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"checkLeaderLease")) (Val #()))
  {{ (d : time.Duration), RET #d; ∃ st : w32, mainOwnAt r γ rc i s st ∗
      ⌜st = stLeader ∨ st = stFollower⌝ ∗ leaderOwnC r γ rc i s.term s.log ∗ rtok tid }}

end spec

end Perennial
