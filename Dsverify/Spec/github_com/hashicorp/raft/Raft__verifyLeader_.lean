/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__verifyLeader_.lean (241f27e).
-/
/-
`raft.(*Raft).verifyLeader`'s spec (internal to the leader part of the main goroutine, MAIN-L, stage 2).
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

/-- `(*Raft).verifyLeader(v)` (the leader loop's `verifyCh` case for a fresh future, stage 2): the
leader of `s.term` registers `v` (`verifyRegistry`: at a snapshot after the client's; its own vote
with its witness; its responder side pending in the registry) in its notify set and in each
follower's (stage 4, fix `6c3454c`: each voter's of its latest configuration, with that follower's
vote token), and wakes the heartbeat goroutines; (stage 4, fixes `4bb3955`, `0c7aa12`) its own vote
counts only if it is a voter of its latest configuration, and when that alone reaches the quorum
size the future goes to the FSM goroutine (`fsmVerifyP`, behind the batches sent: the leader's facts
at the registration, `gprot.read_bound_upd` with a quorum of one); stage 3 had two voters or more. -/
abbrev github_com.hashicorp.raft.Raft.verifyLeader.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (v : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s stLeader ∗ leaderOwnC r γ rc i s.term s.log ∗ verifyNew γ rc i v ∗
     (∃ n0 : Nat, len0Is γ s.term n0 ∗ ⌜n0 < s.log.length⌝) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"verifyLeader")) (Val #v))
  {{ RET #(); mainOwnAt r γ rc i s stLeader ∗ leaderOwnC r γ rc i s.term s.log }}

end spec

end Perennial
