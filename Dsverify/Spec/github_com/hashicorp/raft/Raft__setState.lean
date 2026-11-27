/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setState.lean (241f27e).
-/
/-
`raft.(*Raft).setState`'s spec (raft-internal interface, notes/raft-iface.md). Clears the leader, stores the state, and observes it if it changed: for `Leader`, the caller (the main goroutine, as it becomes leader) lends its protocol state with its `leaderIs` witness to the observers (`obsArg`) and gets the same state `s` back.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

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

/-- `(*Raft).setState`: Clears the leader, stores the state, and observes it if it changed: for `Leader`, the caller (the main goroutine, as it becomes leader) lends its protocol state with its `leaderIs` witness to the observers (`obsArg`) and gets the same state `s` back. -/
abbrev github_com.hashicorp.raft.Raft.setState.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (st0 st : w32) (s : SState) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ ghostVar rc.names.state (1 : Qp).half st0 ∗
     ⌜st = stFollower ∨ st = stCandidate ∨ st = stLeader⌝ ∗
     obsArg γ i s (interface.mkOk RaftState.ty #st) ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setState")) (Val #st))
  {{ RET #(); ghostVar rc.names.state (1 : Qp).half st ∗
      obsArg γ i s (interface.mkOk RaftState.ty #st) ∗ rtok tid }}

end spec

end Perennial
