/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setLeader.lean (241f27e).
-/
/-
`raft.(*Raft).setLeader`'s spec (raft-internal interface, notes/raft-iface.md). Writes `leaderAddr`/`leaderID` under `leaderLock`, and observes a `LeaderObservation` if they changed.
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

/-- `(*Raft).setLeader`: Writes `leaderAddr`/`leaderID` under `leaderLock`, and observes a `LeaderObservation` if they changed. -/
abbrev github_com.hashicorp.raft.Raft.setLeader.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (a : ServerAddress) (id : ServerID) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ rtok tid }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLeader")) (Val #a)) (Val #id))
  {{ RET #(); rtok tid }}

end spec

end Perennial
