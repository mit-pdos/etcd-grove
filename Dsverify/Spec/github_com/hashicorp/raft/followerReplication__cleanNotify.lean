/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/followerReplication__cleanNotify.lean (241f27e).
-/
/-
`raft.followerReplication.cleanNotify`'s spec (replication subsystem, internal; stage 2).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

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

/-- `(*followerReplication).cleanNotify(v)` (stage 2), by the leader loop (leaderLoop's verify
cases): removes `v` from the follower's notify set, under its lock (the entry's vote token is
dropped). -/
abbrev github_com.hashicorp.raft.followerReplication.cleanNotify.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s v : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ replShared r γ rc i T j s }}
    (App (Val (s @!! go.GoType.PointerType followerReplication.ty @!! go!"cleanNotify")) (Val #v))
  {{ RET #(); True }}

end spec

end Perennial
