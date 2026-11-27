/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/followerReplication__LastContact.lean (241f27e).
-/
/-
`raft.(*followerReplication).LastContact`'s spec (raft-internal interface, notes/raft-iface.md). Under the replication state's `lastContactLock` (read lock: a thread token); called by the main goroutine (`checkLeaderLease`).
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

/-- `(*followerReplication).LastContact`: Under the replication state's `lastContactLock` (read lock: a thread token); called by the main goroutine (`checkLeaderLease`). -/
abbrev github_com.hashicorp.raft.followerReplication.LastContact.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ replShared r γ rc i T j s ∗ rtok tid }}
    (App (Val (s @!! go.GoType.PointerType followerReplication.ty @!! go!"LastContact")) (Val #()))
  {{ (t : time.Time), RET #t; rtok tid }}

end spec

end Perennial
