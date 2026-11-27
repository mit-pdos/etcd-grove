/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__replicateTo.lean (241f27e).
-/
/-
`raft.(*Raft).replicateTo`'s spec (replication subsystem, internal).
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

/-- `(*Raft).replicateTo` (with the fork's fix: the term check before the RPC), by the replication
goroutine of the leader `i` of term `T` for voter `j`: every request it sends is valid; it stops
(`true`) when the term moved on, the follower has a newer term, or the stop channel is closed
(stage 2: a close-only broadcast channel, `stopChan`; receiving needs only its persistent facts). -/
abbrev github_com.hashicorp.raft.Raft.replicateTo.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc)
    (γs : StopNames) (lastIndex : w64) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ leaderIs γ T i ∗ termLb γ i T ∗ replStopCh s γs ∗
     replFields s ∗ rtok tid }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"replicateTo")) (Val #s))
      (Val #lastIndex))
  {{ (b : Bool), RET #b; rtok tid ∗ replFields s }}

end spec

end Perennial
