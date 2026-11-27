/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__heartbeat.lean (241f27e).
-/
/-
`raft.(*Raft).heartbeat`'s spec (replication subsystem, internal).
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

/-- `(*Raft).heartbeat`, the heartbeat goroutine of the leader `i` of term `T` for voter `j`
(started by `replicate`): sends valid heartbeats (`aeValid_heartbeat`) until `stopCh` is closed. -/
abbrev github_com.hashicorp.raft.Raft.heartbeat.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s stopCh : Loc)
    (γh : SpscNames) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     replShared r γ rc i T j s ∗ leaderIs γ T i ∗ termLb γ i T ∗ hbStop γh stopCh ∗
     spscConsumer γh ([] : List Unit) ∗ rtok tid }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"heartbeat")) (Val #s)) (Val #stopCh))
  {{ RET #(); rtok tid }}

end spec

end Perennial
