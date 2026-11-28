/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__pickServer.lean (241f27e).
-/
/-
`raft.(*Raft).pickServer`'s spec (internal to the leader part of the main goroutine, MAIN-L, stage 2).
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

/-- `(*Raft).pickServer()` (the leader loop's leadership transfer without a target): `nil`, or a
fresh `*Server` holding a voter `j ≠ i` of the latest configuration `ss` (`voterSrv j`; stage 4: of
`ss`, stage 3: of the fixed voters) with a replication goroutine. It reads the configuration and the
replication map (and each follower's `nextIndex` atomic). -/
abbrev github_com.hashicorp.raft.Raft.pickServer.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (ccfg cfg : Configuration)
    (cidx li : w64) (ss : List Server) (rs : GoMap) (rmap : GMap SID Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗ cfgVal γ cfg ss ∗
     r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs ∗ rs ↦$ rmap ∗
     ([∗map] j ↦ s ∈ rmap, replShared r γ rc i T j s) }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"pickServer")) (Val #()))
  {{ (p : Loc), RET #p; r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
     r.[Raft, go!"leaderState"].[leaderState, go!"replState"] ↦ rs ∗ rs ↦$ rmap ∗
     (⌜p = null⌝ ∨ ∃ (j : SID) (s : Loc), p ↦ voterSrv j ∗
        ⌜rmap !! j = some s ∧ j ≠ i ∧ j ∈ srvVoters ss⌝) }}

end spec

end Perennial
