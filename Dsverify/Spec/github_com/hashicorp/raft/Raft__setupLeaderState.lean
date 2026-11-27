/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setupLeaderState.lean (241f27e).
-/
/-
`raft.(*Raft).setupLeaderState`'s spec (internal to the leader part of the main goroutine, MAIN-L). Allocates the leader state of term `s.term`: the commit channel, the commitment (start index `len0 + 1`: nothing was appended since the election), empty inflight list, replication map and notify map, the step-down channel.
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

/-- `(*Raft).setupLeaderState`: Allocates the leader state of term `s.term`: the commit channel, the commitment (start index `len0 + 1`: nothing was appended since the election; stage 4: over the latest configuration's voters, with the commitment's half of `ccfgOwn`), empty inflight list, replication map and notify map, the step-down channel. -/
abbrev github_com.hashicorp.raft.Raft.setupLeaderState.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAt r γ rc i s stLeader ∗ len0Is γ s.term s.log.length ∗
     ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ leaderStateAny r rc }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setupLeaderState")) (Val #()))
  {{ RET #(); mainOwnAt r γ rc i s stLeader ∗ leaderOwnM r γ rc i s.term (fun m => m = ∅) s.log.length }}

end spec

end Perennial
