/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__appendConfigurationEntry.lean (241f27e).
-/
/-
`raft.Raft.appendConfigurationEntry`'s spec (stage 4 interface).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs
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

/-- `(*Raft).appendConfigurationEntry(f)` (stage 4; the leader loop's `configurationChangeChIfStable`
case), by the leader `i` of `s.term` with a configuration change future `f` (`ccfP`) and the stability
`configurationChangeChIfStable` checked (a recorded commit of its term covers its latest
configuration's index): `nextConfiguration` of the latest; on an error the future is answered; else
the configuration entry is dispatched (`gprot.leaderAppendCfg_upd`: adjacent, valid; the future
inflight, `futResp`'s configuration case), becomes the latest (`setLatestConfiguration`, the cell too),
the commitment counts it (`commitment.setConfiguration`, `gprot.installCfg_upd`), and the replication
goroutines follow it (`startStopReplication`). -/
abbrev github_com.hashicorp.raft.Raft.appendConfigurationEntry.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (f : Loc) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     mainOwnAtSt r γ rc i s ∗ leaderOwnC r γ rc i s.term s.log ∗ ccfP γ f ∗
     (∃ k p : Nat, commitIs γ s.term k p ∗ ⌜lastCfgIdx s.log ≤ k⌝) ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"appendConfigurationEntry")) (Val #f))
  {{ RET #(); ∃ s' : SState, mainOwnAt r γ rc i s' stLeader ∗
      ⌜s'.term = s.term ∧ s.log.length ≤ s'.log.length⌝ ∗
      leaderOwnC r γ rc i s.term s'.log ∗ rtok tid }}

end spec

end Perennial
