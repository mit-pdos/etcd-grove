/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__runLeader.lean (241f27e).
-/
/-
`raft.(*Raft).runLeader`'s spec (main goroutine; called by `run` when the state is `Leader`).
Internal to the main-goroutine subsystems (written by MAIN-C, proved by MAIN-L).
The caller holds `mainOwn` with the raft state `Leader` (`mainOwnAt … s stLeader`, which carries
`leaderIs γ s.term i`: `runCandidate` did `becomeLeader_upd` before `setState(Leader)`), nothing
appended since the election (`len0Is γ s.term s.log.length`, from `becomeLeader_upd`, kept by
`mainOwn` in the state `Leader`), and the leader-state fields with any values. On return (stepped down), `mainOwn` (any state) and the
leader-state fields again.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.main.MainOwnAt

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

/-- `(*Raft).runLeader()`: the leader loop of term `s.term`, entered with the state `Leader` (stage 4:
with the commitment's half of `ccfgOwn`, `mainOwn`'s leader case). -/
abbrev github_com.hashicorp.raft.Raft.runLeader.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
      mainOwnAt r γ rc i s stLeader ∗ len0Is γ s.term s.log.length ∗
      ccfgOwn γ i s.term (lastCfgIdx s.log) ∗ leaderStateAny r rc ∗
      rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"runLeader")) (Val #()))
  {{ RET #(); mainOwn r γ rc i ∗ leaderStateAny r rc ∗ rtok tid }}

end spec

end Perennial
