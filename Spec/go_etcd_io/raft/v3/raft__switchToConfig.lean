/-
Port of election_proof/spec_raft__switchToConfig.v (feb5c73d4); generalized to a leader
on 2026-10-13 (reconfiguration stage D, `ApplyConfChange`).

Lean notes:
* Rocq's `s <| nstate.progress := prs |> <| nstate.prvals := pvs |>` is
  `{ s with progress := prs, prvals := pvs }` (the same value), and the type of the
  untyped binder `pvs` is written out.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
-- `CommitOkC`
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section switch
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- What a leader does after installing the new configuration `s1` at the configuration `c`
(`switchToConfig`'s leader branch, when it stays a voter; 2026-10-13, reconfiguration stage A2):
`maybeCommit` moves the commit index to `n` by a joint quorum (`CommitOkC`), or not;
`bcastAppend` or a `Visit` of `maybeSendAppend(id, false)` sends `ms` (`ReplSends`), moving no
`Match`; the leader-transfer target may be cleared (`abortLeaderTransfer`). Includes doing
nothing (`n` the old commit index, no sends, the same values and target): what happens when the
new configuration has no incoming voter (`len(cs.Voters) == 0`). -/
def LeaderSwitchC (c : CfgM) (id : w64) (s1 s' : NState) : Prop :=
  ∃ (n : w64) (ms : List Msg) (pvs2 : GMap w64 Progress) (lt' : w64),
    (n = s1.logst.committed ∨ CommitOkC c (toPState s1) n) ∧
    ReplSends id { s1 with logst := { s1.logst with committed := n } } ms ∧
    prvalsMatch pvs2 = prvalsMatch s1.prvals ∧
    s' = { sendMsgs { s1 with logst := { s1.logst with committed := n } } ms with
             prvals := pvs2, lt := lt' }

/-- `switchToConfig`'s result at the configuration `c` (2026-10-13, reconfiguration stage A2):
a non-leader stops at `s1`; a leader that stays a voter of either half goes on
(`LeaderSwitchC`); a leader that is removed or demoted (no voter of either half) steps down,
`becomeFollower(r.Term, None)`, with `stepDownOnRemoval`, and (2026-10-25, T-M M2c; until then the
spec's premise required the flag) without it stops at `s1`, still leader. -/
def SwitchOkC (c : CfgM) (id : w64) (s1 s' : NState) : Prop :=
  if s1.role = .leader then
    (if id ∈ c.voters then LeaderSwitchC c id s1 s'
     else if s1.sdr = true then ∃ pvs, s' = { becomeFollower s1 s1.term (W64 0) with prvals := pvs }
     else s' = s1)
  else s' = s1

/-- What `switchToConfig` stores in `r.isLearner` at the configuration `c`: whether the node is
a learner of `c` (`ok && pr.IsLearner`; every learner is tracked, `LearnerFlagsC`). -/
def learnerOfC (c : CfgM) (id : w64) : Bool := decide (id ∈ c.learners)

theorem learnerOfC_simple (cfg : GSet w64) (prs : GMap w64 Loc) (id : w64) :
    learnerOfC (CfgM.simple cfg (domSet prs \ cfg)) id = learnerOf cfg prs id := by
  unfold learnerOfC learnerOf CfgM.simple
  simp only [GMap.elem_of_difference]

end switch

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.switchToConfig(cfg, trk)` installs a configuration and progress map in `r.trk`,
sets `r.isLearner`, and returns the tracker's `ConfState`; at a leader that stays a voter it
then commits what the new configuration's quorums allow and sends appends.

**It changes the configuration** `ownRaftPhys` is indexed by to `cfg`, and the progress map
with it. The struct comes in *open at its tracker* -- the field `r.trk` (holding `tv0`) and
the wand that re-seals it at any tracker of `cfg` (`ownRaftPhysCV_reconfig`'s) -- with what of
the old tracker survives, its tally and inflight bound (`ownTracker_votes`), and the new
`Config` and progress map as `ownConfigV` (`pvs` the new `Progress` records). Taking the
struct open lets the caller move the old `Progress` objects' resources to the new ones before
the call: `ApplyConfChange`'s new `Progress` objects are copies that share the old ones'
`Inflights` (`ownNewPr_transfer`). (Until 2026-10-13 it took `ownRaftPhys cfg0` sealed and
`ownConfig`, the non-leader case only: that statement, `spec_nonleader`, had no
caller and is gone, 2026-10-17; its open form is `newRaft`'s `wp_switchToConfig_follower`.)

**The leader case** (2026-10-13): `id ∈ cfg` (the node stays a voter: removing or demoting the
leader, and `stepDownOnRemoval`, are not covered), and each new `Match` is `0` or the old one
(`MatchKept`, what `Step.reMatch` takes); then `maybeCommit`, `bcastAppend` or the `Visit` of
`maybeSendAppend`, and the `leadTransferee` check over `Voters.IDs()` (`LeaderSwitch`).

`r.isLearner` ends up `learnerOf cfg prs id`: it is `ok && pr.IsLearner`, and a tracked
`Progress` is a learner's exactly outside `cfg` (`LearnerFlags`; since 2026-10-13, until
then `false`). The `ConfState` has the learners too (the tracked ids outside `cfg`).

**At any configuration since 2026-10-13** (reconfiguration stage A2): the new configuration
is any `c : CfgM` the `confchange` package produces (`ownConfigC`: joint, learners, staged
learners, `AutoLeave`), the struct is taken open at its tracker with the wand re-sealing it at
`c` with `Hvoter` at `c.voters ∪ {[id]}` (`ownRaftPhysCV_reconfig`; the node itself counted,
for the leader that is being removed), and the `ConfState` returned has all four lists and
`AutoLeave`. A leader either stays a voter of either half (`MatchKept`, then as above, with a
joint-quorum commit, `LeaderSwitchC`) or is removed or demoted: it steps down with `s.sdr = true`
(`Config.StepDownOnRemoval`), and without it stays leader outside the configuration (2026-10-25,
T-M M2c: `ownRaftPhysC`'s `Hvoter` no longer covers a leader; until then `s.sdr = true` was a
premise). A candidate or pre-candidate must
stay a voter, for the same reason (the Go code leaves it campaigning; if it then won,
`becomeLeader` would dereference its missing `Progress`: see
`issues/raft-advance-before-applyconfchange.md`, which is how an application gets there).
The result is `SwitchOkC`, from `{ s with progress, prvals, isLearner := learnerOfC c id }`.
(Until 2026-10-21 also the statement on `ownRaftPhys`, `specS`, derived by `spec_simple`.)

raft v3.7 (2026-10-15, stage R4): the `ConfState` returned is a `*pb.ConfState`, the tracker's
fresh one (`ProgressTracker.ConfState`'s post, R0): owned, its `AutoLeave` set (`csPts cs 1 ⟨xs,
ls, os, lns, c.autoLeave⟩ true`), with the same permutation facts on its lists. -/
abbrev raft.switchToConfig.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tv0 : tracker.ProgressTracker)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
  -- (2026-10-25, T-M M2c; until then `id ∉ c.voters` only with `s.sdr = true`) a leader that stays a
  -- voter keeps its peers' `Match` values
  (s.role = .leader → id ∈ c.voters → MatchKept s.prvals pvs) →
  (s.role = .candidate ∨ s.role = .preCandidate → id ∈ c.voters) →
  -- (2026-10-16, stage R8a, D11) at a leader the new `Progress` values are within its log (the
  -- leader's progress bound `PrvalsOk`, which the struct keeps): a kept peer's is the old one, a
  -- fresh one is at `max(lastIndex, 1)` (`applyConfChange`, `PrKept`)
  (s.role = .leader → ∀ v p, pvs !! v = some p → PrOkN s.gh.ns s.logst p) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htrkf" ∷ r.[raft, go!"trk"] ↦ tv0 ∗
      "Hback" ∷ (∀ tv' prs' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨s.votes, prs', pvs'⟩ -∗
           ⌜PrvalsOk { s with progress := prs', prvals := pvs' }⌝ -∗
           ownRaftPhysCV c (c.voters ∪ {[id]}) r id { s with progress := prs', prvals := pvs' }) ∗
      "Hvotes" ∷ tv0.Votes' ↦$ s.votes ∗
      "%Hmi" ∷ ⌜0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62⌝ ∗
      "Hnew" ∷ ownConfigC c cfgv prsm prs pvs }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
      (Val #cfgv)) (Val #prsm))
  {{ (cs : Loc) (xs os ls lns : List w64) (s' : NState), RET #cs;
      ownRaftPhysCV c c.voters r id s' ∗
      csPts cs (DFrac.own 1) (ConfStateM.mk xs ls os lns c.autoLeave) true ∗
      ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
        lns ≡ₚ elements c.learnersNext⌝ ∗
      ⌜SwitchOkC c id { s with progress := prs, prvals := pvs, isLearner := learnerOfC c id }
        s'⌝ }}

end spec

end EtcdGrove
end Perennial
