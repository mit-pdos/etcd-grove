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
-- `CommitOk`
public import Spec.go_etcd_io.raft.v3.raft__maybeCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section switch
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- What a leader does after installing the new configuration `s1` (`switchToConfig`'s
leader branch, when it stays a voter): `maybeCommit` moves the commit index to `c` (or not:
`c` is the old one), `bcastAppend` (after a commit) or a `Visit` of `maybeSendAppend(id,
false)` sends `ms`, which `ReplOk` allows, moving no `Match`; the leader-transfer target may
be cleared (`abortLeaderTransfer`, when it left the voters). -/
def LeaderSwitch (cfg : GSet w64) (id : w64) (s1 s' : NState) : Prop :=
  ∃ (c : w64) (ms : List Msg) (pvs2 : GMap w64 Progress) (lt' : w64),
    (c = s1.logst.committed ∨ CommitOk cfg (toPState s1) c) ∧
    ReplSends id { s1 with logst := { s1.logst with committed := c } } ms ∧
    prvalsMatch pvs2 = prvalsMatch s1.prvals ∧
    s' = { sendMsgs { s1 with logst := { s1.logst with committed := c } } ms with
             prvals := pvs2, lt := lt' }

/-- `switchToConfig`'s result from the state `s1` with the new configuration installed: a
non-leader stops there; a leader goes on (`LeaderSwitch`). -/
def SwitchOk (cfg : GSet w64) (id : w64) (s1 s' : NState) : Prop :=
  if s1.role = .leader then LeaderSwitch cfg id s1 s' else s' = s1

/-- `LeaderSwitch` at the configuration `c` (2026-10-13, reconfiguration stage A2): the commit
by a joint quorum (`CommitOkC`). Includes doing nothing (`c` the old commit index, no sends,
the same values and target): what happens when the new configuration has no incoming voter
(`len(cs.Voters) == 0`). -/
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
`becomeFollower(r.Term, None)` (`stepDownOnRemoval`, which the spec's premise requires). -/
def SwitchOkC (c : CfgM) (id : w64) (s1 s' : NState) : Prop :=
  if s1.role = .leader then
    (if id ∈ c.voters then LeaderSwitchC c id s1 s'
     else ∃ pvs, s' = { becomeFollower s1 s1.term (W64 0) with prvals := pvs })
  else s' = s1

/-- What `switchToConfig` stores in `r.isLearner` at the configuration `c`: whether the node is
a learner of `c` (`ok && pr.IsLearner`; every learner is tracked, `LearnerFlagsC`). -/
def learnerOfC (c : CfgM) (id : w64) : Bool := decide (id ∈ c.learners)

theorem LeaderSwitchC.simple {cfg lrn : GSet w64} {id : w64} {s1 s' : NState} (hne : cfg ≠ ∅)
    (h : LeaderSwitchC (CfgM.simple cfg lrn) id s1 s') : LeaderSwitch cfg id s1 s' := by
  obtain ⟨n, ms, pvs2, lt', hn, h2, h3, h4⟩ := h
  exact ⟨n, ms, pvs2, lt', hn.imp_right (fun h => h.simple hne), h2, h3, h4⟩

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
the wand that re-seals it at any tracker of `cfg` (`ownRaftPhys_reconfig`'s) -- with what of
the old tracker survives, its tally and inflight bound (`ownTracker_votes`), and the new
`Config` and progress map as `ownConfigV` (`pvs` the new `Progress` records). Taking the
struct open lets the caller move the old `Progress` objects' resources to the new ones before
the call: `ApplyConfChange`'s new `Progress` objects are copies that share the old ones'
`Inflights` (`ownNewPr_transfer`). (Until 2026-10-13 it took `ownRaftPhys cfg0` sealed and
`ownConfig`, the non-leader case only: that statement is `raft.switchToConfig.spec_nonleader`
below.)

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
joint-quorum commit, `LeaderSwitchC`) or is removed or demoted and steps down: the premise
`s.sdr = true` (`Config.StepDownOnRemoval`), since otherwise it would stay leader outside the
configuration, which `ownRaftPhysC`'s `Hvoter` excludes. A candidate or pre-candidate must
stay a voter, for the same reason (the Go code leaves it campaigning; if it then won,
`becomeLeader` would dereference its missing `Progress`: see
`issues/raft-advance-before-applyconfchange.md`, which is how an application gets there).
The result is `SwitchOkC`, from `{ s with progress, prvals, isLearner := learnerOfC c id }`.
The statement on `ownRaftPhys` is `raft.switchToConfig.specS`, which gained the candidate
premise. -/
abbrev raft.switchToConfig.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (tv0 : tracker.ProgressTracker)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
  (s.role = .leader →
    (id ∈ c.voters ∧ MatchKept s.prvals pvs) ∨ (id ∉ c.voters ∧ s.sdr = true)) →
  (s.role = .candidate ∨ s.role = .preCandidate → id ∈ c.voters) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htrkf" ∷ r.[raft, go!"trk"] ↦ tv0 ∗
      "Hback" ∷ (∀ tv' prs' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTrackerC c tv' ⟨s.votes, prs', pvs'⟩ -∗
           ownRaftPhysCV c (c.voters ∪ {[id]}) r id { s with progress := prs', prvals := pvs' }) ∗
      "Hvotes" ∷ tv0.Votes' ↦$ s.votes ∗
      "%Hmi" ∷ ⌜0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62⌝ ∗
      "Hnew" ∷ ownConfigC c cfgv prsm prs pvs }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
      (Val #cfgv)) (Val #prsm))
  {{ (cs : raftpb.ConfState) (xs os ls lns : List w64) (s' : NState), RET #cs;
      ownRaftPhysCV c c.voters r id s' ∗
      cs.Voters' ↦* xs ∗ cs.VotersOutgoing' ↦* os ∗ cs.Learners' ↦* ls ∗
      cs.LearnersNext' ↦* lns ∗
      ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
        lns ≡ₚ elements c.learnersNext ∧ cs.AutoLeave' = c.autoLeave⌝ ∗
      ⌜SwitchOkC c id { s with progress := prs, prvals := pvs, isLearner := learnerOfC c id }
        s'⌝ }}

/-- The statement on `ownRaftPhys` (a simple configuration `cfg`) until 2026-10-13, with one
premise added: a candidate or pre-candidate stays a voter. Derived by `spec_simple`. -/
abbrev raft.switchToConfig.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (tv0 : tracker.ProgressTracker)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
  (s.role = .leader → id ∈ cfg ∧ MatchKept s.prvals pvs) →
  (s.role = .candidate ∨ s.role = .preCandidate → id ∈ cfg) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htrkf" ∷ r.[raft, go!"trk"] ↦ tv0 ∗
      "Hback" ∷ (∀ tv' prs' pvs', r.[raft, go!"trk"] ↦ tv' -∗
           ownTracker cfg tv' ⟨s.votes, prs', pvs'⟩ -∗
           ownRaftPhys cfg r id { s with progress := prs', prvals := pvs' }) ∗
      "Hvotes" ∷ tv0.Votes' ↦$ s.votes ∗
      "%Hmi" ∷ ⌜0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62⌝ ∗
      "Hnew" ∷ ownConfigV cfg cfgv prsm prs pvs }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
      (Val #cfgv)) (Val #prsm))
  {{ (cs : raftpb.ConfState) (xs ls : List w64) (s' : NState), RET #cs;
      ownRaftPhys cfg r id s' ∗
      cs.Voters' ↦* xs ∗ cs.Learners' ↦* ls ∗
      ⌜xs ≡ₚ elements cfg ∧ ls ≡ₚ elements (domSet prs \ cfg) ∧
        cs.VotersOutgoing'.len = W64 0 ∧
        cs.LearnersNext'.len = W64 0 ∧
        cs.AutoLeave' = false⌝ ∗
      ⌜SwitchOk cfg id { s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id }
        s'⌝ }}

open Iris.ProofMode in
theorem raft.switchToConfig.spec_simple
    (H : raft.switchToConfig.spec (GF := GF) (hG := hG)) :
    raft.switchToConfig.specS (GF := GF) (hG := hG) := by
  intro cfg r id s tv0 cfgv prsm prs pvs Hlead Hcand
  iintro %Φ ⟨#Hpkg, Htrkf, Hback, Hvotes, %Hmi, Hnew⟩ HΦ
  ihave Hnew := ownConfigV_toC _ _ _ _ _ $$ Hnew
  iapply H (CfgM.simple cfg (domSet prs \ cfg)) r id s tv0 cfgv prsm prs pvs
      (fun hl => .inl (by rw [CfgM.voters_simple]; exact Hlead hl))
      (fun hc => by rw [CfgM.voters_simple]; exact Hcand hc)
    $$ [$Hpkg $Htrkf Hback $Hvotes $Hnew]
  · isplitl [Hback]
    · iintro %tv' %prs' %pvs' Hf Ht
      icases ownTrackerC_toTracker _ _ _ _ $$ Ht with ⟨Ht, %HL⟩
      ihave Hp := Hback $$ %tv' %prs' %pvs' Hf Ht
      ihave Hp := ownRaftPhys_toC' $$ Hp
      simp only at HL
      rw [HL]
      iapply ownRaftPhysCV_widen _ _ _ _ _ ?_ $$ Hp
      intro h hr
      exact GMap.elem_of_union_l _ (h hr)
    · ipureintro; exact Hmi
  inext
  iintro %cs %xs %os %ls %lns %s' ⟨Hphys, Hxs, Hos, Hls, Hlns, %Hcs, %Hsw⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  obtain ⟨H1, H2, H3, H4, H5⟩ := Hcs
  have Hos0 : os = [] := perm_elements_empty _ H2
  have Hlns0 : lns = [] := perm_elements_empty _ H4
  subst Hos0 Hlns0
  ihave %Hol := ownSlice_len $$ Hos
  ihave %Hll := ownSlice_len $$ Hlns
  iapply HΦ $$ %cs %xs %ls %s'
  iframe Hphys Hxs Hls
  ipureintro
  refine ⟨⟨H1, H3, ?_, ?_, H5⟩, ?_⟩
  · simp at Hol; word
  · simp at Hll; word
  · rw [learnerOfC_simple] at Hsw
    unfold SwitchOkC at Hsw
    unfold SwitchOk
    split
    · rename_i hl
      have hin : id ∈ cfg := (Hlead hl).1
      rw [if_pos hl, if_pos (by rw [CfgM.voters_simple]; exact hin)] at Hsw
      exact Hsw.simple (fun h => by rw [h] at hin; exact GMap.not_elem_of_empty _ hin)
    · rename_i hl
      rw [if_neg hl] at Hsw
      exact Hsw

/-- At a follower, from the struct sealed at any configuration `cfg0` and the new
configuration as `confchange.Restore` builds it (`ownConfig`), with the learners `lrn`
(2026-10-13): what `restore` calls. -/
theorem raft.switchToConfig.spec_follower
    (H : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (cfg0 cfg lrn : GSet w64) (r : Loc) (id : w64) (s : NState)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (Hrole : s.role = .follower)
    (Hdom : domSet prs = cfg ∪ lrn) (Hd : ∀ k, k ∈ lrn → k ∉ cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg0 r id s ∗
        ownConfig cfg cfgv prsm prs }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
        (Val #cfgv)) (Val #prsm))
    {{ (cs : raftpb.ConfState) (xs ls : List w64)
        (pvs : GMap w64 Progress), RET #cs;
        ownRaftPhys cfg r id { s with progress := prs, prvals := pvs,
                                      isLearner := learnerOf cfg prs id } ∗
        cs.Voters' ↦* xs ∗ cs.Learners' ↦* ls ∗
        ⌜xs ≡ₚ elements cfg ∧ ls ≡ₚ elements lrn ∧
          cs.VotersOutgoing'.len = W64 0 ∧
          cs.LearnersNext'.len = W64 0 ∧
          cs.AutoLeave' = false⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hphys, Hcfg⟩ HΦ
  icases ownRaftPhys_reconfig cfg0 cfg r id s (fun h => absurd Hrole h) $$ Hphys
    with ⟨%tv, Htrkf, Hold, Hback⟩
  icases ownTracker_votes $$ Hold with ⟨Hvotes, %Hmi⟩
  icases ownConfig_values $$ Hcfg with ⟨%pvs, Hcfg⟩
  iapply (raft.switchToConfig.spec_simple H) cfg r id s tv cfgv prsm prs pvs
      (fun h => absurd (Hrole.symm.trans h) (by decide))
      (fun h => by rcases h with h | h <;> rw [Hrole] at h <;> cases h)
    $$ [$Hpkg $Htrkf $Hback $Hvotes $Hcfg]
  · ipureintro; exact Hmi
  inext
  iintro %cs %xs %ls %s' ⟨Hphys, Hcs, Hls, %Hcs0, %Hsw⟩
  unfold SwitchOk at Hsw
  rw [if_neg (by rw [Hrole]; decide)] at Hsw
  subst Hsw
  have Hl : domSet prs \ cfg = lrn := by
    rw [Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_difference, GMap.elem_of_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
    · intro h; exact ⟨.inr h, Hd k h⟩
  iapply HΦ $$ %cs %xs %ls %pvs
  iframe Hphys Hcs Hls
  ipureintro
  exact ⟨Hcs0.1, Hl ▸ Hcs0.2.1, Hcs0.2.2⟩

/-- The statement until 2026-10-13: at a non-leader, from the struct sealed at any
configuration `cfg0` and the new configuration as `confchange.Restore` builds it
(`ownConfig`), with no learners (`domSet prs = cfg`). What `newRaft` and `restore` call. -/
theorem raft.switchToConfig.spec_nonleader
    (H : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (cfg0 cfg : GSet w64) (r : Loc) (id : w64) (s : NState)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (Hrole : s.role = .follower)
    (Hdom : domSet prs = cfg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg0 r id s ∗
        ownConfig cfg cfgv prsm prs }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"switchToConfig"))
        (Val #cfgv)) (Val #prsm))
    {{ (cs : raftpb.ConfState) (xs : List w64)
        (pvs : GMap w64 Progress), RET #cs;
        ownRaftPhys cfg r id { s with progress := prs, prvals := pvs, isLearner := false } ∗
        cs.Voters' ↦* xs ∗ ⌜xs ≡ₚ elements cfg⌝ ∗
        ⌜cs.VotersOutgoing'.len = W64 0 ∧
          cs.Learners'.len = W64 0 ∧
          cs.LearnersNext'.len = W64 0 ∧
          cs.AutoLeave' = false⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hphys, Hcfg⟩ HΦ
  icases ownRaftPhys_reconfig cfg0 cfg r id s (fun h => absurd Hrole h) $$ Hphys with ⟨%tv, Htrkf, Hold, Hback⟩
  icases ownTracker_votes $$ Hold with ⟨Hvotes, %Hmi⟩
  icases ownConfig_values $$ Hcfg with ⟨%pvs, Hcfg⟩
  iapply (raft.switchToConfig.spec_simple H) cfg r id s tv cfgv prsm prs pvs
      (fun h => absurd (Hrole.symm.trans h) (by decide))
      (fun h => by rcases h with h | h <;> rw [Hrole] at h <;> cases h)
    $$ [$Hpkg $Htrkf $Hback $Hvotes $Hcfg]
  · ipureintro; exact Hmi
  inext
  iintro %cs %xs %ls %s' ⟨Hphys, Hcs, Hls, %Hcs0, %Hsw⟩
  unfold SwitchOk at Hsw
  rw [if_neg (by rw [Hrole]; decide)] at Hsw
  subst Hsw
  have HL : learnerOf cfg prs id = false := by
    unfold learnerOf; rw [Hdom]; simp
  have Hls0 : ls = [] := by
    have h := Hcs0.2.1.length_eq
    rw [Hdom, GMap.length_elements] at h
    have h2 : cfg \ cfg = (∅ : GSet w64) := by
      apply GMap.set_eq; intro k
      rw [GMap.elem_of_difference]
      exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (GMap.not_elem_of_empty _)⟩
    rw [h2, GMap.size_empty] at h
    exact List.eq_nil_of_length_eq_zero h
  subst Hls0
  ihave %Hll := ownSlice_len $$ Hls
  iapply HΦ $$ %cs %xs %pvs
  rw [HL]
  iframe Hphys Hcs
  ipureintro
  refine ⟨Hcs0.1, Hcs0.2.2.1, ?_, Hcs0.2.2.2⟩
  simp at Hll; word

end spec

end EtcdGrove
end Perennial
