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
then `false`). The `ConfState` has the learners too (the tracked ids outside `cfg`). -/
abbrev raft.switchToConfig.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (tv0 : tracker.ProgressTracker)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
  (s.role = .leader → id ∈ cfg ∧ MatchKept s.prvals pvs) →
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
  iapply H cfg r id s tv cfgv prsm prs pvs (fun h => absurd (Hrole.symm.trans h) (by decide))
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
  iapply H cfg r id s tv cfgv prsm prs pvs (fun h => absurd (Hrole.symm.trans h) (by decide))
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
