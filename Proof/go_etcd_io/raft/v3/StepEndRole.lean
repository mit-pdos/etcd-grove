/-
Antithesis parity B1, phase 2 (#33, `notes/antithesis-parity-design.md` §2), step C. **The role facts of a
network message's `Step`** (`RnScope`'s last three conjuncts across `RawNode.Step`): a node is a
pre-candidate after a B1 network message only if it was one before, with its leader (none) kept and its
tally kept or (a pre-vote response, `poll` pending) not a quorum; a follower leaves the follower role only
as a voter (`MsgTimeoutNow`'s `hup`, `HupOkC`'s `id ∉ voters → s' = s`). By the step function's role
(`roleFn_of_stepFn`), through the preamble (`RoleFn.ofPre`), at `StepEnd` (`roleFn_of_stepEnd`).
-/
module

public import Proof.go_etcd_io.raft.v3.StepEndNetK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

set_option hygiene false in
/-- A message type constant decided (`InputEndLift.lean`'s `ie_tyclose`). -/
local syntax "nk_tyclose " term : tactic
macro_rules
  | `(tactic| nk_tyclose $e:term) =>
    `(tactic| simp only [$e:term, Perennial.W32, BitVec.ofInt_ofNat, BitVec.reduceEq,
      Perennial.EtcdGrove.MsgBeat, Perennial.EtcdGrove.MsgHup,
      Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp, Perennial.EtcdGrove.MsgAppResp,
      Perennial.EtcdGrove.MsgVote, Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
      Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,
      Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
      Perennial.EtcdGrove.MsgReadIndex, Perennial.EtcdGrove.MsgReadIndexResp,
      Perennial.EtcdGrove.MsgForgetLeader, Perennial.EtcdGrove.MsgUnreachable,
      Perennial.EtcdGrove.MsgSnapStatus, Perennial.EtcdGrove.MsgTransferLeader,
      Perennial.EtcdGrove.MsgTimeoutNow, Perennial.EtcdGrove.MsgCheckQuorum,
      Perennial.EtcdGrove.UnstampedType,
      ↓reduceIte, _root_.true_and, _root_.false_and, _root_.and_true, _root_.and_false, _root_.true_or,
      _root_.false_or, _root_.or_true,
      _root_.or_false, _root_.not_true_eq_false, _root_.not_false_eq_true, ne_eq, _root_.iff_self,
      _root_.and_self, _root_.not_and, Bool.false_eq_true, ite_true, ite_false])


local syntax "se_tysimp " term " at " ident : tactic
macro_rules
  | `(tactic| se_tysimp $e:term at $h:ident) =>
    `(tactic| simp only [$e:term, Perennial.W32, BitVec.ofInt_ofNat, BitVec.reduceEq, Perennial.EtcdGrove.MsgBeat, Perennial.EtcdGrove.MsgHup,
      Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp, Perennial.EtcdGrove.MsgAppResp,
      Perennial.EtcdGrove.MsgVote, Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
      Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,
      Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
      Perennial.EtcdGrove.MsgReadIndex, Perennial.EtcdGrove.MsgReadIndexResp,
      Perennial.EtcdGrove.MsgForgetLeader, Perennial.EtcdGrove.MsgUnreachable,
      Perennial.EtcdGrove.MsgSnapStatus, Perennial.EtcdGrove.MsgTransferLeader,
      Perennial.EtcdGrove.MsgTimeoutNow, Perennial.EtcdGrove.MsgCheckQuorum,
      ↓reduceIte, _root_.true_and, _root_.false_and, _root_.and_true, _root_.and_false, _root_.true_or, _root_.false_or, _root_.or_true,
      _root_.or_false, _root_.not_true_eq_false, _root_.not_false_eq_true] at $h:ident)


section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The role facts of a step from `t` to `s'`** at the configuration `c`: a pre-candidate after was one
before, its leader kept, its tally kept or not a quorum; a follower before is past the follower role after
only as a voter. -/
def RoleFn (c : CfgM) (id : w64) (t s' : NState) : Prop :=
  (s'.role = .preCandidate → t.role = .preCandidate ∧ s'.lead = t.lead ∧
     (s'.votes = t.votes ∨ ¬ JQuorum c (granted s'.votes))) ∧
  (t.role = .follower → s'.role ≠ .follower → id ∈ c.voters)

theorem RoleFn.of_follower {c : CfgM} {id : w64} {t s' : NState} (h : s'.role = .follower) :
    RoleFn c id t s' :=
  ⟨fun hp => (by rw [h] at hp; cases hp), fun _ hn => absurd h hn⟩

theorem RoleFn.nf {c : CfgM} {id : w64} {t s' : NState} (ht : t.role ≠ .follower)
    (hp : s'.role ≠ .preCandidate) : RoleFn c id t s' :=
  ⟨fun h => absurd h hp, fun h => absurd h ht⟩

theorem RoleFn.keep {c : CfgM} {id : w64} {t s' : NState} (hr : s'.role = t.role)
    (hl : s'.lead = t.lead) (hv : s'.votes = t.votes) : RoleFn c id t s' :=
  ⟨fun h => ⟨(by rw [← hr]; exact h), hl, .inl hv⟩, fun h hn => absurd (hr.trans h) hn⟩

/-- Through `Step`'s preamble: its step-down makes a follower. -/
theorem RoleFn.ofPre {c : CfgM} {id : w64} {s : NState} {m : MessageM} {pvs : GMap w64 Progress}
    {s' : NState} (h : RoleFn c id (preState s m pvs) s') : RoleFn c id s s' := by
  unfold preState at h
  split at h
  · refine ⟨fun hp => ?_, fun _ hn => h.2 (by simp [becomeFollower, resetTo, resetTo0]) hn⟩
    have h2 := (h.1 hp).1
    simp [becomeFollower, resetTo, resetTo0] at h2
  · exact h

theorem RoleFn.voteEnd {c : CfgM} {id : w64} {t : NState} {m : MessageM} {s' : NState}
    (h : VoteEnd id t m s') : RoleFn c id t s' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact RoleFn.keep rfl rfl rfl

set_option maxHeartbeats 1000000 in
theorem roleFn_fol {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hr : t.role = .follower) (hty : m.Type' ∈ netTypesK)
    (H : StepFnEnd c id t m ents ctx s') : RoleFn c id t s' := by
  obtain ⟨scfg, sv, d, c', hres⟩ := H.1 hr
  unfold FollowerStepResultC at hres
  obtain ⟨-, hres⟩ := hres
  rcases netTypesK_cases hty with e | e | e | e | e | e | e | e | e | e | e | e <;> se_tysimp e at hres
  all_goals first
    | exact hres.elim
    | (obtain ⟨-, hup, hpc⟩ := hres
       refine ⟨fun hp => ?_, fun _ hn => Classical.byContradiction fun hv => hn ?_⟩
       · have h2 := (hpc hp).symm.trans hp; rw [hr] at h2; cases h2
       · rw [hup.2.2.2.1 hv]; exact hr)
    | (obtain ⟨-, rfl⟩ := hres; exact RoleFn.of_follower hr)
    | (obtain ⟨-, rfl⟩ := hres
       exact RoleFn.of_follower (by simp [sendMsgs, heartbeatResult, addReadState, hr]))
    | (obtain ⟨-, hres⟩ := hres; exact RoleFn.of_follower (by rw [(bk_handleApp hres).1]; exact hr))
    | (obtain ⟨-, hres⟩ := hres
       split at hres <;> subst hres <;> exact RoleFn.of_follower (by simp [sendMsgs, addReadState, hr]))

set_option maxHeartbeats 1000000 in
theorem roleFn_cand {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hr : t.role = .candidate) (hty : m.Type' ∈ netTypesK)
    (H : StepFnEnd c id t m ents ctx s') : RoleFn c id t s' := by
  refine RoleFn.nf (by rw [hr]; exact fun h => by cases h) ?_
  obtain ⟨scfg, sv, d, c', hres⟩ := H.2.1 (.inl hr)
  unfold CandidateStepResultC at hres
  obtain ⟨-, hres⟩ := hres
  rcases netTypesK_cases hty with e | e | e | e | e | e | e | e | e | e | e | e <;> se_tysimp e at hres
  all_goals try rw [if_neg (by rw [hr]; exact fun h => by cases h)] at hres
  all_goals first
    | exact hres.elim
    | (obtain ⟨-, rfl⟩ := hres; rw [hr]; exact fun h => by cases h)
    | (obtain ⟨-, won, lost, ms, pvs, -, -, -, rfl⟩ := hres
       cases won <;> cases lost <;>
         simp [voteRespResult, sendMsgs, becomeLeader, becomeFollower, resetTo, resetTo0, hr])
    | (obtain ⟨-, pvs, hres⟩ := hres
       rw [(bk_handleApp hres).1]; simp [becomeFollower, resetTo, resetTo0])
    | (obtain ⟨-, pvs, rfl⟩ := hres
       simp [heartbeatResult, sendMsgs, becomeFollower, resetTo, resetTo0])

set_option maxHeartbeats 1000000 in
theorem roleFn_pre {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hr : t.role = .preCandidate) (hty : m.Type' ∈ netTypesK)
    (H : StepFnEnd c id t m ents ctx s') : RoleFn c id t s' := by
  obtain ⟨scfg, sv, d, c', hres⟩ := H.2.1 (.inr hr)
  unfold CandidateStepResultC at hres
  obtain ⟨-, hres⟩ := hres
  rcases netTypesK_cases hty with e | e | e | e | e | e | e | e | e | e | e | e <;> se_tysimp e at hres
  all_goals try rw [if_pos hr] at hres
  all_goals first
    | exact hres.elim
    | (obtain ⟨-, rfl⟩ := hres; exact RoleFn.keep rfl rfl rfl)
    | (obtain ⟨-, pvs, hres⟩ := hres
       exact RoleFn.of_follower (by rw [(bk_handleApp hres).1]; simp [becomeFollower, resetTo, resetTo0]))
    | (obtain ⟨-, pvs, rfl⟩ := hres
       exact RoleFn.of_follower (by simp [heartbeatResult, sendMsgs, becomeFollower, resetTo, resetTo0]))
    | (obtain ⟨-, won, lost, peers, pvs, -, -, hnw, rfl⟩ := hres
       cases won
       · cases lost
         · refine ⟨fun _ => ⟨hr, (by simp [prevoteRespResult]), .inr ?_⟩, fun h => (by rw [hr] at h; cases h)⟩
           simp only [prevoteRespResult, Bool.false_eq_true, ↓reduceIte]
           exact hnw rfl
         · exact RoleFn.of_follower (by simp [prevoteRespResult, becomeFollower, resetTo, resetTo0])
       · exact RoleFn.nf (by rw [hr]; exact fun h => by cases h)
           (by simp [prevoteRespResult, campaignState, sendMsgs, becomeCandidate]))

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem roleFn_lead {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hr : t.role = .leader) (H : StepFnEnd c id t m ents ctx s') :
    RoleFn c id t s' := by
  obtain ⟨d, hres⟩ := H.2.2 hr
  exact RoleFn.nf (by rw [hr]; exact fun h => by cases h) (StepProof.LeaderStepResultC.not_precand hr hres)

/-- **A step function's role facts**, at every role (but on a snapshot). -/
theorem roleFn_of_stepFn {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hty : m.Type' ∈ netTypesK) (H : StepFnEnd c id t m ents ctx s') :
    RoleFn c id t s' := by
  cases hr : t.role with
  | follower => exact roleFn_fol hr hty H
  | candidate => exact roleFn_cand hr hty H
  | preCandidate => exact roleFn_pre hr hty H
  | leader => exact roleFn_lead hr H

/-- `StepEndBody`'s role facts: a stale message's answer, a vote request's (through the preamble), the
step function's (through the preamble). -/
theorem roleFn_of_body {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hh : m.Type' ≠ MsgHup) (hty : m.Type' ∈ netTypesK)
    (h : StepEndBody c id m ents ctx s s') : RoleFn c id s s' := by
  obtain ⟨hst, -, hv, hfn⟩ := h
  by_cases hs : StaleMsg s m
  · rcases hst hs with rfl | ⟨_, _, -, rfl⟩
    · exact RoleFn.keep rfl rfl rfl
    · exact RoleFn.keep rfl rfl rfl
  by_cases hvt : m.Type' = MsgVote
  · rcases hv hs hvt with ⟨-, -, -, -, rfl⟩ | ⟨pvs, H⟩
    · exact RoleFn.keep rfl rfl rfl
    · exact (RoleFn.voteEnd H).ofPre
  · obtain ⟨pvs, H⟩ := hfn hs hh hvt
    exact (roleFn_of_stepFn hty H).ofPre

set_option maxHeartbeats 1000000 in
/-- **A B1 network message's role facts** (`RoleFn`) from `StepEnd`: the `StepEndTy` types by
`roleFn_of_body` (at the state with the transferee's acknowledgement recorded, `StepEnd.body_xt`, whose
role, leader and tally are the node's); a pre-vote request answered (`StepEnd.prevote`); a transfer request
stale, of a higher term (a follower) or current (`transferEnd_of_stepEnd_cur`: the role, leader and tally
kept). -/
theorem roleFn_of_stepEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hty : m.Type' ∈ netTypesK) (hpc : domSet s.progress = c.ids)
    (hns : NoSnapL s'.outbox) (h : StepEnd c id m ents ctx s s') : RoleFn c id s s' := by
  have hT : ∀ t : w32, m.Type' = t → StepEndTy t → StepEndTy m.Type' := fun t e h => e ▸ h
  have hB : StepEndTy m.Type' → m.Type' ≠ MsgHup → RoleFn c id s s' :=
    fun hT hh => by
      obtain ⟨Y, hb⟩ := h.body_xt hT
      exact (roleFn_of_body (s := { s with gh := { s.gh with xt := Y } }) hh hty hb : _)
  rcases netTypesK_cases hty with e | e | e | e | e | e | e | e | e | e | e | e
  rotate_left 6
  · -- `MsgPreVote`
    obtain ⟨hstl, hfr⟩ := h.prevote e
    by_cases hs : StaleMsg s m
    · rw [hstl hs]; exact RoleFn.keep rfl rfl rfl
    · rcases hfr hs with ⟨-, -, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact RoleFn.keep rfl rfl rfl
  rotate_left 3
  · -- `MsgTransferLeader`
    by_cases hst : StaleMsg s m
    · obtain ⟨X, Y, b, rfl⟩ := h.xstale hst e
      exact RoleFn.keep rfl rfl rfl
    by_cases hb : PreBF m s
    · obtain ⟨g, pvs, rfl⟩ := transferEnd_of_stepEnd_gt e hst hb h
      exact RoleFn.of_follower (by simp [becomeFollower, resetTo, resetTo0])
    · obtain ⟨g, l, o, pvs, rfl, -, -⟩ := transferEnd_of_stepEnd_cur e hst hb hpc hns h
      exact RoleFn.keep rfl rfl rfl
  all_goals
    exact hB (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)

end proof

end EtcdGrove
end Perennial
