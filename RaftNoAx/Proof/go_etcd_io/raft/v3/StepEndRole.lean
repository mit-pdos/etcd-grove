-- The copy for the part `RaftNoAx/` of `Proof/go_etcd_io/raft/v3/StepEndRole.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Antithesis parity B1, phase 2 (#33, `notes/antithesis-parity-design.md` §2), step C. **The role facts of a
network message's `Step`** (`RnScope`'s last three conjuncts across `RawNode.Step`): a node is a
pre-candidate after a B1 network message only if it was one before, with its leader (none) kept and its
tally kept or (a pre-vote response, `poll` pending) not a quorum; a follower leaves the follower role only
as a voter (`MsgTimeoutNow`'s `hup`, `HupOkC`'s `id ∉ voters → s' = s`). By the step function's role
(`roleFn_of_stepFn`), through the preamble (`RoleFn.ofPre`), at `StepEnd` (`roleFn_of_stepEnd`).
-/
module

public import RaftNoAx.Proof.go_etcd_io.raft.v3.StepEndNetK

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

/-! ### The scope across a B1 network step (antithesis parity B1, step C1)

What `RawNode.Step` at a mode `md` (snapshots, configuration changes, forwarding and asynchronous storage
off) needs to keep `RnScope md` and the transfer scope's facts (`XScopeOk`): the read state at reads off
(no read-index type among the mode's), the protocol leader (kept, cleared, the sender, or the node itself
as leader), the configuration and the node's membership. -/

section scope
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]
variable {k : NodeK}

/-- At reads off the mode's types hold no read-index type; at transfer off no transfer type. -/
theorem stepTypes_off {md : RnMode} {t : w32} (h : t ∈ stepTypes md) :
    (md.reads = false → t ≠ MsgReadIndex ∧ t ≠ MsgReadIndexResp) ∧
    (md.transfer = false → t ≠ MsgTransferLeader ∧ t ≠ MsgTimeoutNow) := by
  unfold stepTypes antStepTypes at h
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, _root_.or_false] at h
  refine ⟨fun hr => ⟨fun e => ?_, fun e => ?_⟩, fun ht => ⟨fun e => ?_, fun e => ?_⟩⟩
  all_goals
    subst e; revert h
    first | rw [hr] | rw [ht]
    simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, _root_.or_false, _root_.false_or]
    repeat' split
    all_goals simp [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp,
      MsgPreVote, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp, MsgTransferLeader, MsgTimeoutNow,
      MsgProp, MsgSnap, MsgStorageAppendResp, MsgStorageApplyResp]

/-- No B1 network type is local (`IsLocalMsg`'s table). -/
theorem netTypesK_not_local {t : w32} (h : t ∈ netTypesK) : t ∉ localMsgTypes := by
  rcases netTypesK_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- No B1 network type is a snapshot. -/
theorem netTypesK_ne_snap {t : w32} (h : t ∈ netTypesK) : t ≠ MsgSnap := by
  rcases netTypesK_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- A B1 network type's protocol reading is no proposal and no snapshot. -/
theorem netTypesK_mtype {t : w32} (h : t ∈ netTypesK) {ty : MsgType} (hty : mtypeOf t = some ty) :
    ty ≠ .propose ∧ ty ≠ .snap := by
  rcases netTypesK_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases hty <;> exact ⟨by decide, by decide⟩

/-- A B1 network type without a protocol reading is a transfer type. -/
theorem netTypesK_untyped {t : w32} (h : t ∈ netTypesK) (hty : mtypeOf t = none) :
    t = MsgTransferLeader ∨ t = MsgTimeoutNow := by
  rcases netTypesK_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact .inl rfl | exact .inr rfl | cases hty

/-- A network `MsgReadIndex` is unstamped (term `0`, `NetMsgOk`). -/
theorem NetMsgOk.readIndex_term {id : w64} {st : MsgSt} (Hok : NetMsgOk id st)
    (e : st.msg.Type' = MsgReadIndex) : st.msg.Term' = W64 0 :=
  Hok.2.2.1 (by rw [e]; nk_tyclose MsgReadIndex) (by rw [e]; nk_tyclose MsgReadIndex)

/-- A network `MsgTimeoutNow` is stamped (a term past `0`, `NetMsgOk`). -/
theorem NetMsgOk.timeoutNow_term {id : w64} {st : MsgSt} (Hok : NetMsgOk id st)
    (e : st.msg.Type' = MsgTimeoutNow) : st.msg.Term' ≠ W64 0 :=
  (Hok.2.1 (by rw [e]; nk_tyclose MsgTimeoutNow)).2.1

theorem preadRespondAll_lead (id : w64) (s : PState) (qs : List ReadReq) :
    (preadRespondAll id s qs).lead = s.lead := by
  obtain ⟨o, rd, h⟩ := preadRespondAll_eq id s qs
  rw [h]

theorem SendsEnd.lead {c : CfgM} {id : w64} {s s' : PState} (h : SendsEnd c id s s') :
    s'.lead = s.lead := by
  obtain ⟨ms, -, rfl⟩ := h; rfl

theorem ReleaseEnd.lead {c : CfgM} {id : w64} {s s' : PState} (h : ReleaseEnd c id s s') :
    s'.lead = s.lead := by
  rcases h with ⟨-, hb, -, rfl⟩ | ⟨-, rfl⟩
  · rfl
  · exact preadRespondAll_lead id _ _

theorem ReadAckEnd.lead {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (h : ReadAckEnd c id s m s') : s'.lead = s.lead := by
  rcases h with ⟨-, rfl⟩ | ⟨N, -, rfl⟩
  · rfl
  · exact preadRespondAll_lead id _ _

/-- **The protocol leader after a handled message** (not a proposal, not a snapshot): kept, cleared,
the sender (an append or heartbeat adopts it), or the node itself as a new leader (`WinEnd`). -/
theorem handleEnd_lead {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty ≠ .propose ∧ m.ty ≠ .snap) (h : HandleEnd k c id s m s') :
    s'.lead = s.lead ∨ s'.lead = W64 0 ∨ s'.lead = m.src ∨ (s'.lead = id ∧ s'.role = .leader) := by
  unfold HandleEnd at h
  cases e : m.ty <;> rw [e] at h <;> simp only at h
  · left; rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, mt, ms, -, -, rfl⟩ | ⟨-, rfl⟩
      · exact .inl rfl
      · exact .inr (.inr (.inr ⟨rfl, rfl⟩))
      · exact .inr (.inl rfl)
    · subst h; exact .inl rfl
  · split at h
    · subst h; exact .inl rfl
    · right; right; left
      unfold AppEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, l, es, -, rfl⟩ | ⟨-, -, hi, ht, -, -, rfl⟩ <;> rfl
  · split at h
    · left
      unfold AppRespEnd at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩ | ⟨-, x, n, s2, -, -, hr, hs⟩
      · rfl
      · exact hs.lead
      · exact hs.lead
      · exact hs.lead.trans hr.lead
    · subst h; exact .inl rfl
  · split at h
    · subst h; exact .inl rfl
    · subst h; exact .inr (.inr (.inl rfl))
  · split at h
    · obtain ⟨s2, hs, ⟨-, rfl⟩ | ⟨-, ha⟩⟩ := h
      · exact .inl hs.lead
      · exact .inl (ha.lead.trans hs.lead)
    · subst h; exact .inl rfl
  · exact absurd e hty.1
  · exact absurd e hty.2
  · left; unfold PreVoteEndP at h; rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  · split at h
    · rcases h with rfl | ⟨-, peers, -, rfl⟩
      · exact .inl rfl
      · exact .inr (.inl rfl)
    · subst h; exact .inl rfl
  · left; unfold ReadIdxEnd at h
    split at h
    · rcases h with ⟨-, pm, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, ms, -, rfl⟩
      · rfl
      · exact preadRespondAll_lead id _ _
      · rfl
    · split at h <;> (subst h; rfl)
  · left; split at h
    · rcases h with ⟨e, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl
    · subst h; rfl

/-- **The protocol leader after a received message** (`RecvEnd`; not a proposal, not a snapshot): kept,
cleared, the sender, or the node itself as a new leader. -/
theorem recvEnd_lead {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty ≠ .propose ∧ m.ty ≠ .snap) (h : RecvEnd k c id s m s') :
    s'.lead = s.lead ∨ s'.lead = W64 0 ∨ s'.lead = m.src ∨ (s'.lead = id ∧ s'.role = .leader) := by
  rcases h with ⟨-, h⟩ | ⟨-, -, hs⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, h⟩
  · exact handleEnd_lead hty h
  · left; rcases hs with rfl | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl
  · exact .inl rfl
  · have h1 : s1.lead = s.lead ∨ s1.lead = W64 0 ∨ s1.lead = m.src := by
      rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · show (if fromLeader m.ty then m.src else W64 0) = s.lead ∨ _
        split
        · exact .inr (.inr rfl)
        · exact .inr (.inl rfl)
      · exact .inl rfl
      · exact .inl rfl
    rcases handleEnd_lead hty h with h2 | h2 | h2 | h2
    · rw [h2]
      rcases h1 with h1 | h1 | h1
      · exact .inl h1
      · exact .inr (.inl h1)
      · exact .inr (.inr (.inl h1))
    · exact .inr (.inl h2)
    · exact .inr (.inr (.inl h2))
    · exact .inr (.inr (.inr h2))

/-- **The read state after a handled message of no read-index type** (not a proposal, not a snapshot),
with no read request deferred and the read-only queue empty: both kept (a commit's release has nothing
to release; a new role's `reset` installs a fresh read-only object). -/
theorem handleEnd_rd_nr {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty ≠ .readIndex ∧ m.ty ≠ .readIndexResp ∧ m.ty ≠ .propose ∧ m.ty ≠ .snap)
    (h : HandleEnd k c id s m s') (hpd : s.rd.pend = []) (hp : s.rd.ro.pending = []) :
    s'.rd.pend = s.rd.pend ∧ s'.rd.ro.pending = [] := by
  have hold : (m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp) → s'.rd.pend = s.rd.pend ∧ s'.rd.ro.pending = [] := fun ho =>
    ⟨handleEnd_rd_pend ho h hpd, handleEnd_ro ho h hpd hp⟩
  cases e : m.ty
  all_goals first
    | exact absurd e hty.1
    | exact absurd e hty.2.1
    | exact absurd e hty.2.2.1
    | exact absurd e hty.2.2.2
    | (apply hold; simp [e]; done)
    | skip
  · unfold HandleEnd at h; rw [e] at h; simp only at h
    unfold PreVoteEndP at h
    rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact ⟨rfl, hp⟩
  · unfold HandleEnd at h; rw [e] at h; simp only at h
    split at h
    · rcases h with rfl | ⟨-, peers, -, rfl⟩
      · exact ⟨rfl, hp⟩
      · exact ⟨rfl, rfl⟩
    · subst h; exact ⟨rfl, hp⟩

/-- `handleEnd_rd_nr` through `RecvEnd` (the preamble's `becomeFollower` installs a fresh read-only
object; a stale message's answer keeps the read state). -/
theorem recvEnd_rd_nr {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hty : m.ty ≠ .readIndex ∧ m.ty ≠ .readIndexResp ∧ m.ty ≠ .propose ∧ m.ty ≠ .snap)
    (h : RecvEnd k c id s m s') (hpd : s.rd.pend = []) (hp : s.rd.ro.pending = []) :
    s'.rd.pend = s.rd.pend ∧ s'.rd.ro.pending = [] := by
  rcases h with ⟨-, h⟩ | ⟨-, -, hs⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, h⟩
  · exact handleEnd_rd_nr hty h hpd hp
  · rw [hs.rd]; exact ⟨rfl, hp⟩
  · exact ⟨rfl, hp⟩
  · have hp1 : s1.rd.ro.pending = [] := by
      rcases hpre with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩
      · rfl
      · exact hp
      · exact hp
    obtain ⟨h1, h2⟩ := handleEnd_rd_nr hty h (by rw [hpre.rd_pend]; exact hpd) hp1
    exact ⟨h1.trans hpre.rd_pend, h2⟩

/-- **A received `MsgTimeoutNow`'s read state and leader** (`TimeoutNowEndR`): the read requests kept,
an empty read-only queue kept empty, the leader kept or cleared. -/
theorem TimeoutNowEndR.rd_lead {id : w64} {r : RState} {x : XMsg} {r' : RState}
    (h : TimeoutNowEndR id r x r') :
    r'.p.rd.pend = r.p.rd.pend ∧ (r.p.rd.ro.pending = [] → r'.p.rd.ro.pending = []) ∧
      (r'.p.lead = r.p.lead ∨ r'.p.lead = W64 0) := by
  rcases h with ⟨-, rfl⟩ | ⟨-, ⟨p1, hp1, hr⟩, -⟩
  · exact ⟨rfl, fun hp => hp, .inl rfl⟩
  · rcases hr with e | ⟨-, ms, -, e⟩ | ⟨-, -, peers, -, e⟩ <;>
      rcases hp1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rw [e] <;>
      first | exact ⟨rfl, fun _ => rfl, .inr rfl⟩ | exact ⟨rfl, fun hp => hp, .inl rfl⟩

/-- **A received `MsgTransferLeader`'s read state and leader** (`TransferRecvEndR`): as
`TimeoutNowEndR.rd_lead`. -/
theorem TransferRecvEndR.rd_lead {id : w64} {r : RState} {x : XMsg} {r' : RState}
    (h : TransferRecvEndR id r x r') :
    r'.p.rd.pend = r.p.rd.pend ∧ (r.p.rd.ro.pending = [] → r'.p.rd.ro.pending = []) ∧
      (r'.p.lead = r.p.lead ∨ r'.p.lead = W64 0) := by
  rcases h with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, hp'⟩ | ⟨-, rfl⟩
  · exact ⟨rfl, fun hp => hp, .inl rfl⟩
  · rcases hp' with e | ⟨-, -, -, ms, -, e⟩ <;> rw [e]
    · exact ⟨rfl, fun hp => hp, .inl rfl⟩
    · exact ⟨rfl, fun hp => hp, .inl rfl⟩
  · exact ⟨rfl, fun _ => rfl, .inr rfl⟩

/-- A B1 network type of no read-index type has no read-index protocol reading. -/
theorem netTypesK_mtype_rd {t : w32} (h : t ∈ netTypesK) {ty : MsgType} (hty : mtypeOf t = some ty)
    (h1 : t ≠ MsgReadIndex) (h2 : t ≠ MsgReadIndexResp) : ty ≠ .readIndex ∧ ty ≠ .readIndexResp := by
  rcases netTypesK_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases hty <;> first | exact ⟨by decide, by decide⟩ | exact absurd rfl h1 | exact absurd rfl h2

theorem absMsg_src_eq (ty : MsgType) (m : MessageM) (ents : List EntryM) (ctx : List w8) :
    (absMsg ty m ents ctx).src = m.From' := by
  simp [absMsg, absMsgFrom, Msg.mkV]

/-- (antithesis parity B1, step C1) **The scope's configuration at a mode without configuration
changes**: `CfgScope`, no learners, the node's configuration the step's. -/
theorem cfgScope_ofMd {md : RnMode} {γ : RaftNames} {id : w64} {rs : RNState} {s : NState} {c : CfgM}
    (hcc : md.confChanges = false) (Hs : RnScope md id rs s) (Hc : RnCfgIn md γ id rs)
    (Hm : (rs.mode.isDyn = false → CfgStatic γ c) ∧ (rs.mode.isDyn = true → rs.cfg.cfg = c)) :
    CfgScope γ c ∧ c.learners = ∅ ∧ rs.cfg.cfg = c := by
  have hd := Hc.2.2.2
  have hcf := Hm.2 hd
  subst hcf
  exact ⟨⟨(Hc.2.1 hcc).1 hd, Hs.1 hcc hd, trivial⟩, (Hc.2.1 hcc).2, rfl⟩

/-- A member of a configuration without learners is a voter. -/
theorem CfgM.voter_of_ids {c : CfgM} {i : w64} (hl : c.learners = ∅) (h : i ∈ c.ids) : i ∈ c.voters := by
  unfold CfgM.ids at h; rw [hl, GMap.union_empty_r_L] at h; exact h

/-- (step C1) **`LiftScopeK` from the scope at a mode** without configuration changes: the node constant
from `KTie`, a pre-candidate's leader none (`RnScope`), a non-follower in the progress map (with
non-voters off a member of the names' voters, `RnCfgIn`; on, `RnScope`'s last conjunct). -/
theorem liftScopeK_of {md : RnMode} {γ : RaftNames} {id : w64} {rs : RNState} {s : NState} {c : CfgM}
    (hcc : md.confChanges = false) (Hs : RnScope md id rs s) (Hc : RnCfgIn md γ id rs) (Hk : KTie rs s)
    (HC : CfgScope γ c) (Hpre : s.role = .preCandidate → s.prevote = true)
    (Hfv : FollowerVotesOk (toPState s)) (Hd1 : domSet s.prvals = domSet s.progress)
    (Hd2 : domSet s.progress = c.ids) : LiftScopeK rs.k c id s := by
  obtain ⟨-, h2, -, -, -, -, -, h8, h9⟩ := Hs
  refine ⟨by rw [← Hk], by rw [← Hk], fun hr => ?_, Hfv, Hd1, fun hf => ?_, Hd2⟩
  · cases hp : md.prevote
    · have := Hpre hr; rw [h2 hp] at this; cases this
    · exact h8 hp hr
  · cases hnv : md.nonVoters
    · rw [Hd1, Hd2]; exact GMap.elem_of_union_l c.learners (by rw [HC.voters]; exact Hc.1 hnv)
    · exact h9 hcc hnv hf

/-- (step C1) A pre-candidate's tally is not a quorum (`RnScope`; at pre-vote off no pre-candidate). -/
theorem preCand_noQuorum_of {md : RnMode} {id : w64} {rs : RNState} {s : NState} {c : CfgM}
    (hcc : md.confChanges = false) (Hs : RnScope md id rs s) (hc : rs.cfg.cfg = c)
    (Hpre : s.role = .preCandidate → s.prevote = true) :
    s.role = .preCandidate → ¬ JQuorum c (granted s.votes) := by
  intro hr
  cases hp : md.prevote
  · have := Hpre hr; rw [Hs.2.1 hp] at this; cases this
  · rw [← hc]; exact Hs.2.2.2.2.2.2.1 hcc hp hr

/-- (step C1) **A non-follower after a step is a member of the names' voters** (with non-voters off by
`RnCfgIn`; on, a follower became one only as a voter, `RoleFn`, else it was in the progress map before). -/
theorem id_mem_of_roleFn {md : RnMode} {γ : RaftNames} {id : w64} {rs : RNState} {s s' : NState}
    {c : CfgM} (hcc : md.confChanges = false) (Hs : RnScope md id rs s) (Hc : RnCfgIn md γ id rs)
    (HC : CfgScope γ c) (hl : c.learners = ∅)
    (hfol : s.role = .follower → s'.role ≠ .follower → id ∈ c.voters)
    (Hd : domSet s.prvals = domSet s.progress ∧ domSet s.progress = c.ids)
    (hnf : s'.role ≠ .follower) : id ∈ γ.reCfg := by
  cases hnv : md.nonVoters
  · exact Hc.1 hnv
  · rw [← HC.voters]
    by_cases hf : s.role = .follower
    · exact hfol hf hnf
    · have h := Hs.2.2.2.2.2.2.2.2 hcc hnv hf
      rw [Hd.1, Hd.2] at h
      exact CfgM.voter_of_ids hl h

/-- (step C1) **`RnScope md` after a B1 network step**: the configuration and the flags kept; the read
state at reads off (`hrd`); no snapshot (`hsn`); no transfer request stepped at transfer off (`hxs`); the
pre-candidate facts and the node's membership from the role facts (`RoleFn`) and the progress maps' domains
before and after. -/
theorem RnScope.stepG {md : RnMode} {γ : RaftNames} {id : w64} {rs rs' : RNState} {s s' : NState}
    {c : CfgM} (hcc : md.confChanges = false) (Hs : RnScope md id rs s) (Hc : RnCfgIn md γ id rs)
    (HC : CfgScope γ c) (hl : c.learners = ∅) (hc : rs.cfg.cfg = c)
    (hm : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg ∧ rs'.slent = rs.slent)
    (hpv : s'.prevote = s.prevote) (hcq : s'.cq = s.cq)
    (hrd : md.reads = false → s'.rd.pend = s.rd.pend ∧
      ((toPState s).rd.ro.pending = [] → (toPState s').rd.ro.pending = []))
    (hsn : md.snapshots = false → s'.logst.prev = s.logst.prev ∧ s'.logst.snap = s.logst.snap ∧
      NoSnapL s'.outbox)
    (hxs : md.transfer = false → s'.gh.xs = s.gh.xs)
    (hpre : s'.role = .preCandidate →
      (s.role = .preCandidate ∧ s'.lead = s.lead ∧ (s'.votes = s.votes ∨ ¬ JQuorum c (granted s'.votes))) ∨
      (s'.lead = W64 0 ∧ ¬ JQuorum c (granted s'.votes)))
    (hfol : s.role = .follower → s'.role ≠ .follower → id ∈ c.voters)
    (Hd : domSet s.prvals = domSet s.progress ∧ domSet s.progress = c.ids)
    (Hd' : domSet s'.prvals = domSet s'.progress ∧ domSet s'.progress = c.ids) :
    RnScope md id rs' s' := by
  have Hs0 := Hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := Hs
  obtain ⟨hmo, hcf, hsl⟩ := hm
  refine ⟨fun a b => by rw [hcf]; exact h1 a (by rw [← hmo]; exact b), fun a => hpv.trans (h2 a),
    fun a => hcq.trans (h3 a), fun a => ?_, fun a => ?_, fun a => (hxs a).trans (h6 a),
    fun a b hr => ?_, fun a hr => ?_, fun a b hnf => ?_⟩
  · obtain ⟨hp1, hp2⟩ := h4 a
    obtain ⟨e1, e2⟩ := hrd a
    exact ⟨e1.trans hp1, (roEmpty_iff s').2 (e2 ((roEmpty_iff s).1 hp2))⟩
  · obtain ⟨q1, q2, q3, q4⟩ := h5 a
    obtain ⟨e1, e2, e3⟩ := hsn a
    exact ⟨hsl.trans q1, e1.trans q2, e2.trans q3, e3⟩
  · rw [hcf, hc]
    rcases hpre hr with ⟨hr0, -, hv | hv⟩ | ⟨-, hv⟩
    · rw [hv, ← hc]; exact h7 a b hr0
    · exact hv
    · exact hv
  · rcases hpre hr with ⟨hr0, hl0, -⟩ | ⟨hl0, -⟩
    · rw [hl0]; exact h8 a hr0
    · exact hl0
  · rw [Hd'.1, Hd'.2]
    exact GMap.elem_of_union_l c.learners
      (by rw [HC.voters]; exact id_mem_of_roleFn a Hs0 Hc HC hl hfol Hd hnf)

/-- `RnScope.stepG` at a network step's role facts (`RoleFn`). -/
theorem RnScope.step {md : RnMode} {γ : RaftNames} {id : w64} {rs rs' : RNState} {s s' : NState}
    {c : CfgM} (hcc : md.confChanges = false) (Hs : RnScope md id rs s) (Hc : RnCfgIn md γ id rs)
    (HC : CfgScope γ c) (hl : c.learners = ∅) (hc : rs.cfg.cfg = c)
    (hm : rs'.mode = rs.mode ∧ rs'.cfg = rs.cfg ∧ rs'.slent = rs.slent)
    (hpv : s'.prevote = s.prevote) (hcq : s'.cq = s.cq)
    (hrd : md.reads = false → s'.rd.pend = s.rd.pend ∧
      ((toPState s).rd.ro.pending = [] → (toPState s').rd.ro.pending = []))
    (hsn : md.snapshots = false → s'.logst.prev = s.logst.prev ∧ s'.logst.snap = s.logst.snap ∧
      NoSnapL s'.outbox)
    (hxs : md.transfer = false → s'.gh.xs = s.gh.xs)
    (hrole : RoleFn c id s s')
    (Hd : domSet s.prvals = domSet s.progress ∧ domSet s.progress = c.ids)
    (Hd' : domSet s'.prvals = domSet s'.progress ∧ domSet s'.progress = c.ids) :
    RnScope md id rs' s' :=
  RnScope.stepG hcc Hs Hc HC hl hc hm hpv hcq hrd hsn hxs (fun hr => .inl (hrole.1 hr)) hrole.2 Hd Hd'

/-- (step C2) **An empty tally is no quorum** of a configuration with a voter in its incoming half. -/
theorem not_jquorum_granted_empty {c : CfgM} {i : w64} (hin : i ∈ c.incoming) :
    ¬ JQuorum c (granted ∅) := by
  rintro ⟨h1, -⟩
  rw [granted_empty] at h1
  rcases h1 with h1 | h1
  · rw [h1] at hin; exact GMap.not_elem_of_empty i hin
  · unfold IsQuorum at h1
    have hs : (∅ : GSet w64) ∩ c.incoming ⊆ ∅ := by
      rw [GMap.elem_of_subseteq]; set_solver
    have := GMap.subseteq_size hs
    rw [GMap.size_empty] at this
    omega

/-- A tick's protocol leader: kept or cleared. -/
theorem tickEnd_lead {c : CfgM} {id : w64} {s s' : PState} (h : TickEnd k c id s s') :
    s'.lead = s.lead ∨ s'.lead = W64 0 := by
  rcases h with rfl | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, -, -, peers, -, rfl⟩ | ⟨-, ms, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl
  · exact .inr rfl
  · exact .inl rfl
  · exact .inr rfl

end scope

section ghostK
open Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (step C1) **A known leader's term is past `0`** (`ownStepGhost_lead`, `isLeader_term_nz`; a
pre-candidate reads as knowing none). -/
theorem ownStepGhost_leadNz (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ md c id s ⊢
      ⌜(toPState s).lead ≠ W64 0 → s.term ≠ W64 0⌝ ∗ ownStepGhost γ md c id s := by
  by_cases hr : s.role = .preCandidate
  · iintro H; iframe H; ipureintro
    show (if s.role = .preCandidate then W64 0 else s.lead) ≠ W64 0 → _
    rw [if_pos hr]; intro h; exact absurd rfl h
  · iintro H
    icases ownStepGhost_lead γ md c id s hr $$ H with ⟨#Hl, H⟩
    rw [toPState_lead_nonpre s hr]
    by_cases hl : s.lead = W64 0
    · iframe H; ipureintro; intro h; exact absurd hl h
    · ihave Hi := Hl $$ %hl
      ihave %Hnz := isLeader_term_nz γ s.lead s.term $$ Hi
      iframe H; ipureintro; intro _; exact Hnz

end ghostK

end EtcdGrove
end Perennial
