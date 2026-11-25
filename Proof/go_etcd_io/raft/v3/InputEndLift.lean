/-
Lean-first (#33 S3c step 2, `notes/antithesis-rawnode-design.md` §2.2). **`StepEnd` lifted to the
per-input end relations** (`Protocol/InputEnd.lean`): raft's exact per-path end state of `Step`
over `NState` (`StepEnd`, `LemmasStepGates.lean`, from the step functions' results
`FollowerStepResultC`, `CandidateStepResultC`, `LeaderStepResultC`, `HupOkC` and `VoteEnd`), read
through `toPState`, is `RecvEnd`/`TickEnd`/`ProposeEnd` at the message's abstraction (`absMsg`).

One lemma per input of the harness's scope: a stale protocol message, `MsgHeartbeat`, `MsgApp`,
`MsgHeartbeatResp`, `MsgAppResp`, `MsgVote`, `MsgVoteResp`, a local or forwarded `MsgProp` (term
`0`), a tick's `MsgHup` and `MsgBeat`. Their premises: the untraced scope at the step's state
(`LiftScope`: pre-vote and check-quorum off, no pre-candidate, `FollowerVotesOk`, no read-index
request pending, the progress map's halves agreeing with the node in it), a protocol message's
term nonzero (a local one's zero), a `MsgHeartbeatResp` with no read-index context, and, where the
step may broadcast, that it queued no `MsgSnap` (`NoSnapSent`, the design's §2.5, which the RawNode
layer discharges). The configuration is any: the relations name its quorums (`JQuorum`, `JLost`),
so nothing here needs it static or non-joint.

The small `toPState` facts of `raft__Step/repl_lemmas.lean` and `raft__Step/MsgProp.lean`
(`adopt_follower`, `adopt_candidate`, `toPState_proposed`) are restated here (`ie_` prefix): a
module outside `raft__Step/` may not import those.
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasStepGates
public import Proof.go_etcd_io.raft.v3.StepLemmas
public import Proof.go_etcd_io.raft.v3.Protocol.InputEnd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section lift
variable {k : NodeK}
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The message-type constants unfolded, the `if`s on them decided. -/
local syntax "ie_tysimp " term " at " ident : tactic
macro_rules
  | `(tactic| ie_tysimp $e:term at $h:ident) =>
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

/-- A goal about message-type constants, closed by unfolding and deciding them. -/
local syntax "ie_tyclose " term : tactic
macro_rules
  | `(tactic| ie_tyclose $e:term) =>
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
      ↓reduceIte, _root_.true_and, _root_.false_and, _root_.and_true, _root_.and_false, _root_.true_or, _root_.false_or, _root_.or_true,
      _root_.or_false, _root_.not_true_eq_false, _root_.not_false_eq_true, ne_eq, _root_.iff_self, _root_.and_self, _root_.not_and,
      Perennial.EtcdGrove.fromLeader, Bool.false_eq_true, ite_true, ite_false])

/-! ### The scope -/

/-- (#33 S3c step 2) **The untraced scope of the lifting lemmas**, at the state a step starts in:
pre-vote and check-quorum off (`Config.PreVote`, `Config.CheckQuorum`), so no pre-candidate; the
protocol's invariant that a follower's tally is empty (`FollowerVotesOk`, which `ownRaftGhost`
carries); no read-index request pending (the harness sends none); and the progress map's two
halves agreeing, with the node in it (`ownTrackerC`'s facts, what makes `reset`'s `Match` values
`LeaderMatchOk` and an unknown sender of a `MsgAppResp` one with no `Match`); (#33 S4,
destinations) the progress map's ids the configuration's (`ownTrackerC`'s), so that a leader's sends,
to peers of the progress map (`ReplSends`, `bcastHeartbeat`), are to peers of `c` (`AppSendOk`,
`TickEnd`). -/
def LiftScope (c : CfgM) (id : w64) (s : NState) : Prop :=
  s.prevote = false ∧ s.cq = false ∧ s.role ≠ .preCandidate ∧ FollowerVotesOk (toPState s) ∧
  s.rd.pend = [] ∧ domSet s.prvals = domSet s.progress ∧ id ∈ domSet s.prvals ∧
  domSet s.progress = c.ids

/-- What the step function's state (after the preamble) has of `LiftScope`: the role facts; the
rest only for a non-follower, which is the state the step started in. -/
def FnScope (c : CfgM) (id : w64) (t : NState) : Prop :=
  t.role ≠ .preCandidate ∧ (t.role = .follower → t.votes = ∅) ∧
  (t.role ≠ .follower →
    t.rd.pend = [] ∧ domSet t.prvals = domSet t.progress ∧ id ∈ domSet t.prvals ∧
    domSet t.progress = c.ids)

theorem LiftScope.fn {c : CfgM} {id : w64} {s : NState} (h : LiftScope c id s) : FnScope c id s :=
  ⟨h.2.2.1, fun hr => followerVotesOk_phys s h.2.2.2.1 hr, fun _ => h.2.2.2.2⟩

/-- A send to a peer of a progress map of the configuration's ids is to a peer of the
configuration. -/
theorem ie_dst_ids {c : CfgM} {t X : NState} (hX : X.progress = t.progress)
    (hpc : domSet t.progress = c.ids) {y : Msg} (hy : y.dst ∈ domSet X.progress) : y.dst ∈ c.ids := by
  rw [hX, hpc] at hy; exact hy

/-! ### The protocol readings of the step's pieces -/

theorem ie_toPState_preState (s : NState) (m : MessageM) (pvs : GMap w64 Progress) :
    toPState (preState s m pvs) =
      if PreBF m s then pbecomeFollower (toPState s) m.Term' (preLead m) else toPState s := by
  unfold preState
  split
  · rw [toPState_prvals_nl _ _ (by simp [becomeFollower]), toPState_becomeFollower]
  · rfl

theorem ie_preState_nobf {s : NState} {m : MessageM} (h : ¬ PreBF m s) (pvs : GMap w64 Progress) :
    preState s m pvs = s := by
  simp [preState, h]

theorem ie_preState_outbox (s : NState) (m : MessageM) (pvs : GMap w64 Progress) :
    (toPState (preState s m pvs)).outbox = (toPState s).outbox := by
  rw [ie_toPState_preState]; split <;> rfl

theorem FnScope.of_preState {c : CfgM} {id : w64} {s : NState} {m : MessageM} (h : LiftScope c id s)
    (pvs : GMap w64 Progress) : FnScope c id (preState s m pvs) := by
  by_cases hb : PreBF m s
  · simp only [preState, hb, ↓reduceIte]
    refine ⟨by simp [becomeFollower], fun _ => rfl, fun hr => absurd rfl hr⟩
  · rw [ie_preState_nobf hb]; exact h.fn

/-- `stepFollower`'s `r.lead = m.From` (`raft__Step/repl_lemmas.lean`'s `adopt_follower`, which a
module outside `raft__Step/` may not import). -/
theorem ie_adopt_follower (s : NState) (src : w64) (Hr : s.role = .follower) (Hv : s.votes = ∅) :
    toPState { s with lead := src } = padoptLeader (toPState s) src := by
  simp [toPState, padoptLeader, Hr, Hv, proleRole]

/-- `stepCandidate`'s `becomeFollower(r.Term, m.From)` (`repl_lemmas.lean`'s `adopt_candidate`). -/
theorem ie_adopt_candidate (s : NState) (src : w64) (pvs : GMap w64 Progress)
    (Hnl : s.role ≠ .leader) :
    toPState { becomeFollower s s.term src with prvals := pvs } = padoptLeader (toPState s) src := by
  simp [toPState, padoptLeader, becomeFollower, resetTo, resetTo0, proleRole, rdNL, Hnl]

theorem ie_toPState_heartbeatResult (id : w64) (t : NState) (ps : PState) (m : MessageM)
    (ctx : List w8) (h : toPState t = padoptLeader ps m.From') :
    toPState (heartbeatResult id t m ctx) =
      psendMsgs { padoptLeader ps m.From' with commit := plogCommitTo ps.commit m.Commit' }
        [{ Msg.plain .heartbeatResp id m.From' ps.term false with ctx := ctx }] := by
  have Htm : t.term = ps.term := congrArg PState.term h
  unfold heartbeatResult
  rw [toPState_sendMsgs]
  have Hs : toPState { t with logst := { t.logst with
        committed := plogCommitTo t.logst.committed m.Commit' } } =
      { toPState t with commit := plogCommitTo (toPState t).commit m.Commit' } := rfl
  rw [Hs, h, Htm]
  rfl

/-- `HandleAppResult` at a state whose protocol reading is `ps` is `AppEnd` there. -/
theorem ie_appEnd_of_handle (id : w64) (t : NState) (ps : PState) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (s' : NState) (ht : toPState t = ps)
    (hres : HandleAppResult id t m ents s') :
    AppEnd id ps (absMsg .app m ents ctx) (toPState s') := by
  have Htm : t.term = ps.term := congrArg PState.term ht
  have Hb : t.logst.prev = ps.base := congrArg PState.base ht
  have Hl : t.logst.sents ++ t.logst.uents = ps.log := congrArg PState.log ht
  have Hc : t.logst.committed = ps.commit := congrArg PState.commit ht
  unfold HandleAppResult at hres
  simp only [Hb, Hl] at hres
  rw [Hc] at hres
  rcases hres with ⟨Hlt, rfl⟩ | ⟨Hle, lastnewi, es', ls', Happ, Hprev', Hes, -, Hcm', -, -, rfl⟩ |
      ⟨Hle, Hnm, hint, hintterm, Hrh, Hht, rfl⟩
  · left; refine ⟨Hlt, ?_⟩
    rw [toPState_sendMsgs, ht]; simp only [appResp, Htm]; rfl
  · right; left; refine ⟨Hle, lastnewi, es', Happ, ?_⟩
    rw [toPState_sendMsgs]
    have Hs : toPState { t with logst := ls' } =
        { toPState t with base := ls'.prev, log := ls'.sents ++ ls'.uents,
                          commit := ls'.committed } := rfl
    rw [Hs, ht, Hprev', Hes, Hcm']
    simp only [appResp, Htm]
    rfl
  · right; right; refine ⟨Hle, Hnm, hint, hintterm, Hrh, Hht, ?_⟩
    rw [toPState_sendMsgs, ht]; simp only [appResp, Htm]; rfl

/-! ### The type switch, by type, at the step function's state `t` -/

theorem ie_handle_heartbeat {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgHeartbeat)
    (H : StepFnEnd c id t m ents ctx s') :
    HandleEnd k c id (toPState t) (absMsg .heartbeat m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
    exact ie_toPState_heartbeatResult id _ _ m ctx (ie_adopt_follower t _ hr (hsc.2.1 hr))
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, pvs, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
    exact ie_toPState_heartbeatResult id _ _ m ctx
      (ie_adopt_candidate t _ pvs (by rw [hr]; decide))
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    rw [if_pos (by rw [toPState_role, hr]; rfl)]

theorem ie_handle_app {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgApp)
    (H : StepFnEnd c id t m ents ctx s') :
    HandleEnd k c id (toPState t) (absMsg .app m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
    exact ie_appEnd_of_handle id _ _ m ents ctx _ (ie_adopt_follower t _ hr (hsc.2.1 hr)) hres
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, pvs, hres⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
    exact ie_appEnd_of_handle id _ _ m ents ctx _
      (ie_adopt_candidate t _ pvs (by rw [hr]; decide)) hres
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    rw [if_pos (by rw [toPState_role, hr]; rfl)]

theorem ie_toPState_leader_send (t : NState) (hr : t.role = .leader) (ms : List Msg)
    (pvs : GMap w64 Progress) (n : w64) :
    toPState { sendMsgs { t with logst := { t.logst with committed := n } } ms with prvals := pvs } =
      psendMsgs { toPState t with matched := prvalsMatch pvs, commit := n } ms := by
  simp only [toPState, sendMsgs, psendMsgs, hr, ↓reduceIte]

theorem ie_toPState_send_prvals (t : NState) (ms : List Msg) (pvs : GMap w64 Progress)
    (hpm : t.role = .leader → prvalsMatch pvs = prvalsMatch t.prvals) :
    toPState { sendMsgs t ms with prvals := pvs } = psendMsgs (toPState t) ms := by
  rw [toPState_prvals (sendMsgs t ms) pvs hpm, toPState_sendMsgs]

theorem ie_toPState_prvals_leader (t : NState) (hr : t.role = .leader) (pvs : GMap w64 Progress) :
    toPState { t with prvals := pvs } = { toPState t with matched := prvalsMatch pvs } := by
  simp only [toPState, hr, ↓reduceIte]

theorem ie_matched_leader (t : NState) (hr : t.role = .leader) :
    (toPState t).matched = prvalsMatch t.prvals := by
  simp only [toPState, hr, ↓reduceIte]

theorem ie_matched_none (t : NState) (hr : t.role = .leader) (src : w64)
    (hd : domSet t.prvals = domSet t.progress) (h : src ∉ domSet t.progress) :
    (toPState t).matched !! src = none := by
  rw [← hd] at h
  have h' : t.prvals !! src = none := by
    simpa [domSet, GMap.mem_iff] using h
  rw [ie_matched_leader t hr]
  simp [prvalsMatch, h']

theorem ie_matched_some (t : NState) (hr : t.role = .leader) (src : w64)
    (hd : domSet t.prvals = domSet t.progress) (h : src ∈ domSet t.progress) :
    (toPState t).matched !! src ≠ none := by
  rw [← hd] at h
  have h' : (t.prvals !! src).isSome := by
    simpa [domSet, GMap.mem_iff] using h
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h'
  rw [ie_matched_leader t hr]
  simp [prvalsMatch, hp]

theorem ie_sendMsgs_nil (s : NState) : sendMsgs s [] = s := by
  simp [sendMsgs]

theorem ie_releasedState_nil (id : w64) (s : NState) (h : s.rd.pend = []) :
    releasedState id s = s := by
  unfold releasedState
  rw [h]
  cases s with
  | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ rd =>
    cases rd
    simp only at h ⊢
    rw [h]
    rfl

theorem ie_rd_pend_nil (s : NState) (h : s.rd.pend = []) :
    ({ s with rd := { s.rd with pend := [] } } : NState) = s := by
  cases s with
  | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ rd =>
    cases rd
    simp only at h ⊢
    rw [h]

theorem ie_handle_appResp {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgAppResp)
    (hns : NoSnapSent (toPState t) (toPState s')) (H : StepFnEnd c id t m ents ctx s') :
    HandleEnd k c id (toPState t) (absMsg .appResp m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨hpend, hdom, -, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, hres⟩ := hres
    rw [if_pos (by rw [toPState_role, hr]; rfl)]
    rcases hres with ⟨hnin, hs⟩ | ⟨hin, hrej, ms, pvs, rfl, hrs, hpm⟩ | ⟨hin, hacc, hA⟩
    · exact Or.inl ⟨ie_matched_none t hr _ hdom hnin, by rw [hs]⟩
    · have he := ie_toPState_send_prvals t ms pvs (fun _ => hpm)
      refine Or.inr (Or.inl ⟨hrej, ie_matched_some t hr _ hdom hin, ms, fun y hy => ?_, he⟩)
      have hn := hns ms ((congrArg PState.outbox he).trans rfl) y hy
      exact ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
    · obtain ⟨x, pvs, n, hb, ms, hx, hpm, hn, -, -, hrs, hif⟩ := hA
      have he : toPState s' =
          psendMsgs { toPState t with matched := prvalsMatch pvs, commit := n } ms := by
        by_cases hnc : n = t.logst.committed
        · rw [if_pos hnc] at hif
          obtain ⟨-, rfl⟩ := hif; exact ie_toPState_leader_send t hr ms pvs n
        · rw [if_neg hnc] at hif
          rcases hif with ⟨-, hrel, rfl⟩ | ⟨-, -, rfl⟩
          · have hb0 : hb = [] := by
              cases hb with
              | nil => rfl
              | cons y _ =>
                obtain ⟨-, k, hk1, hk2, -⟩ := hrel y List.mem_cons_self
                simp only [hpend, List.length_nil] at hk2
                omega
            subst hb0
            have hT : sendMsgs (sendMsgs (releasedState id
                { t with logst := { t.logst with committed := n } }) []) ms =
                sendMsgs { t with logst := { t.logst with committed := n } } ms := by
              rw [ie_sendMsgs_nil, ie_releasedState_nil id { t with logst := { t.logst with committed := n } } hpend]
            refine (congrArg (fun x => toPState { x with prvals := pvs }) hT).trans ?_
            exact ie_toPState_leader_send t hr ms pvs n
          · have hp : pendReqs { t with logst := { t.logst with committed := n } } = [] := by
              simp [pendReqs, hpend]
            have hT : sendMsgs (readRespondAll id
                { t with logst := { t.logst with committed := n }, rd := { t.rd with pend := [] } }
                (pendReqs { t with logst := { t.logst with committed := n } })) ms =
                sendMsgs { t with logst := { t.logst with committed := n } } ms := by
              rw [hp]
              have h2 := ie_rd_pend_nil { t with logst := { t.logst with committed := n } } hpend
              exact congrArg (fun x => sendMsgs x ms) h2
            refine (congrArg (fun x => toPState { x with prvals := pvs }) hT).trans ?_
            exact ie_toPState_leader_send t hr ms pvs n
      have hM : prvalsMatch pvs =
          <[m.From' := if uint.Z x < uint.Z m.Index' then m.Index' else x]> (toPState t).matched := by
        rw [hpm, ie_matched_leader t hr]
      have hx' : (toPState t).matched !! m.From' = some x := by
        rw [ie_matched_leader t hr]; exact hx
      refine Or.inr (Or.inr ⟨hacc, x, n, hx', ?_, ms, fun y hy => ?_, by rw [he, hM]⟩)
      · rcases hn with hn | hn
        · exact Or.inl hn
        · right
          rw [ie_toPState_prvals_leader t hr, hM] at hn
          exact hn
      · have hn := hns ms (by rw [he]; rfl) y hy
        have H : AppSendOk c id (toPState { t with logst := { t.logst with committed := n } }) y :=
          ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
        refine AppSendOk.proper ?_ ?_ ?_ ?_ H <;> rfl

theorem ie_handle_heartbeatResp {c : CfgM} {id : w64} {t : NState} {m : MessageM}
    {ents : List EntryM} {ctx : List w8} {s' : NState} (hsc : FnScope c id t)
    (hty : m.Type' = MsgHeartbeatResp) (hctx : ctx = [])
    (hns : NoSnapSent (toPState t) (toPState s')) (H : StepFnEnd c id t m ents ctx s') :
    HandleEnd k c id (toPState t) (absMsg .heartbeatResp m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨-, -, -, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, ms, pvs, hrs, hpm, hres⟩ := hres
    rw [if_pos (by rw [toPState_role, hr]; rfl)]
    rcases hres with ⟨-, rfl⟩ | ⟨hne, -⟩
    · have he := ie_toPState_send_prvals t ms pvs (fun _ => hpm)
      refine ⟨ms, fun y hy => ?_, he⟩
      have hn := hns ms ((congrArg PState.outbox he).trans rfl) y hy
      exact ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
    · exact absurd hctx hne

theorem ie_handle_voteResp {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgVoteResp)
    (hns : NoSnapSent (toPState t) (toPState s')) (H : StepFnEnd c id t m ents ctx s') :
    HandleEnd k c id (toPState t) (absMsg .voteResp m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | candidate =>
    obtain ⟨-, -, hid, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_neg (by rw [hr]; decide)] at hres
    obtain ⟨won, lost, ms, pvs, hwon, hlost, hnl, rfl⟩ := hres
    have hv : (toPState t).votes = t.votes := toPState_votes_nonpre _ (by rw [hr]; decide)
    have hout : (toPState { voteRespResult id t m.From' m.Reject' won lost ms with prvals := pvs }).outbox
        = (toPState t).outbox ++ (if won then [pselfAck id (pwinState id { toPState t with
            votes := recordVote (toPState t).votes m.From' (!m.Reject') } (prvalsMatch pvs))] ++ ms
            else []) := by
      rw [toPState_voteRespResult _ _ _ _ _ _ _ _ hr]
      cases won <;> cases lost <;> simp [pvoteRespResult, psendMsgs, pwinState, pappend,
        pbecomeLeader, pbecomeFollower]
    rw [if_pos (by rw [toPState_role, hr]; rfl), toPState_voteRespResult _ _ _ _ _ _ _ _ hr]
    rw [← hv] at hlost hnl
    cases won
    · cases lost
      · refine Or.inl ⟨fun hj => absurd (hnl rfl hj) (by decide), ?_⟩
        simp only [pvoteRespResult, Bool.false_eq_true, ↓reduceIte]
      · refine Or.inr (Or.inr ⟨hlost rfl, ?_⟩)
        simp only [pvoteRespResult, Bool.false_eq_true, ↓reduceIte]
    · obtain ⟨hq, hms, hmt⟩ := hwon rfl
      rw [← hv] at hq
      refine Or.inr (Or.inl ⟨hq, prvalsMatch pvs, ms, ?_, fun y hy => ?_, ?_⟩)
      · rw [hmt]
        exact resetMatched_leader_ok id t hid _ rfl rfl
      · have hn := hns _ hout y (List.mem_append_right _ hy)
        have hbl := toPState_becomeLeader id { t with votes := recordVote t.votes m.From' (!m.Reject') }
          (becomeLeader id { t with votes := recordVote t.votes m.From' (!m.Reject') }).prvals
        have H : AppSendOk c id (toPState (becomeLeader id
            { t with votes := recordVote t.votes m.From' (!m.Reject') })) y :=
          ⟨(hms y hy).1.app hn, (hms y hy).2.1, ie_dst_ids rfl hpc (hms y hy).2.2.1⟩
        refine AppSendOk.proper ?_ ?_ ?_ ?_ H
        · rfl
        · rfl
        · exact ((congrArg PState.log hbl).trans rfl).symm
        · rfl
      · simp only [pvoteRespResult, ↓reduceIte]
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]

theorem ie_handle_vote (c : CfgM) {id : w64} {t : NState} {m : MessageM} (ents : List EntryM)
    (ctx : List w8) {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgVote)
    (H : VoteEnd id t m s') :
    HandleEnd k c id (toPState t) (absMsg .vote m ents ctx) (toPState s') := by
  have hlead : (toPState t).lead = t.lead := toPState_lead_nonpre _ hsc.1
  have hpv : ¬ m.Type' = MsgPreVote := by rw [hty]; ie_tyclose MsgVote
  have hg : VoteGrant t m ↔ (PCanVote (toPState t) m.From' ∧
      plogUpToDate (toPState t).base (toPState t).log (entryID.mk m.LogTerm' m.Index') = true) := by
    unfold VoteGrant PCanVote
    rw [hlead]
    simp only [hpv, _root_.false_and, _root_.or_false]
    rfl
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  rcases H with ⟨hgr, rfl⟩ | ⟨hgr, rfl⟩
  · refine Or.inl ⟨(hg.1 hgr).1, (hg.1 hgr).2, ?_⟩
    simp only [vrespMsgOf, hty, ↓reduceIte, Bool.false_eq_true]
    rfl
  · refine Or.inr ⟨fun h => hgr (hg.2 h), ?_⟩
    simp only [vrespMsgOf, hty, ↓reduceIte]
    rfl

/-- `stepLeader`'s accepted proposal (`raft__Step/MsgProp.lean`'s `toPState_proposed`, which a
module outside `raft__Step/` may not import; as `TracedRaftStepProp.lean`'s copy). -/
theorem ie_toPState_proposed (id : w64) (s : NState) (ents : List EntryM) :
    toPState (proposed id s ents) =
    psendMsgs
      (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))
      [pselfAck id
         (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))] := by
  have Hli : ∀ s : NState, plastIndex (toPState s) = logLast s.logst := by
    intro s
    simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
    congr 1; push_cast; omega
  simp only [proposed, sendMsgs, toPState, psendMsgs, pappend, pselfAck, selfAck, logAppend,
    List.append_assoc]
  rw [← Hli s]
  simp only [toPState]
  congr 3
  simp only [plastIndex, plogLastIndexZ, logLast, List.length_append]
  congr 2; push_cast; simp only [List.length_mapIdx]; omega

theorem ie_handle_prop {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgProp)
    (hns : NoSnapSent (toPState t) (toPState s')) (H : StepFnEnd c id t m ents ctx s') :
    ProposeEnd c id (toPState t) (absMsg .propose m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  have hlead : (toPState t).lead = t.lead := toPState_lead_nonpre _ hsc.1
  unfold ProposeEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, hres⟩ := hres
    have hpr : (toPState t).role = .follower := by rw [toPState_role, hr]; rfl
    rw [if_neg (by rw [hpr]; decide)]
    by_cases hl0 : t.lead = W64 0
    · rw [if_pos (show t.lead = 0#64 from hl0)] at hres
      obtain ⟨-, hs⟩ := hres
      rw [if_neg (by rw [hlead]; exact fun h => h.2 hl0), hs]
    · rw [if_neg (show ¬ t.lead = 0#64 from hl0)] at hres
      obtain ⟨-, hs⟩ := hres
      rw [if_pos ⟨hpr, by rw [hlead]; exact hl0⟩, hs, toPState_sendMsgs, hlead]
      rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    have hpr : (toPState t).role = .candidate := by rw [toPState_role, hr]; rfl
    rw [if_neg (by rw [hpr]; decide), if_neg (by rw [hpr]; exact fun h => absurd h.1 (by decide)), hs]
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨-, -, -, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨cs, hcc, -, hres⟩ := hres
    rw [if_pos (by rw [toPState_role, hr]; rfl)]
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte] at hres
      obtain ⟨ms, pvs, rfl, hrs, hpm⟩ := hres
      have he : toPState { sendMsgs (proposed id { t with pci := (leaderPropConf t ents cs c.joint).2 }
            (leaderPropConf t ents cs c.joint).1) ms with prvals := pvs } =
          psendMsgs (pappend (toPState t) ((leaderPropConf t ents cs c.joint).1.mapIdx
              (stamp t.term (plastIndex (toPState t)))))
            ([pselfAck id (pappend (toPState t) ((leaderPropConf t ents cs c.joint).1.mapIdx
              (stamp t.term (plastIndex (toPState t)))))] ++ ms) := by
        refine (ie_toPState_send_prvals (proposed id { t with pci := (leaderPropConf t ents cs c.joint).2 }
          (leaderPropConf t ents cs c.joint).1) ms pvs (fun _ => hpm)).trans ?_
        rw [ie_toPState_proposed]
        simp only [psendMsgs, List.append_assoc]
        rfl
      refine Or.inr ⟨(leaderPropConf t ents cs c.joint).1, ms,
        propConf_repl _ _ _ ents cs hcc, fun y hy => ?_, he⟩
      have hn := hns _ ((congrArg PState.outbox he).trans rfl) y (List.mem_append_right _ hy)
      have H : AppSendOk c id (toPState (proposed id { t with pci := (leaderPropConf t ents cs c.joint).2 }
          (leaderPropConf t ents cs c.joint).1)) y :=
        ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
      have hp := ie_toPState_proposed id { t with pci := (leaderPropConf t ents cs c.joint).2 }
          (leaderPropConf t ents cs c.joint).1
      refine AppSendOk.proper ?_ ?_ ?_ ?_ H
      · rfl
      · rfl
      · exact ((congrArg PState.log hp).trans rfl).symm
      · rfl
    · simp only [↓reduceIte] at hres
      rcases hres with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl rfl

/-! ### `StepEnd`'s arms -/

/-- `Step`'s preamble at the protocol level. -/
theorem ie_preEnd_preState {s : NState} {m : MessageM} {ty : MsgType} {ents : List EntryM}
    {ctx : List w8} (pvs : GMap w64 Progress) (h0 : m.Term' ≠ W64 0) (hst : ¬ StaleMsg s m)
    (hbf : PreBF m s ↔ uint.Z s.term < uint.Z m.Term')
    (hpl : preLead m = if fromLeader ty then m.From' else W64 0) :
    PreEnd k (toPState s) (absMsg ty m ents ctx) (toPState (preState s m pvs)) := by
  rw [ie_toPState_preState]
  by_cases hb : PreBF m s
  · left
    rw [if_pos hb, hpl]
    exact ⟨hbf.1 hb, rfl⟩
  · right
    rw [if_neg hb]
    refine ⟨?_, rfl⟩
    have h1 : ¬ uint.Z s.term < uint.Z m.Term' := fun h => hb (hbf.2 h)
    have h2 : ¬ uint.Z m.Term' < uint.Z s.term := fun h => hst ⟨h0, h⟩
    show m.Term' = s.term
    word

/-- `Step`'s stale arm: ignored, with check-quorum and pre-vote off. -/
theorem ie_recvEnd_stale {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} {ty : MsgType} (hsc : LiftScope c id s) (hT : StepEndTy m.Type')
    (hpv : m.Type' ≠ MsgPreVote) (hst : StaleMsg s m) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') := by
  obtain ⟨hs, -, -, -⟩ := h hT
  have he : s' = s := by
    rcases hs hst with he | ⟨ty', mm, hlow, -⟩
    · exact he
    · exfalso
      rcases hlow with ⟨-, hcq, -⟩ | ⟨-, hp, -⟩
      · rw [hsc.1, hsc.2.1] at hcq; simp at hcq
      · exact hpv hp
  subst he
  exact Or.inr (Or.inl ⟨hst.1, hst.2, rfl⟩)

/-- A message of a nonzero term handled by the role's step function: stale, or the preamble then
the step function's result. -/
theorem ie_recvEnd_fn {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} {ty : MsgType} (hsc : LiftScope c id s) (hT : StepEndTy m.Type')
    (hpv : m.Type' ≠ MsgPreVote) (hh : m.Type' ≠ MsgHup) (hv : m.Type' ≠ MsgVote)
    (h0 : m.Term' ≠ W64 0) (hbf : PreBF m s ↔ uint.Z s.term < uint.Z m.Term')
    (hpl : preLead m = if fromLeader ty then m.From' else W64 0)
    (hH : ∀ t : NState, FnScope c id t → (toPState t).outbox = (toPState s).outbox →
      StepFnEnd c id t m ents ctx s' → HandleEnd k c id (toPState t) (absMsg ty m ents ctx) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') := by
  by_cases hst : StaleMsg s m
  · exact ie_recvEnd_stale hsc hT hpv hst h
  obtain ⟨-, -, -, hfn⟩ := h hT
  obtain ⟨pvs, H⟩ := hfn hst hh hv
  exact Or.inr (Or.inr ⟨h0, _, ie_preEnd_preState pvs h0 hst hbf hpl,
    hH _ (FnScope.of_preState hsc pvs) (ie_preState_outbox s m pvs) H⟩)

/-- A local message (term `0`): no preamble, the step function at `s`. -/
theorem ie_fn_local {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hT : StepEndTy m.Type') (hh : m.Type' ≠ MsgHup) (hv : m.Type' ≠ MsgVote)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') : StepFnEnd c id s m ents ctx s' := by
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  have hbf : ¬ PreBF m s := fun hb => by
    have h1 := hb.1
    rw [h0] at h1
    word
  obtain ⟨-, -, -, hfn⟩ := h hT
  obtain ⟨pvs, H⟩ := hfn hst hh hv
  rwa [ie_preState_nobf hbf] at H

/-! ### The lifting lemmas, by input -/

/-- **A stale message** (any of the harness's protocol messages, `m.Term < r.Term`): ignored. -/
theorem recvEnd_of_stepEnd_stale {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} {ty : MsgType} (hsc : LiftScope c id s)
    (hty : m.Type' = MsgApp ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeat ∨
      m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgVote ∨ m.Type' = MsgVoteResp)
    (hst : StaleMsg s m) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') :=
  ie_recvEnd_stale hsc (by unfold StepEndTy; rcases hty with e | e | e | e | e | e <;> ie_tyclose e)
    (by rcases hty with e | e | e | e | e | e <;> (rw [e]; ie_tyclose MsgPreVote)) hst h

/-- **`MsgHeartbeat`**. -/
theorem recvEnd_of_stepEnd_heartbeat {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgHeartbeat)
    (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .heartbeat m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
    (fun _ hsc' _ H => ie_handle_heartbeat hsc' hty H) h

/-- **`MsgApp`**. -/
theorem recvEnd_of_stepEnd_app {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgApp)
    (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .app m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
    (fun _ hsc' _ H => ie_handle_app hsc' hty H) h

/-- **`MsgHeartbeatResp`**, with no read-index context (`ctx = []`: no read-index request in the
scope, so the leader's heartbeats carry none). -/
theorem recvEnd_of_stepEnd_heartbeatResp {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgHeartbeatResp)
    (h0 : m.Term' ≠ W64 0) (hctx : ctx = []) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .heartbeatResp m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
    (fun _ hsc' ho H => ie_handle_heartbeatResp hsc' hty hctx (hns.of_outbox ho) H) h

/-- **`MsgAppResp`**. -/
theorem recvEnd_of_stepEnd_appResp {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgAppResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .appResp m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
    (fun _ hsc' ho H => ie_handle_appResp hsc' hty (hns.of_outbox ho) H) h

/-- **`MsgVoteResp`**. -/
theorem recvEnd_of_stepEnd_voteResp {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgVoteResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .voteResp m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
    (fun _ hsc' ho H => ie_handle_voteResp hsc' hty (hns.of_outbox ho) H) h

/-- **`MsgVote`**: `Step`'s own arm (no step function), with check-quorum off (no lease). -/
theorem recvEnd_of_stepEnd_vote {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgVote)
    (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .vote m ents ctx) (toPState s') := by
  have hT : StepEndTy m.Type' := by unfold StepEndTy; ie_tyclose hty
  by_cases hst : StaleMsg s m
  · exact ie_recvEnd_stale hsc hT (by rw [hty]; ie_tyclose MsgPreVote) hst h
  obtain ⟨-, -, hv, -⟩ := h hT
  rcases hv hst hty with ⟨hcq, -⟩ | ⟨pvs, H⟩
  · rw [hsc.2.1] at hcq; cases hcq
  · exact Or.inr (Or.inr ⟨h0, _,
      ie_preEnd_preState pvs h0 hst (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty),
      ie_handle_vote c ents ctx (FnScope.of_preState hsc pvs) hty H⟩)

/-- **`MsgProp`** (term `0`: `RawNode.Propose`'s, or a forwarded one), as `ProposeEnd`. -/
theorem proposeEnd_of_stepEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgProp)
    (h0 : m.Term' = W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    ProposeEnd c id (toPState s) (absMsg .propose m ents ctx) (toPState s') :=
  ie_handle_prop hsc.fn hty hns
    (ie_fn_local (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgHup)
      (by rw [hty]; ie_tyclose MsgVote) h0 h)

/-- **`MsgProp`** as a received message (`RecvEnd`'s local arm). -/
theorem recvEnd_of_stepEnd_prop {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgProp)
    (h0 : m.Term' = W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .propose m ents ctx) (toPState s') :=
  Or.inl ⟨h0, proposeEnd_of_stepEnd hsc hty h0 hns h⟩

/-- **A tick's `MsgHup`** (`tickElection`): nothing, or a campaign at the next term (pre-vote
off). -/
theorem tickEnd_of_stepEnd_hup {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgHup)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') :
    TickEnd k c id (toPState s) (toPState s') := by
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  obtain ⟨-, hhup, -, -⟩ := h (by unfold StepEndTy; ie_tyclose hty)
  obtain ⟨-, -, -, -, hg⟩ := hhup hst hty
  rcases hg with ⟨-, rfl⟩ | ⟨⟨hnl, hv, -, -⟩, pre, peers, pvs, cl, hpre, hperm, rfl⟩
  · exact Or.inl rfl
  · cases pre
    · refine Or.inr (Or.inl ⟨by rw [toPState_role]; exact proleRole_not_leader _ hnl, hv, peers,
        cl, hperm, ?_⟩)
      rw [toPState_prvals_nl _ _ (by simp [campaignState, sendMsgs, becomeCandidate])]
      simp only [campaignState, Bool.false_eq_true, ↓reduceIte]
      rw [toPState_sendMsgs, toPState_becomeCandidate]
      rfl
    · exact absurd (hpre rfl) (by rw [hsc.1]; decide)

/-- **A tick's `MsgBeat`** (`tickHeartbeat`): a leader's heartbeats; nothing elsewhere. -/
theorem tickEnd_of_stepEnd_beat {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgBeat)
    (h0 : m.Term' = W64 0) (hro : (toPState s).rd.ro.pending = [])
    (h : StepEnd c id m ents ctx s s') :
    TickEnd k c id (toPState s) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := ie_fn_local (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgHup)
      (by rw [hty]; ie_tyclose MsgVote) h0 h
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    exact Or.inl (by rw [hs])
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    exact Or.inl (by rw [hs])
  | preCandidate => exact absurd hr hsc.2.2.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, ms, pvs, rfl, hok, hpm⟩ := hres
    have hpc : domSet s.progress = c.ids := hsc.2.2.2.2.2.2.2
    -- (#33 S4, msgShape) the read-only queue empty: the heartbeats carry no context (`hbCtx`)
    have hpend : s.rd.ro.pending = [] := by
      have h' := hro; unfold toPState at h'; simp only [hr, ite_true] at h'; exact h'
    exact Or.inr (Or.inr ⟨by rw [toPState_role, hr]; rfl, ms,
      fun y hy => ⟨(hok y hy).1, (hok y hy).2.2.1, (hok y hy).2.2.2.1, (hok y hy).2.2.2.2.1,
        by rw [(hok y hy).2.1]; unfold hbCtx; rw [hpend, hro]; simp, ie_dst_ids rfl hpc (hok y hy).2.2.2.2.2⟩,
      ie_toPState_send_prvals s ms pvs (fun _ => hpm)⟩)

/-- (#33 S4) **A tick's `MsgHup` keeps the log's state** (`HupOkC`: a campaign touches no log
field), `offsetInProgress` with it. -/
theorem logst_of_stepEnd_hup {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hty : m.Type' = MsgHup) (h0 : m.Term' = W64 0)
    (h : StepEnd c id m ents ctx s s') : s'.logst = s.logst := by
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  obtain ⟨-, hhup, -, -⟩ := h (by unfold StepEndTy; ie_tyclose hty)
  exact (hhup hst hty).2.2.1.1

/-- (#33 S4) **A tick's `MsgBeat` keeps the log's state**: a leader's heartbeats queue messages
only; elsewhere nothing. -/
theorem logst_of_stepEnd_beat {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgBeat)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') : s'.logst = s.logst := by
  obtain ⟨hf, hc, hl⟩ := ie_fn_local (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgHup)
      (by rw [hty]; ie_tyclose MsgVote) h0 h
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    rw [hs]
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    rw [hs]
  | preCandidate => exact absurd hr hsc.2.2.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, ms, pvs, rfl, -, -⟩ := hres
    rfl

end lift

end EtcdGrove
end Perennial
