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

/-- What the step function's state (after the preamble) has of `LiftScope`: the role facts (a
pre-candidate knows no leader, `becomePreCandidate`'s `r.lead = None`); the rest only for a
non-follower, which is the state the step started in. (antithesis parity B1, step B) No read-index
fact: a leader's release of its deferred requests is `AppRespEnd`'s `ReleaseEnd` arm. -/
def FnScope (c : CfgM) (id : w64) (t : NState) : Prop :=
  (t.role = .preCandidate → t.lead = W64 0) ∧ (t.role = .follower → t.votes = ∅) ∧
  (t.role ≠ .follower →
    domSet t.prvals = domSet t.progress ∧ id ∈ domSet t.prvals ∧ domSet t.progress = c.ids)

theorem LiftScope.fn {c : CfgM} {id : w64} {s : NState} (h : LiftScope c id s) : FnScope c id s :=
  ⟨fun hr => absurd hr h.2.2.1, fun hr => followerVotesOk_phys s h.2.2.2.1 hr, fun _ => h.2.2.2.2.2⟩

/-- (antithesis parity B1, phase 2, step B) **`LiftScope` at the node's flags `k`**: check-quorum and
pre-vote the raft state's (`KTie`), a pre-candidate with no leader, the node in its own progress map
past the follower role (`RnScope`'s facts at a mode with pre-vote and non-voters, the lead's decisions
1 and 2), the progress map's facts as `LiftScope`'s. No read-index fact (`FnScope` has none). -/
def LiftScopeK (k : NodeK) (c : CfgM) (id : w64) (s : NState) : Prop :=
  k.cq = s.cq ∧ k.prevote = s.prevote ∧ (s.role = .preCandidate → s.lead = W64 0) ∧
  FollowerVotesOk (toPState s) ∧ domSet s.prvals = domSet s.progress ∧
  (s.role ≠ .follower → id ∈ domSet s.prvals) ∧ domSet s.progress = c.ids

theorem LiftScopeK.fn {k : NodeK} {c : CfgM} {id : w64} {s : NState} (h : LiftScopeK k c id s) :
    FnScope c id s :=
  ⟨h.2.2.1, fun hr => followerVotesOk_phys s h.2.2.2.1 hr,
    fun hr => ⟨h.2.2.2.2.1, h.2.2.2.2.2.1 hr, h.2.2.2.2.2.2⟩⟩

/-- The basic scope's `LiftScope` at the flags off. -/
theorem LiftScope.toK {k : NodeK} {c : CfgM} {id : w64} {s : NState} (h : LiftScope c id s)
    (hk : k.cq = false ∧ k.prevote = false) : LiftScopeK k c id s :=
  ⟨hk.1.trans h.2.1.symm, hk.2.trans h.1.symm, fun hr => absurd hr h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.2.1, fun _ => h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

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
    refine ⟨fun hr => absurd hr (by simp [becomeFollower]), fun _ => rfl, fun hr => absurd rfl hr⟩
  · rw [ie_preState_nobf hb]; exact h.fn

theorem FnScope.of_preStateK {k : NodeK} {c : CfgM} {id : w64} {s : NState} {m : MessageM}
    (h : LiftScopeK k c id s) (pvs : GMap w64 Progress) :
    FnScope c id (preState s m pvs) := by
  by_cases hb : PreBF m s
  · simp only [preState, hb, ↓reduceIte]
    refine ⟨fun hr => absurd hr (by simp [becomeFollower]), fun _ => rfl, fun hr => absurd rfl hr⟩
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
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, pvs, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
    exact ie_toPState_heartbeatResult id _ _ m ctx
      (ie_adopt_candidate t _ pvs (by rw [hr]; decide))
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
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, pvs, hres⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
    exact ie_appEnd_of_handle id _ _ m ents ctx _
      (ie_adopt_candidate t _ pvs (by rw [hr]; decide)) hres
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

/-- `readRespond` at a leader, read (`raft__Step/resp_lemmas.lean`'s `toPState_readRespond`, restated). -/
theorem ie_toPState_readRespond (id : w64) (s : NState) (Hr : s.role = .leader) (q : ReadReq) :
    toPState (readRespond id s q) = preadRespond id (toPState s) q := by
  unfold readRespond preadRespond
  by_cases h : q.src = W64 0 ∨ q.src = id
  · simp only [h, ↓reduceIte]
    cases q.ents with
    | nil => rfl
    | cons e es => simp [addReadState, toPState, Hr]
  · simp only [h, ↓reduceIte]
    simp [toPState, sendMsgs, psendMsgs, Hr]

theorem ie_toPState_readRespondAll (id : w64) (s : NState) (Hr : s.role = .leader)
    (qs : List ReadReq) :
    toPState (readRespondAll id s qs) = preadRespondAll id (toPState s) qs := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
    have e1 : readRespondAll id s (q :: qs) = readRespondAll id (readRespond id s q) qs := rfl
    rw [e1, preadRespondAll_cons, ← ie_toPState_readRespond id s Hr q]
    obtain ⟨o1, r1, h1⟩ := readRespond_eq id s q
    apply ih
    rw [h1]; exact Hr

/-- Answering read requests only appends to the outbox. -/
theorem ie_preadRespondAll_outbox (id : w64) (s : PState) (qs : List ReadReq) :
    ∃ xs : List Msg, (preadRespondAll id s qs).outbox = s.outbox ++ xs := by
  induction qs generalizing s with
  | nil => exact ⟨[], by simp [preadRespondAll]⟩
  | cons q qs ih =>
    rw [preadRespondAll_cons]
    have h1 : ∃ ys, (preadRespond id s q).outbox = s.outbox ++ ys := by
      unfold preadRespond
      split
      · split
        · exact ⟨[], by simp⟩
        · exact ⟨[], by simp⟩
      · exact ⟨_, rfl⟩
    obtain ⟨ys, hys⟩ := h1
    obtain ⟨xs, hxs⟩ := ih (preadRespond id s q)
    exact ⟨ys ++ xs, by rw [hxs, hys, List.append_assoc]⟩

/-- Answering read requests only appends to the outbox (`NState`). -/
theorem ie_readRespondAll_outbox (id : w64) (s : NState) (qs : List ReadReq) (o : List Msg)
    (ho : s.outbox = o) : ∃ xs : List Msg, (toPState (readRespondAll id s qs)).outbox = o ++ xs := by
  subst ho
  induction qs generalizing s with
  | nil => exact ⟨[], by simp [readRespondAll, toPState]⟩
  | cons q qs ih =>
    have e1 : readRespondAll id s (q :: qs) = readRespondAll id (readRespond id s q) qs := rfl
    rw [e1]
    have h1 : ∃ ys, (readRespond id s q).outbox = s.outbox ++ ys := by
      unfold readRespond
      split
      · split
        · exact ⟨[], by simp [addReadState]⟩
        · exact ⟨[], by simp⟩
      · exact ⟨_, rfl⟩
    obtain ⟨ys, hys⟩ := h1
    obtain ⟨xs, hxs⟩ := ih (readRespond id s q)
    exact ⟨ys ++ xs, by rw [hxs, hys, List.append_assoc]⟩

theorem ie_mem_filter_gset (P : w64 → Unit → Bool) (X : GSet w64) (x : w64) :
    x ∈ GMap.filter P X ↔ x ∈ X ∧ P x () = true := by
  rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_filter]
  cases h : X !! x with
  | none => simp
  | some u => cases u; simp [Option.filter]

/-- (`raft__Step/resp_lemmas.lean`'s `majIdx_majQ`, restated) One half's quorum index bounds a
quorum of that half from below. -/
theorem ie_majIdx_majQ {s : GSet w64} {f : w64 → w64} {N0 N : w64} (H : MajIdx s f N0)
    (Hle : uint.Z N ≤ uint.Z N0) (Q : GSet w64)
    (HQ : ∀ v, v ∈ s → uint.Z N ≤ uint.Z (f v) → v ∈ Q) : MajQ s Q := by
  by_cases hs : s = ∅
  · exact Or.inl hs
  · right
    obtain ⟨-, Hq, -⟩ := H.2 hs
    unfold IsQuorum at Hq ⊢
    refine Nat.lt_of_lt_of_le Hq (Nat.mul_le_mul_left 2 (GMap.subseteq_size ?_))
    rw [GMap.elem_of_subseteq]
    intro v hv
    rw [GMap.elem_of_intersection] at hv ⊢
    obtain ⟨hv1, hv2⟩ := hv
    rw [ie_mem_filter_gset] at hv1
    refine ⟨HQ v hv2 ?_, hv2⟩
    have := hv1.2
    simp only [decide_eq_true_eq] at this
    omega

/-- (`JCommittedIdx.acked`, restated) `JointConfig.CommittedIndex`'s answer is acknowledged by a
joint quorum. -/
theorem ie_jCommittedIdx_acked {c : CfgM} {f : w64 → w64} {N : w64}
    (H : JCommittedIdx c.incoming c.outgoing f N) : JQuorumAcked c f N := by
  obtain ⟨N0, N1, H0, H1, HN⟩ := H
  have h0 : uint.Z N ≤ uint.Z N0 := by rw [HN]; split <;> omega
  have h1 : uint.Z N ≤ uint.Z N1 := by rw [HN]; split <;> omega
  refine ⟨GMap.filter (fun v _ => decide (uint.Z N ≤ uint.Z (f v))) c.voters,
    ⟨ie_majIdx_majQ H0 h0 _ fun v hv hn => ?_, ie_majIdx_majQ H1 h1 _ fun v hv hn => ?_⟩,
    fun v hv => ?_⟩
  · rw [ie_mem_filter_gset]
    exact ⟨GMap.elem_of_union_l _ hv, by simpa using hn⟩
  · rw [ie_mem_filter_gset]
    exact ⟨GMap.elem_of_union_r _ hv, by simpa using hn⟩
  · rw [ie_mem_filter_gset] at hv
    simpa using hv.2

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
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | leader =>
    obtain ⟨hdom, -, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
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
      have hM : prvalsMatch pvs =
          <[m.From' := if uint.Z x < uint.Z m.Index' then m.Index' else x]> (toPState t).matched := by
        rw [hpm, ie_matched_leader t hr]
      have hx' : (toPState t).matched !! m.From' = some x := by
        rw [ie_matched_leader t hr]; exact hx
      -- the appends, judged at the state with the new commit index
      have hap : ∀ y ∈ ms, y.ty ≠ .snap →
          AppSendOk c id (toPState { t with logst := { t.logst with committed := n } }) y :=
        fun y hy hn => ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
      -- the state the commit leaves, read
      have hS : ({ toPState t with
          matched := <[m.From' := if uint.Z x < uint.Z m.Index' then m.Index' else x]> (toPState t).matched,
          commit := n } : PState) =
          toPState { t with logst := { t.logst with committed := n }, prvals := pvs } := by
        rw [← hM]; simp [toPState, hr]
      have hPrd : (toPState { t with logst := { t.logst with committed := n }, prvals := pvs }).rd = t.rd := by
        simp [toPState, hr]
      by_cases hnc : n = t.logst.committed
      · rw [if_pos hnc] at hif
        obtain ⟨-, rfl⟩ := hif
        have he := ie_toPState_leader_send t hr ms pvs n
        refine Or.inr (Or.inr (Or.inl ⟨hacc, x, n, hx', Or.inl hnc, ms, fun y hy => ?_, by rw [he, hM]⟩))
        exact AppSendOk.proper rfl rfl rfl rfl (hap y hy (hns ms (by rw [he]; rfl) y hy))
      · rw [if_neg hnc] at hif
        have hcm : PCommitOk c ({ toPState t with matched := <[m.From' := if uint.Z x < uint.Z m.Index' then m.Index' else x]> (toPState t).matched } : PState) n := by
          rcases hn with hn | hn
          · exact absurd hn hnc
          · rw [ie_toPState_prvals_leader t hr, hM] at hn; exact hn
        rcases hif with ⟨hns1, hrel, rfl⟩ | ⟨hs1, -, rfl⟩
        · -- (antithesis parity) the release: the deferred requests queued, the heartbeats
          have he : toPState { sendMsgs (sendMsgs (releasedState id
              { t with logst := { t.logst with committed := n } }) hb) ms with prvals := pvs } =
              psendMsgs (psendMsgs { toPState { t with logst := { t.logst with committed := n }, prvals := pvs }
                with rd := { t.rd with pend := [], ro := readonlyRelease t.rd.ro id n t.rd.pend } } hb) ms := by
            simp [toPState, hr, sendMsgs, psendMsgs, releasedState]
          refine Or.inr (Or.inr (Or.inr ⟨hacc, x, n, _, hx', hcm, ?_, ms, fun y hy => ?_, he⟩))
          · rw [hS]; unfold ReleaseEnd; rw [hPrd]
            refine Or.inl ⟨hns1, hb, fun y hy => ?_, rfl⟩
            obtain ⟨hok, ⟨hi, hlt, hen, hd⟩, kk, hk1, hk2, hcx⟩ := hrel y hy
            exact ⟨⟨hok, hi, hlt, hen, ie_dst_ids rfl hpc hd⟩, kk, hk1, hk2, hcx⟩
          · have hn := hns (hb ++ ms) (by rw [he]; simp [psendMsgs, toPState]) y (List.mem_append_right _ hy)
            exact AppSendOk.proper rfl rfl rfl rfl (hap y hy hn)
        · -- (antithesis parity) the release at a single voter: each request answered at once
          have he : toPState { sendMsgs (readRespondAll id
              { t with logst := { t.logst with committed := n }, rd := { t.rd with pend := [] } }
              (pendReqs { t with logst := { t.logst with committed := n } })) ms with prvals := pvs } =
              psendMsgs (preadRespondAll id
                { toPState { t with logst := { t.logst with committed := n }, prvals := pvs }
                  with rd := { t.rd with pend := [] } }
                (t.rd.pend.map (fun p => ⟨n, p.1.From', p.2⟩))) ms := by
            show psendMsgs (toPState { readRespondAll id
              { t with logst := { t.logst with committed := n }, rd := { t.rd with pend := [] } }
              (pendReqs { t with logst := { t.logst with committed := n } }) with prvals := pvs }) ms = _
            rw [← readRespondAll_prvals, ie_toPState_readRespondAll id _ (by simp [hr])]
            congr 2
            simp [toPState, hr]
          obtain ⟨o, r2, ho⟩ := preadRespondAll_eq id
            { toPState { t with logst := { t.logst with committed := n }, prvals := pvs }
                with rd := { t.rd with pend := [] } } (t.rd.pend.map (fun p => ⟨n, p.1.From', p.2⟩))
          obtain ⟨xs, hxs⟩ := ie_preadRespondAll_outbox id
            { toPState { t with logst := { t.logst with committed := n }, prvals := pvs }
                with rd := { t.rd with pend := [] } } (t.rd.pend.map (fun p => ⟨n, p.1.From', p.2⟩))
          refine Or.inr (Or.inr (Or.inr ⟨hacc, x, n, _, hx', hcm, ?_, ms, fun y hy => ?_, he⟩))
          · rw [hS]; unfold ReleaseEnd; rw [hPrd]
            exact Or.inr ⟨hs1, rfl⟩
          · have hn := hns (xs ++ ms) (by rw [he]; simp only [psendMsgs]; rw [hxs]; simp [toPState])
              y (List.mem_append_right _ hy)
            exact AppSendOk.proper (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (hap y hy hn)

theorem ie_handle_heartbeatResp {c : CfgM} {id : w64} {t : NState} {m : MessageM}
    {ents : List EntryM} {ctx : List w8} {s' : NState} (hsc : FnScope c id t)
    (hty : m.Type' = MsgHeartbeatResp)
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
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | leader =>
    obtain ⟨hdom, -, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, ms, pvs, hrs, hpm, hres⟩ := hres
    rw [if_pos (by rw [toPState_role, hr]; rfl)]
    have he := ie_toPState_send_prvals t ms pvs (fun _ => hpm)
    obtain ⟨xs, hxs⟩ : ∃ xs, (toPState s').outbox = (toPState t).outbox ++ ms ++ xs := by
        rcases hres with ⟨-, rfl⟩ | ⟨-, N, -, rfl⟩
        · exact ⟨[], by rw [he]; simp [psendMsgs]⟩
        · exact ie_readRespondAll_outbox id _ _ _ rfl
    have hsend : SendsEnd c id (toPState t) (toPState { sendMsgs t ms with prvals := pvs }) := by
      refine ⟨ms, fun y hy => ?_, he⟩
      have hn := hns (ms ++ xs) (by rw [hxs, List.append_assoc]) y (List.mem_append_left _ hy)
      exact ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
    refine ⟨_, hsend, ?_⟩
    rcases hres with ⟨hc0, rfl⟩ | ⟨hne, N, hN, rfl⟩
    · refine Or.inl ⟨?_, rfl⟩
      rcases hc0 with hc0 | hc0
      · exact .inl hc0
      · exact .inr (ie_matched_none t hr _ hdom hc0)
    · -- (antithesis parity) the read acknowledgement: the requests up to the joint quorum's position
      -- answered
      refine Or.inr ⟨hne, Or.inr ⟨N, ?_, ?_⟩⟩
      · have hro : (toPState { sendMsgs t ms with prvals := pvs }).rd.ro = t.rd.ro := by
          simp [toPState, hr, sendMsgs]
        rw [hro]
        exact ie_jCommittedIdx_acked hN
      · rw [ie_toPState_readRespondAll id _ (by simp [sendMsgs, hr])]
        congr 1 <;> simp [toPState, hr, sendMsgs, Msg.mkV]

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
    obtain ⟨-, hid, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
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
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_pos hr] at hres
    subst hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
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
  have hlead : (toPState t).lead = t.lead := by
    by_cases hp : t.role = .preCandidate
    · rw [hsc.1 hp]; simp [toPState, hp]
    · exact toPState_lead_nonpre _ hp
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
  unfold ProposeEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    have hlead : (toPState t).lead = t.lead := toPState_lead_nonpre _ (by rw [hr]; decide)
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
  | preCandidate =>
    -- a pre-candidate drops it (`stepCandidate`), and reads as a follower with no leader
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    have hpr : (toPState t).role = .follower := by rw [toPState_role, hr]; rfl
    have hl0 : (toPState t).lead = W64 0 := by simp [toPState, hr]
    rw [if_neg (by rw [hpr]; decide), if_neg (by rw [hl0]; exact fun h => h.2 rfl), hs]
  | leader =>
    obtain ⟨-, -, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
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

/-- A type `Step`'s preamble turns into a follower at a higher term (`PreTermKeep`'s complement). -/
theorem ie_not_preTermKeep {ty : MsgType} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    (h1 : ty ≠ .preVote) (h2 : ty ≠ .preVoteResp) : ¬ PreTermKeep (absMsg ty m ents ctx) := by
  rintro (h | ⟨h, -⟩)
  · exact h1 h
  · exact h2 h

/-- `Step`'s preamble at the protocol level. -/
theorem ie_preEnd_preState {s : NState} {m : MessageM} {ty : MsgType} {ents : List EntryM}
    {ctx : List w8} (pvs : GMap w64 Progress) (h0 : m.Term' ≠ W64 0) (hst : ¬ StaleMsg s m)
    (hbf : PreBF m s ↔ uint.Z s.term < uint.Z m.Term')
    (hpl : preLead m = if fromLeader ty then m.From' else W64 0)
    (hpk : ¬ PreTermKeep (absMsg ty m ents ctx)) :
    PreEnd k (toPState s) (absMsg ty m ents ctx) (toPState (preState s m pvs)) := by
  rw [ie_toPState_preState]
  by_cases hb : PreBF m s
  · left
    rw [if_pos hb, hpl]
    exact ⟨hbf.1 hb, hpk, rfl⟩
  · right; left
    rw [if_neg hb]
    refine ⟨?_, rfl⟩
    have h1 : ¬ uint.Z s.term < uint.Z m.Term' := fun h => hb (hbf.2 h)
    have h2 : ¬ uint.Z m.Term' < uint.Z s.term := fun h => hst ⟨h0, h⟩
    show m.Term' = s.term
    word

/-- `Step`'s stale arm: ignored, with check-quorum and pre-vote off. -/
theorem ie_recvEnd_stale {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} {ty : MsgType} (hsc : LiftScope c id s)
    (hpv : m.Type' ≠ MsgPreVote) (hst : StaleMsg s m) (h : StepEndBody c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') := by
  obtain ⟨hs, -, -, -⟩ := h
  have he : s' = s := by
    rcases hs hst with he | ⟨ty', mm, hlow, -⟩
    · exact he
    · exfalso
      rcases hlow with ⟨-, hcq, -⟩ | ⟨-, hp, -⟩
      · rw [hsc.1, hsc.2.1] at hcq; simp at hcq
      · exact hpv hp
  subst he
  exact Or.inr (Or.inl ⟨hst.1, hst.2, Or.inl rfl⟩)

/-- (antithesis parity B1, phase 2) `Step`'s stale arm at any flags `k` the node's (`KTie`): ignored,
or (check-quorum or pre-vote on) a stale `MsgApp`/`MsgHeartbeat` answered by an empty `MsgAppResp`
at the node's term (`StaleEnd`'s second arm). Not for a `MsgPreVote` (`StepEnd.prevote` is about a
current one). -/
theorem ie_recvEnd_staleK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} {ty : MsgType} (hk : k.cq = s.cq ∧ k.prevote = s.prevote)
    (hty : mtypeOf m.Type' = some ty)
    (hpv : m.Type' ≠ MsgPreVote) (hst : StaleMsg s m) (h : StepEndBody c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') := by
  obtain ⟨hs, -, -, -⟩ := h
  refine Or.inr (Or.inl ⟨hst.1, hst.2, ?_⟩)
  rcases hs hst with rfl | ⟨ty', mm, hlow, rfl⟩
  · exact Or.inl rfl
  · rcases hlow with ⟨-, hcq, hha, rfl⟩ | ⟨-, hp, -⟩
    · refine Or.inr (Or.inl ⟨by rw [hk.1, hk.2]; exact hcq, ?_, ?_⟩)
      · rcases hha with e | e <;> rw [e] at hty <;> cases hty
        · exact .inr rfl
        · exact .inl rfl
      · rw [toPState_sendMsgs]; rfl
    · exact absurd hp hpv

/-- A message of a nonzero term handled by the role's step function: stale, or the preamble then
the step function's result. -/
theorem ie_recvEnd_fn {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} {ty : MsgType} (hsc : LiftScope c id s)
    (hpv : m.Type' ≠ MsgPreVote) (hh : m.Type' ≠ MsgHup) (hv : m.Type' ≠ MsgVote)
    (h0 : m.Term' ≠ W64 0) (hbf : PreBF m s ↔ uint.Z s.term < uint.Z m.Term')
    (hpl : preLead m = if fromLeader ty then m.From' else W64 0)
    (hpk : ¬ PreTermKeep (absMsg ty m ents ctx))
    (hH : ∀ t : NState, FnScope c id t → (toPState t).outbox = (toPState s).outbox →
      StepFnEnd c id t m ents ctx s' → HandleEnd k c id (toPState t) (absMsg ty m ents ctx) (toPState s'))
    (h : StepEndBody c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') := by
  by_cases hst : StaleMsg s m
  · exact ie_recvEnd_stale hsc hpv hst h
  obtain ⟨-, -, -, hfn⟩ := h
  obtain ⟨pvs, H⟩ := hfn hst hh hv
  exact Or.inr (Or.inr (Or.inr ⟨h0, _, ie_preEnd_preState pvs h0 hst hbf hpl hpk,
    hH _ (FnScope.of_preState hsc pvs) (ie_preState_outbox s m pvs) H⟩))

/-- A local message (term `0`): no preamble, the step function at `s`. -/
theorem ie_fn_local {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hT : StepEndTy m.Type') (hh : m.Type' ≠ MsgHup) (hv : m.Type' ≠ MsgVote)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') (hnx : ¬ XtRec id m s := by xtrec_tac) :
    StepFnEnd c id s m ents ctx s' := by
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  have hbf : ¬ PreBF m s := fun hb => by
    have h1 := hb.1
    rw [h0] at h1
    word
  obtain ⟨-, -, -, hfn⟩ := h hT (by xtrec_tac)
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
  -- (option (b)) the body at `s` but for `gh.xt` (an append response `Step` records first)
  (h.body_xt (by unfold StepEndTy; rcases hty with e | e | e | e | e | e <;> ie_tyclose e)).elim
    fun Y hb => ie_recvEnd_stale (s := { s with gh := { s.gh with xt := Y } }) hsc
      (by rcases hty with e | e | e | e | e | e <;> (rw [e]; ie_tyclose MsgPreVote)) hst hb

/-- **`MsgHeartbeat`**. -/
theorem recvEnd_of_stepEnd_heartbeat {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgHeartbeat)
    (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .heartbeat m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' _ H => ie_handle_heartbeat hsc' hty H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgApp`**. -/
theorem recvEnd_of_stepEnd_app {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgApp)
    (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .app m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' _ H => ie_handle_app hsc' hty H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgHeartbeatResp`**, with no read-index context (`ctx = []`: no read-index request in the
scope, so the leader's heartbeats carry none). -/
theorem recvEnd_of_stepEnd_heartbeatResp {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgHeartbeatResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .heartbeatResp m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' ho H => ie_handle_heartbeatResp hsc' hty (hns.of_outbox ho) H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgAppResp`**. -/
theorem recvEnd_of_stepEnd_appResp {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgAppResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .appResp m ents ctx) (toPState s') :=
  (h.body_xt (by unfold StepEndTy; ie_tyclose hty)).elim fun Y hb =>
  ie_recvEnd_fn (s := { s with gh := { s.gh with xt := Y } }) hsc (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' ho H => ie_handle_appResp hsc' hty (hns.of_outbox ho) H) hb

/-- **`MsgVoteResp`**. -/
theorem recvEnd_of_stepEnd_voteResp {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgVoteResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .voteResp m ents ctx) (toPState s') :=
  ie_recvEnd_fn hsc (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' ho H => ie_handle_voteResp hsc' hty (hns.of_outbox ho) H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgVote`**: `Step`'s own arm (no step function), with check-quorum off (no lease). -/
theorem recvEnd_of_stepEnd_vote {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgVote)
    (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .vote m ents ctx) (toPState s') := by
  have hT : StepEndTy m.Type' := by unfold StepEndTy; ie_tyclose hty
  by_cases hst : StaleMsg s m
  · exact ie_recvEnd_stale hsc (by rw [hty]; ie_tyclose MsgPreVote) hst (h hT (by xtrec_tac))
  obtain ⟨-, -, hv, -⟩ := h hT (by xtrec_tac)
  rcases hv hst hty with ⟨hcq, -⟩ | ⟨pvs, H⟩
  · rw [hsc.2.1] at hcq; cases hcq
  · exact Or.inr (Or.inr (Or.inr ⟨h0, _,
      ie_preEnd_preState pvs h0 hst (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
        (ie_not_preTermKeep (by decide) (by decide)),
      ie_handle_vote c ents ctx (FnScope.of_preState hsc pvs) hty H⟩))

/-! ### The lifting lemmas at the node's flags (antithesis parity B1, step B)

The six received arms over `LiftScopeK` (check-quorum and pre-vote at the node's flags, a
pre-candidate's arms): stale at any flags
(`ie_recvEnd_staleK`), a `MsgVote` within the lease ignored (`LeaseIgnore`). -/

/-- `ie_recvEnd_fn` over `LiftScopeK`. -/
theorem ie_recvEnd_fnK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} {ty : MsgType} (hsc : LiftScopeK k c id s)
    (hty : mtypeOf m.Type' = some ty)
    (hpv : m.Type' ≠ MsgPreVote) (hh : m.Type' ≠ MsgHup) (hv : m.Type' ≠ MsgVote)
    (h0 : m.Term' ≠ W64 0) (hbf : PreBF m s ↔ uint.Z s.term < uint.Z m.Term')
    (hpl : preLead m = if fromLeader ty then m.From' else W64 0)
    (hpk : ¬ PreTermKeep (absMsg ty m ents ctx))
    (hH : ∀ t : NState, FnScope c id t → (toPState t).outbox = (toPState s).outbox →
      StepFnEnd c id t m ents ctx s' → HandleEnd k c id (toPState t) (absMsg ty m ents ctx) (toPState s'))
    (h : StepEndBody c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') := by
  by_cases hst : StaleMsg s m
  · exact ie_recvEnd_staleK ⟨hsc.1, hsc.2.1⟩ hty hpv hst h
  obtain ⟨-, -, -, hfn⟩ := h
  obtain ⟨pvs, H⟩ := hfn hst hh hv
  exact Or.inr (Or.inr (Or.inr ⟨h0, _, ie_preEnd_preState pvs h0 hst hbf hpl hpk,
    hH _ (FnScope.of_preStateK hsc pvs) (ie_preState_outbox s m pvs) H⟩))

/-- **A stale message** over `LiftScopeK`: ignored, or (check-quorum or pre-vote on) a stale
`MsgApp`/`MsgHeartbeat` answered. -/
theorem recvEnd_of_stepEnd_staleK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} {ty : MsgType} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgApp ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeat ∨
      m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgVote ∨ m.Type' = MsgVoteResp)
    (hmt : mtypeOf m.Type' = some ty) (hst : StaleMsg s m) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') :=
  (h.body_xt (by unfold StepEndTy; rcases hty with e | e | e | e | e | e <;> ie_tyclose e)).elim
    fun Y hb => ie_recvEnd_staleK (s := { s with gh := { s.gh with xt := Y } }) ⟨hsc.1, hsc.2.1⟩ hmt
      (by rcases hty with e | e | e | e | e | e <;> (rw [e]; ie_tyclose MsgPreVote)) hst hb

/-- **`MsgHeartbeat`** over `LiftScopeK`. -/
theorem recvEnd_of_stepEnd_heartbeatK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgHeartbeat) (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .heartbeat m ents ctx) (toPState s') :=
  ie_recvEnd_fnK hsc (by rw [hty]; rfl) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' _ H => ie_handle_heartbeat hsc' hty H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgApp`** over `LiftScopeK`. -/
theorem recvEnd_of_stepEnd_appK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgApp) (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .app m ents ctx) (toPState s') :=
  ie_recvEnd_fnK hsc (by rw [hty]; rfl) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' _ H => ie_handle_app hsc' hty H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgHeartbeatResp`** over `LiftScopeK`, with no read-index context. -/
theorem recvEnd_of_stepEnd_heartbeatRespK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgHeartbeatResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .heartbeatResp m ents ctx) (toPState s') :=
  ie_recvEnd_fnK hsc (by rw [hty]; rfl) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' ho H => ie_handle_heartbeatResp hsc' hty (hns.of_outbox ho) H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgAppResp`** over `LiftScopeK`. -/
theorem recvEnd_of_stepEnd_appRespK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgAppResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .appResp m ents ctx) (toPState s') :=
  (h.body_xt (by unfold StepEndTy; ie_tyclose hty)).elim fun Y hb =>
  ie_recvEnd_fnK (s := { s with gh := { s.gh with xt := Y } }) hsc (by rw [hty]; rfl)
    (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' ho H => ie_handle_appResp hsc' hty (hns.of_outbox ho) H) hb

/-- **`MsgVoteResp`** over `LiftScopeK`. -/
theorem recvEnd_of_stepEnd_voteRespK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgVoteResp)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .voteResp m ents ctx) (toPState s') :=
  ie_recvEnd_fnK hsc (by rw [hty]; rfl) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty) (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' ho H => ie_handle_voteResp hsc' hty (hns.of_outbox ho) H) (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- **`MsgVote`** over `LiftScopeK`: stale at any flags; within the lease (check-quorum on, a leader
known, a higher term, not forced) ignored (`LeaseIgnore`); else `Step`'s own arm. -/
theorem recvEnd_of_stepEnd_voteK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgVote) (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .vote m ents ctx) (toPState s') := by
  have hT : StepEndTy m.Type' := by unfold StepEndTy; ie_tyclose hty
  by_cases hst : StaleMsg s m
  · exact ie_recvEnd_staleK ⟨hsc.1, hsc.2.1⟩ (by rw [hty]; rfl) (by rw [hty]; ie_tyclose MsgPreVote) hst
      (h hT (by xtrec_tac))
  obtain ⟨-, -, hv, -⟩ := h hT (by xtrec_tac)
  rcases hv hst hty with ⟨hcq, hl, hlt, hcx, he⟩ | ⟨pvs, H⟩
  · have hpl : (toPState s).lead ≠ W64 0 := by
      by_cases hr : s.role = .preCandidate
      · exact absurd (hsc.2.2.1 hr) hl
      · rw [toPState_lead_nonpre s hr]; exact hl
    exact Or.inr (Or.inr (Or.inl ⟨h0, ⟨hsc.1.trans hcq, .inl rfl, hlt, hpl, hcx⟩, by rw [he]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h0, _,
      ie_preEnd_preState pvs h0 hst (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
        (ie_not_preTermKeep (by decide) (by decide)),
      ie_handle_vote c ents ctx (FnScope.of_preStateK hsc pvs) hty H⟩))

/-- `Step`'s `MsgPreVote` answer at the protocol level (`PreVoteEnd` → `PreVoteEndP`): the grant reads
the physical `lead`, which a pre-candidate's is `0` too. -/
theorem ie_handle_preVote (c : CfgM) {id : w64} {t : NState} {m : MessageM} (ents : List EntryM)
    (ctx : List w8) {s' : NState} (hpre : t.role = .preCandidate → t.lead = W64 0)
    (hty : m.Type' = MsgPreVote) (H : PreVoteEnd id t m s') :
    HandleEnd k c id (toPState t) (absMsg .preVote m ents ctx) (toPState s') := by
  have hlead : (toPState t).lead = t.lead := by
    by_cases hp : t.role = .preCandidate
    · rw [hpre hp]; simp [toPState, hp]
    · exact toPState_lead_nonpre _ hp
  have hnv : m.Type' ≠ MsgVote := by rw [hty]; ie_tyclose MsgPreVote
  have hg : VoteGrant t m ↔ ((PCanVote (toPState t) m.From' ∨ uint.Z (toPState t).term < uint.Z m.Term') ∧
      plogUpToDate (toPState t).base (toPState t).log (entryID.mk m.LogTerm' m.Index') = true) := by
    unfold VoteGrant PCanVote
    rw [hlead]
    constructor
    · rintro ⟨h1 | h1 | ⟨-, h1⟩, h2⟩
      · exact ⟨.inl (.inl h1), h2⟩
      · exact ⟨.inl (.inr h1), h2⟩
      · exact ⟨.inr h1, h2⟩
    · rintro ⟨(h1 | h1) | h1, h2⟩
      · exact ⟨.inl h1, h2⟩
      · exact ⟨.inr (.inl h1), h2⟩
      · exact ⟨.inr (.inr ⟨hty, h1⟩), h2⟩
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  rcases H with ⟨hgr, rfl⟩ | ⟨hgr, rfl⟩
  · refine Or.inl ⟨(hg.1 hgr).1, (hg.1 hgr).2, ?_⟩
    simp only [vrespMsgOf, if_neg hnv, ↓reduceIte, Bool.false_eq_true]
    rfl
  · refine Or.inr ⟨fun h => hgr (hg.2 h), ?_⟩
    simp only [vrespMsgOf, if_neg hnv, ↓reduceIte]
    rfl

/-- (antithesis parity B1, step B) **`MsgPreVote`** over `LiftScopeK` (`StepEnd.prevote`): stale, the
rejection at the node's term (`StaleEnd`'s third arm); within the lease ignored (`LeaseIgnore`); else
answered at the node's state (the preamble keeps a pre-vote request's state, `PreTermKeep`). -/
theorem recvEnd_of_stepEnd_preVoteK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgPreVote) (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .preVote m ents ctx) (toPState s') := by
  obtain ⟨hstl, hfr⟩ := h.prevote hty
  by_cases hs : StaleMsg s m
  · refine Or.inr (Or.inl ⟨hs.1, hs.2, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩)
    rw [hstl hs, toPState_sendMsgs]; rfl
  rcases hfr hs with ⟨hcq, hl, hlt, hcx, he⟩ | H
  · have hpl : (toPState s).lead ≠ W64 0 := by
      by_cases hr : s.role = .preCandidate
      · exact absurd (hsc.2.2.1 hr) hl
      · rw [toPState_lead_nonpre s hr]; exact hl
    exact Or.inr (Or.inr (Or.inl ⟨h0, ⟨hsc.1.trans hcq, .inr rfl, hlt, hpl, hcx⟩, by rw [he]⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨h0, toPState s, ?_, ie_handle_preVote c ents ctx hsc.2.2.1 hty H⟩))
    have h2 : ¬ uint.Z m.Term' < uint.Z s.term := fun hl => hs ⟨h0, hl⟩
    by_cases hgt : uint.Z s.term < uint.Z m.Term'
    · exact Or.inr (Or.inr ⟨hgt, Or.inl rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨by show m.Term' = s.term; word, rfl⟩)

/-- A quorum of a larger set: `IsQuorum` is monotone in the voters it counts. -/
theorem ie_isQuorum_mono {cfg q q' : GSet w64} (h : q ⊆ q') (hq : IsQuorum cfg q) :
    IsQuorum cfg q' := by
  unfold IsQuorum at *
  have hs : q ∩ cfg ⊆ q' ∩ cfg := by
    rw [GMap.elem_of_subseteq] at h ⊢; set_solver
  have := GMap.subseteq_size hs
  omega

/-- A recorded rejection adds no grant, so it does not make a tally a quorum. -/
theorem ie_not_jquorum_reject {c : CfgM} {votes : GMap w64 Bool} {src : w64}
    (h : ¬ JQuorum c (granted votes)) : ¬ JQuorum c (granted (recordVote votes src false)) := by
  have hsub : granted (recordVote votes src false) ⊆ granted votes := by
    rw [GMap.elem_of_subseteq]
    intro v hv
    rcases elem_of_granted_recordVote votes src false v hv with h1 | ⟨-, h2⟩
    · exact h1
    · cases h2
  rintro ⟨h1, h2⟩
  refine h ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · exact .inl h1
    · exact .inr (ie_isQuorum_mono hsub h1)
  · rcases h2 with h2 | h2
    · exact .inl h2
    · exact .inr (ie_isQuorum_mono hsub h2)

/-- (antithesis parity B1, step B) `Step`'s `MsgPreVoteResp` at the protocol level (`HandleEnd`'s
`.preVoteResp` arm): ignored at a follower, a candidate and a leader; at a pre-candidate (a follower
with no leader in `PState`) a pending or lost tally leaves `PState` as it is, and a win campaigns
(`CampaignSends`), only on a grant: the tally before it is not a quorum (`hq`, `RnScope`'s
pre-candidate conjunct) and a recorded rejection adds no grant. -/
theorem ie_handle_preVoteResp {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgPreVoteResp)
    (hq : t.role = .preCandidate → ¬ JQuorum c (granted t.votes))
    (H : StepFnEnd c id t m ents ctx s') :
    HandleEnd k c id (toPState t) (absMsg .preVoteResp m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    split
    · exact Or.inl rfl
    · rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_neg (by rw [hr]; decide)] at hres
    subst hres
    rw [if_neg (fun h => by rw [toPState_role, hr] at h; simp [proleRole] at h)]
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    rw [if_neg (fun h => by rw [toPState_role, hr] at h; simp [proleRole] at h)]
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_pos hr] at hres
    obtain ⟨won, lost, peers, pvs, hwon, -, -, rfl⟩ := hres
    have hlead : t.lead = W64 0 := hsc.1 hr
    have hpf : (toPState t).role = .follower ∧ (toPState t).lead = W64 0 := by
      simp [toPState, hr, hlead, proleRole]
    rw [if_pos hpf]
    have Hs1 : toPState { t with votes := recordVote t.votes m.From' (!m.Reject') } = toPState t :=
      toPState_votes_pre _ _ hr
    cases won
    · refine Or.inl ?_
      cases lost
      · show toPState { { t with votes := recordVote t.votes m.From' (!m.Reject') } with prvals := pvs } = _
        rw [toPState_prvals_nl _ pvs (by simp [hr]), Hs1]
      · show toPState { becomeFollower { t with votes := recordVote t.votes m.From' (!m.Reject') }
            t.term (W64 0) with prvals := pvs } = _
        rw [toPState_prvals_nl _ pvs (by simp [becomeFollower]), toPState_becomeFollower, Hs1]
        simp [pbecomeFollower, toPState, hr, hlead, rdNL_rdNL, proleRole]
    · obtain ⟨hjq, hperm⟩ := hwon rfl
      refine Or.inr ⟨?_, peers, hperm, ?_⟩
      · cases hrj : m.Reject'
        · rfl
        · rw [hrj] at hjq
          exact absurd hjq (ie_not_jquorum_reject (hq hr))
      · show toPState { campaignState id { t with votes := recordVote t.votes m.From' (!m.Reject') }
            false peers with prvals := pvs } = _
        rw [toPState_prvals_nl _ _ (by simp [campaignState, sendMsgs, becomeCandidate])]
        simp only [campaignState, Bool.false_eq_true, ↓reduceIte]
        rw [toPState_sendMsgs, toPState_becomeCandidate, Hs1]
        rfl

/-- (antithesis parity B1, step B) **`MsgPreVoteResp`** over `LiftScopeK`: stale, ignored; a grant
keeps the preamble's state (`PreTermKeep`, at a higher term too); a rejection of a higher term steps
down (the preamble), which then ignores it; the step function's answer `ie_handle_preVoteResp`, with
the pre-candidate's tally not a quorum (`hq`, from `RnScope`). -/
theorem recvEnd_of_stepEnd_preVoteRespK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hq : s.role = .preCandidate → ¬ JQuorum c (granted s.votes))
    (hty : m.Type' = MsgPreVoteResp) (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .preVoteResp m ents ctx) (toPState s') := by
  have hT : StepEndTy m.Type' := by unfold StepEndTy; ie_tyclose hty
  have hpv : m.Type' ≠ MsgPreVote := by rw [hty]; ie_tyclose MsgPreVote
  by_cases hst : StaleMsg s m
  · exact ie_recvEnd_staleK ⟨hsc.1, hsc.2.1⟩ (by rw [hty]; rfl) hpv hst (h hT (by xtrec_tac))
  obtain ⟨-, -, -, hfn⟩ := h hT (by xtrec_tac)
  obtain ⟨pvs, H⟩ := hfn hst (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote)
  have hfs := FnScope.of_preStateK hsc (m := m) pvs
  have h2 : ¬ uint.Z m.Term' < uint.Z s.term := fun hl => hst ⟨h0, hl⟩
  cases hrj : m.Reject'
  · -- a grant: the preamble keeps the state
    have hnb : ¬ PreBF m s := fun hb => hb.2.2 ⟨hty, hrj⟩
    have hps : preState s m pvs = s := by unfold preState; rw [if_neg hnb]
    rw [hps] at H hfs
    refine Or.inr (Or.inr (Or.inr ⟨h0, toPState s, ?_, ie_handle_preVoteResp hfs hty hq H⟩))
    by_cases hgt : uint.Z s.term < uint.Z m.Term'
    · exact Or.inr (Or.inr ⟨hgt, Or.inr ⟨rfl, by show m.Reject' = false; exact hrj⟩, rfl⟩)
    · exact Or.inr (Or.inl ⟨by show m.Term' = s.term; word, rfl⟩)
  · -- a rejection: the preamble as for the other types
    have hbf : PreBF m s ↔ uint.Z s.term < uint.Z m.Term' :=
      ⟨fun hb => hb.1, fun hgt => ⟨hgt, hpv, fun hh => by rw [hrj] at hh; exact absurd hh.2 (by decide)⟩⟩
    have hpk : ¬ PreTermKeep (absMsg .preVoteResp m ents ctx) := by
      rintro (hh | ⟨-, hh⟩)
      · exact absurd (show MsgType.preVoteResp = MsgType.preVote from hh) (by decide)
      · have : m.Reject' = false := hh
        rw [hrj] at this; exact absurd this (by decide)
    have hq' : (preState s m pvs).role = .preCandidate →
        ¬ JQuorum c (granted (preState s m pvs).votes) := by
      unfold preState
      split
      · intro hr; simp [becomeFollower] at hr
      · exact hq
    exact Or.inr (Or.inr (Or.inr ⟨h0, _,
      ie_preEnd_preState pvs h0 hst hbf (by unfold preLead; ie_tyclose hty) hpk,
      ie_handle_preVoteResp hfs hty hq' H⟩))

/-- (antithesis parity B1, step B) `Step`'s `MsgReadIndexResp` at the protocol level (`HandleEnd`'s
`.readIndexResp` arm): a follower records the read state of a one-entry response (`stepFollower`'s
`addReadState`) and ignores any other; a candidate, a pre-candidate (a follower with no leader in
`PState`) and a leader ignore it. -/
theorem ie_handle_readIndexResp {c : CfgM} {id : w64} {t : NState} {m : MessageM}
    {ents : List EntryM} {ctx : List w8} {s' : NState} (hsc : FnScope c id t)
    (hty : m.Type' = MsgReadIndexResp) (H : StepFnEnd c id t m ents ctx s') :
    HandleEnd k c id (toPState t) (absMsg .readIndexResp m ents ctx) (toPState s') := by
  obtain ⟨hf, hc, hl⟩ := H
  unfold HandleEnd
  dsimp only [absMsg, absMsgFrom]
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_pos (by rw [toPState_role, hr]; rfl)]
    rcases ents with _ | ⟨e, _ | ⟨e2, es⟩⟩
    · simp only at hres; subst hres; exact Or.inr (Or.inl ⟨by simp, rfl⟩)
    · simp only at hres; subst hres
      refine Or.inl ⟨e, rfl, ?_⟩
      have hnl : t.role ≠ .leader := by rw [hr]; decide
      simp [addReadState, toPState, hnl, hr, rdNL]
    · simp only at hres; subst hres; exact Or.inr (Or.inl ⟨by simp, rfl⟩)
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    rw [if_pos (by simp [toPState, hr, proleRole])]
    exact Or.inr (Or.inr ⟨by simp [toPState, hr, hsc.1 hr], rfl⟩)
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    rw [if_neg (by rw [toPState_role, hr]; decide)]

/-- (antithesis parity B1, step B) **`MsgReadIndexResp`** over `LiftScopeK` (a leader's answer,
stamped with its term): stale, ignored; else after the preamble `ie_handle_readIndexResp`. -/
theorem recvEnd_of_stepEnd_readIndexRespK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hty : m.Type' = MsgReadIndexResp) (h0 : m.Term' ≠ W64 0) (h : StepEnd c id m ents ctx s s') :
    RecvEnd k c id (toPState s) (absMsg .readIndexResp m ents ctx) (toPState s') :=
  ie_recvEnd_fnK hsc (by rw [hty]; rfl) (by rw [hty]; ie_tyclose MsgPreVote)
    (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote) h0
    (by unfold PreBF; ie_tyclose hty) (by unfold preLead; ie_tyclose hty)
    (ie_not_preTermKeep (by decide) (by decide))
    (fun _ hsc' _ H => ie_handle_readIndexResp hsc' hty H)
    (h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac))

/-- (antithesis parity B1, step B) `Step`'s step function on a `MsgTimeoutNow` at `t` (the state after
the preamble): a follower runs `hup(campaignTransfer)` (`HupOkC`): nothing, or the campaign with the
transfer marker on its requests (`CampaignEnd` at `ctxTransfer`); a candidate or pre-candidate ignores it
(`stepCandidate`); a leader's spec gives the transfer types' appends (`ReplSends`, `SendsEnd`). -/
theorem ie_handle_timeoutNow {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgTimeoutNow)
    (hns : NoSnapSent (toPState t) (toPState s')) (H : StepFnEnd c id t m ents ctx s') :
    toPState s' = toPState t ∨ ((toPState t).role = .leader ∧ SendsEnd c id (toPState t) (toPState s')) ∨
      ((toPState t).role = .follower ∧ CampaignEnd c id (toPState t) ctxTransfer (toPState s')) := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hup, -⟩ := hres
    obtain ⟨-, -, -, -, hg⟩ := hup
    rcases hg with ⟨-, rfl⟩ | ⟨⟨-, hv, -, -⟩, -, peers, pvs, hperm, rfl⟩
    · exact Or.inl rfl
    · have hd : decide (campaignTransfer = campaignPreElection) = false := by
        simp (config := {decide := true}) [campaignTransfer, campaignPreElection]
      have hcx : transferCtx campaignTransfer = ctxTransfer := by
        simp [transferCtx, ctxTransfer, campaignTransfer]
      refine Or.inr (Or.inr ⟨by rw [toPState_role, hr]; rfl, hv, peers, hperm, ?_⟩)
      rw [hd, hcx, toPState_prvals_nl _ _ (by simp [campaignState, sendMsgs, becomeCandidate])]
      simp only [campaignState, Bool.false_eq_true, ↓reduceIte]
      rw [toPState_sendMsgs, toPState_becomeCandidate]
      rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact Or.inl rfl
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact Or.inl rfl
  | leader =>
    obtain ⟨-, -, hpc⟩ := hsc.2.2 (by rw [hr]; decide)
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC at hres
    rw [if_neg (by rw [hty]; ie_tyclose MsgProp)] at hres
    obtain ⟨-, hres⟩ := hres
    unfold LeaderNonpropResultC at hres
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨-, lt', ms, pvs, rfl, ⟨hrs, -⟩, hpm, -⟩ | ⟨h, -⟩
    rotate_right 2
    · have he : toPState { sendMsgs { t with lt := lt' } ms with prvals := pvs } =
          psendMsgs (toPState t) ms := ie_toPState_send_prvals _ ms pvs (fun _ => hpm)
      refine Or.inr (Or.inl ⟨by rw [toPState_role, hr]; rfl, ms, fun y hy => ?_, he⟩)
      have hn := hns ms (by rw [he]; rfl) y hy
      exact ⟨(hrs y hy).1.app hn, (hrs y hy).2.1, ie_dst_ids rfl hpc (hrs y hy).2.2.1⟩
    all_goals (exfalso; ie_tysimp hty at h)

/-- (antithesis parity B1, step B) **`MsgTimeoutNow`** (a leader's, stamped with its term) over
`LiftScopeK`: stale, ignored; else after the preamble (a higher term: a follower with no leader,
`preLead`), `ie_handle_timeoutNow`: `TimeoutNowEndR`'s protocol part. -/
theorem timeoutNowEnd_of_stepEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s) (hty : m.Type' = MsgTimeoutNow)
    (h0 : m.Term' ≠ W64 0) (hns : NoSnapSent (toPState s) (toPState s'))
    (h : StepEnd c id m ents ctx s s') :
    (uint.Z m.Term' < uint.Z (toPState s).term ∧ toPState s' = toPState s) ∨
    (uint.Z (toPState s).term ≤ uint.Z m.Term' ∧
      ∃ p1, (uint.Z (toPState s).term < uint.Z m.Term' ∧ p1 = pbecomeFollower (toPState s) m.Term' (W64 0) ∨
              m.Term' = (toPState s).term ∧ p1 = toPState s) ∧
        (toPState s' = p1 ∨ (p1.role = .leader ∧ SendsEnd c id p1 (toPState s')) ∨
         (p1.role = .follower ∧ CampaignEnd c id p1 ctxTransfer (toPState s')))) := by
  have hT : StepEndTy m.Type' := by unfold StepEndTy; ie_tyclose hty
  obtain ⟨hs, -, -, hfn⟩ := h hT (by xtrec_tac)
  by_cases hst : StaleMsg s m
  · refine Or.inl ⟨hst.2, ?_⟩
    rcases hs hst with rfl | ⟨ty', mm, hlow, -⟩
    · rfl
    · exfalso
      rcases hlow with ⟨-, -, hha, -⟩ | ⟨-, hp, -⟩
      · rcases hha with e | e <;> rw [hty] at e <;> ie_tysimp e at e
      · rw [hty] at hp; ie_tysimp hp at hp
  · have h2 : ¬ uint.Z m.Term' < uint.Z s.term := fun hl => hst ⟨h0, hl⟩
    refine Or.inr ⟨by show uint.Z s.term ≤ _; omega, ?_⟩
    obtain ⟨pvs, H⟩ := hfn hst (by rw [hty]; ie_tyclose MsgHup) (by rw [hty]; ie_tyclose MsgVote)
    have hbf : PreBF m s ↔ uint.Z s.term < uint.Z m.Term' := by unfold PreBF; ie_tyclose hty
    have hpl : preLead m = W64 0 := by unfold preLead; ie_tyclose hty
    refine ⟨toPState (preState s m pvs), ?_,
      ie_handle_timeoutNow (FnScope.of_preStateK hsc pvs) hty
        (hns.of_outbox (ie_preState_outbox s m pvs)) H⟩
    rw [ie_toPState_preState, hpl]
    by_cases hb : PreBF m s
    · rw [if_pos hb]; exact Or.inl ⟨hbf.1 hb, rfl⟩
    · rw [if_neg hb]
      refine Or.inr ⟨?_, rfl⟩
      have h1 : ¬ uint.Z s.term < uint.Z m.Term' := fun h => hb (hbf.2 h)
      show m.Term' = s.term
      word

/-- (antithesis parity B1, step B) **A tick's `MsgCheckQuorum`** (`tickHeartbeat`, check-quorum on):
nothing at a non-leader; a leader stays (its `Progress` values of the same `Match`) or steps down at its
term with no leader known (`becomeFollower(r.Term, None)`): `TickEnd`'s step-down arm. -/
theorem cqEnd_of_stepEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hty : m.Type' = MsgCheckQuorum) (h0 : m.Term' = W64 0)
    (h : StepEnd c id m ents ctx s s') :
    (toPState s' = toPState s ∧ s'.role = s.role) ∨
    (s.role = .leader ∧ toPState s' = pbecomeFollower (toPState s) (toPState s).term (W64 0) ∧
      s'.role = .follower) := by
  obtain ⟨hf, hc, hl⟩ := ie_fn_local (by unfold StepEndTy; ie_tyclose hty) (by rw [hty]; ie_tyclose MsgHup)
      (by rw [hty]; ie_tyclose MsgVote) h0 h
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    exact Or.inl ⟨by rw [hs], by rw [hs, hr]⟩
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    exact Or.inl ⟨by rw [hs], by rw [hs, hr]⟩
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    exact Or.inl ⟨by rw [hs], by rw [hs, hr]⟩
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    ie_tysimp hty at hres
    obtain ⟨-, pvs, ⟨hpm, rfl⟩ | rfl⟩ := hres
    · exact Or.inl ⟨toPState_prvals s pvs (fun _ => hpm), hr⟩
    · refine Or.inr ⟨rfl, ?_, rfl⟩
      rw [toPState_prvals_nl _ _ (by simp [becomeFollower]), toPState_becomeFollower]
      rfl

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
off), or a pre-campaign (pre-vote on); the node's flag `k.prevote` the state's. -/
theorem tickEnd_of_stepEnd_hup {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hk : k.prevote = s.prevote) (hty : m.Type' = MsgHup)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') :
    TickEnd k c id (toPState s) (toPState s') := by
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  obtain ⟨-, hhup, -, -⟩ := h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac)
  obtain ⟨-, -, -, -, hg⟩ := hhup hst hty
  rcases hg with ⟨-, rfl⟩ | ⟨⟨hnl, hv, -, -⟩, -, peers, pvs, hperm, rfl⟩
  · exact Or.inl rfl
  · have hnl' : (toPState s).role ≠ .leader := by
      rw [toPState_role]; exact proleRole_not_leader _ hnl
    rw [hupType_pre_iff, hupType_ctx]
    cases hpv : s.prevote
    · refine Or.inr (Or.inl ⟨hnl', by rw [hk, hpv], hv, peers, hperm, ?_⟩)
      rw [toPState_prvals_nl _ _ (by simp [campaignState, sendMsgs, becomeCandidate])]
      simp only [campaignState, Bool.false_eq_true, ↓reduceIte]
      rw [toPState_sendMsgs, toPState_becomeCandidate]
      rfl
    · refine Or.inr (Or.inr (Or.inl ⟨hnl', by rw [hk, hpv], hv, peers, hperm, ?_⟩))
      rw [toPState_prvals_nl _ _ (by simp [campaignState, sendMsgs, becomePrecandidate])]
      simp only [campaignState, ↓reduceIte]
      rw [toPState_sendMsgs, toPState_becomePrecandidate]
      have hm : (toPState s).matched = ∅ := by simp [toPState, hnl]
      have hr : (toPState s).rd = rdNL s.rd := by simp [toPState, hnl]
      have ht : (toPState s).term = s.term := rfl
      simp only [pbecomeFollower, ht, eq_self_iff_true, ite_true, ↓reduceIte, hm, hr, rdNL_rdNL]
      rfl

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
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [toPState_role, hr]; rfl, ms,
      fun y hy => ⟨(hok y hy).1, (hok y hy).2.2.1, (hok y hy).2.2.2.1, (hok y hy).2.2.2.2.1,
        by rw [(hok y hy).2.1]; unfold hbCtx; rw [hpend, hro]; simp, ie_dst_ids rfl hpc (hok y hy).2.2.2.2.2⟩,
      ie_toPState_send_prvals s ms pvs (fun _ => hpm)⟩)))

/-- (#33 S4) **A tick's `MsgHup` keeps the log's state** (`HupOkC`: a campaign touches no log
field), `offsetInProgress` with it. -/
theorem logst_of_stepEnd_hup {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hty : m.Type' = MsgHup) (h0 : m.Term' = W64 0)
    (h : StepEnd c id m ents ctx s s') : s'.logst = s.logst := by
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  obtain ⟨-, hhup, -, -⟩ := h (by unfold StepEndTy; ie_tyclose hty) (by xtrec_tac)
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
