/-
Lean-first (#33 S4, P-raft-3, `notes/antithesis-rawnode-design.md` §2.6, §2.7). **A network message's
`Step`, at the protocol level, for `RawNode.Step.absSpec`**:
- the in-progress boundary after the step (`ipEnd_of_stepEnd`): `ip' = min ip (lcpLen log log')`; a
  `MsgApp` moves it exactly as `maybeAppendIp` (`HandleAppResult`'s accepting arm, `maybeAppendIp_lcp`),
  every other type of the harness's network keeps it and only appends to the log (`LogGrow`: a won
  election's empty entry, `becomeLeader`'s `logAppend`; else the log kept);
- the exact effect (`recvEnd_of_stepEnd_net`): `RecvEnd` at the message's abstraction, by type, from
  `InputEndLift.lean`'s lifting lemmas; at the harness's configuration `rnCfg γ` for a node whose
  configuration has its halves (`RecvEnd.of_halves`: the relations read the configuration's quorums
  only, for these types).
Both walk `StepEnd`'s arms as the lifting lemmas do.
-/
module

public import Proof.go_etcd_io.raft.v3.InputEndLift
public import Proof.go_etcd_io.raft.v3.InputEndIp
public import Proof.go_etcd_io.raft.v3.RawNodeAbsSpecs
public import Proof.go_etcd_io.raft.v3.StepEndBk
-- `noConfIn_of_unapplied`
public import Proof.go_etcd_io.raft.v3.StepLemmasR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable {k : NodeK}
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The message-type constants unfolded, the `if`s on them decided (`InputEndLift.lean`'s
`ie_tysimp`, which is local there). -/
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

/-- A goal about message-type constants, closed by unfolding and deciding them. -/
local syntax "se_tyclose " term : tactic
macro_rules
  | `(tactic| se_tyclose $e:term) =>
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

/-! ### The log's state across a step that does not truncate -/

/-- **The log only appended to, the in-progress boundary kept** (`offsetInProgress`): what every
step of the harness's network types but a `MsgApp` does to the log's state. -/
def LogGrow (ls ls' : LogState) : Prop :=
  ls'.inprogress = ls.inprogress ∧ ∃ x, ls'.sents ++ ls'.uents = ls.sents ++ ls.uents ++ x

/-- The log's state kept (up to what `LogGrow` reads). -/
theorem LogGrow.keep {ls ls' : LogState} (hi : ls'.inprogress = ls.inprogress)
    (he : ls'.sents ++ ls'.uents = ls.sents ++ ls.uents) : LogGrow ls ls' :=
  ⟨hi, [], by rw [he, List.append_nil]⟩

/-- `Step`'s preamble keeps the log's state (`becomeFollower` does not touch it). -/
theorem preState_logst (s : NState) (m : MessageM) (pvs : GMap w64 Progress) :
    (preState s m pvs).logst = s.logst := by
  unfold preState; split <;> rfl

/-- A boundary kept and a log appended to: the boundary is `min` of itself and the common prefix. -/
theorem ip_of_logGrow {ls ls' : LogState} (h : LogGrow ls ls')
    (hhi : uint.Z ls.inprogress ≤ ((ls.sents ++ ls.uents).length : Int) + 1) :
    uint.nat ls'.inprogress - 1 =
      min (uint.nat ls.inprogress - 1) (lcpLen (ls.sents ++ ls.uents) (ls'.sents ++ ls'.uents)) := by
  obtain ⟨hi, x, hx⟩ := h
  rw [hi, hx]
  have := uint_nat_eq ls.inprogress
  exact ip_eq_min_of_append (by omega)

/-! ### By type, at the step function's state -/

theorem logGrow_fn_heartbeat {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgHeartbeat)
    (H : StepFnEnd c id t m ents ctx s') : LogGrow t.logst s'.logst := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, pvs, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, pvs, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    exact LogGrow.keep rfl rfl

theorem logGrow_fn_appResp {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgAppResp)
    (H : StepFnEnd c id t m ents ctx s') : LogGrow t.logst s'.logst := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | leader =>
    obtain ⟨hpend, -, -⟩ := hsc.2.2 (by rw [hr]; decide)
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, hres⟩ := hres
    rcases hres with ⟨-, hs⟩ | ⟨-, -, ms, pvs, rfl, -, -⟩ | ⟨-, -, hA⟩
    · rw [hs]; exact LogGrow.keep rfl rfl
    · exact LogGrow.keep rfl rfl
    · obtain ⟨x, pvs, n, hb, ms, -, -, -, -, -, -, hif⟩ := hA
      by_cases hnc : n = t.logst.committed
      · rw [if_pos hnc] at hif
        obtain ⟨-, rfl⟩ := hif
        exact LogGrow.keep rfl rfl
      · rw [if_neg hnc] at hif
        rcases hif with ⟨-, hrel, rfl⟩ | ⟨-, -, rfl⟩
        · have hb0 : hb = [] := by
            cases hb with
            | nil => rfl
            | cons y _ =>
              obtain ⟨-, -, k, hk1, hk2, -⟩ := hrel y List.mem_cons_self
              simp only [hpend, List.length_nil] at hk2
              omega
          subst hb0
          have hT : sendMsgs (sendMsgs (releasedState id
              { t with logst := { t.logst with committed := n } }) []) ms =
              sendMsgs { t with logst := { t.logst with committed := n } } ms := by
            rw [ie_sendMsgs_nil, ie_releasedState_nil id { t with logst := { t.logst with committed := n } } hpend]
          show LogGrow t.logst (sendMsgs (sendMsgs (releasedState id
              { t with logst := { t.logst with committed := n } }) []) ms).logst
          rw [hT]
          exact LogGrow.keep rfl rfl
        · have hp : pendReqs { t with logst := { t.logst with committed := n } } = [] := by
            simp [pendReqs, hpend]
          have hT : sendMsgs (readRespondAll id
              { t with logst := { t.logst with committed := n }, rd := { t.rd with pend := [] } }
              (pendReqs { t with logst := { t.logst with committed := n } })) ms =
              sendMsgs { t with logst := { t.logst with committed := n } } ms := by
            rw [hp]
            have h2 := ie_rd_pend_nil { t with logst := { t.logst with committed := n } } hpend
            exact congrArg (fun x => sendMsgs x ms) h2
          show LogGrow t.logst (sendMsgs (readRespondAll id
              { t with logst := { t.logst with committed := n }, rd := { t.rd with pend := [] } }
              (pendReqs { t with logst := { t.logst with committed := n } })) ms).logst
          rw [hT]
          exact LogGrow.keep rfl rfl

theorem logGrow_fn_heartbeatResp {c : CfgM} {id : w64} {t : NState} {m : MessageM}
    {ents : List EntryM} {ctx : List w8} {s' : NState} (hsc : FnScope c id t)
    (hty : m.Type' = MsgHeartbeatResp) (hctx : ctx = []) (H : StepFnEnd c id t m ents ctx s') :
    LogGrow t.logst s'.logst := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, ms, pvs, -, -, hres⟩ := hres
    rcases hres with ⟨-, rfl⟩ | ⟨hne, -⟩
    · exact LogGrow.keep rfl rfl
    · exact absurd hctx hne

theorem logGrow_fn_voteResp {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgVoteResp)
    (H : StepFnEnd c id t m ents ctx s') : LogGrow t.logst s'.logst := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact LogGrow.keep rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_neg (by rw [hr]; decide)] at hres
    obtain ⟨won, lost, ms, pvs, -, -, -, rfl⟩ := hres
    cases won
    · cases lost
      · exact LogGrow.keep rfl rfl
      · exact LogGrow.keep rfl rfl
    · exact ⟨rfl, _, (List.append_assoc _ _ _).symm⟩
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_pos hr] at hres
    subst hres
    exact LogGrow.keep rfl rfl
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    exact LogGrow.keep rfl rfl

theorem logGrow_vote {id : w64} {t : NState} {m : MessageM} {s' : NState} (H : VoteEnd id t m s') :
    LogGrow t.logst s'.logst := by
  rcases H with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact LogGrow.keep rfl rfl

/-- **A `MsgApp`'s step function's log**: kept, or `handleAppendEntries`' accepting arm at the
log's state `ls` (`HandleAppResult`). -/
theorem app_fn_logst {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgApp)
    (H : StepFnEnd c id t m ents ctx s') :
    s'.logst = t.logst ∨
    ∃ lastnewi es', plogMaybeAppend t.logst.prev (t.logst.sents ++ t.logst.uents)
        (entryID.mk m.LogTerm' m.Index') ents = some (lastnewi, es') ∧
      s'.logst.sents ++ s'.logst.uents = es' ∧ s'.logst.inprogress = maybeAppendIp t.logst ents := by
  have hres_of : ∀ t1 : NState, t1.logst = t.logst → HandleAppResult id t1 m ents s' →
      s'.logst = t.logst ∨
      ∃ lastnewi es', plogMaybeAppend t.logst.prev (t.logst.sents ++ t.logst.uents)
          (entryID.mk m.LogTerm' m.Index') ents = some (lastnewi, es') ∧
        s'.logst.sents ++ s'.logst.uents = es' ∧ s'.logst.inprogress = maybeAppendIp t.logst ents := by
    intro t1 hl hres
    unfold HandleAppResult at hres
    rw [hl] at hres
    rcases hres with ⟨-, rfl⟩ | ⟨-, lastnewi, es', ls', Happ, -, Hes, -, -, -, ⟨-, Hip⟩, rfl⟩ |
        ⟨-, -, -, -, -, -, rfl⟩
    · exact .inl hl
    · exact .inr ⟨lastnewi, es', Happ, Hes, Hip⟩
    · exact .inl hl
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    exact hres_of _ (by rfl) hres
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, pvs, hres⟩ := hres
    exact hres_of _ (by rfl) hres
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, pvs, hres⟩ := hres
    exact hres_of _ (by rfl) hres
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    exact .inl rfl

/-! ### The boundary after a network message's step -/

/-- A stale message's step leaves the log's state (no answer in the scope, or `sendMsgs`). -/
theorem logst_of_stale {id : w64} {s s' : NState} {m : MessageM}
    (h : s' = s ∨ ∃ (ty : w32) (mm : Msg), LowSend id s m ty mm ∧ s' = sendMsgs s [mm]) :
    s'.logst = s.logst := by
  rcases h with rfl | ⟨-, -, -, rfl⟩ <;> rfl

/-- **The in-progress boundary after a `Step` of the harness's network types** (in the lifting
lemmas' scope, at a log from `base0` with the boundary inside it): `min` of the boundary before and
the common prefix of the logs before and after. A `MsgApp` (its batch well formed, `AppPayloadOk`)
as `maybeAppendIp` (`maybeAppendIp_lcp`), the other types by `LogGrow`. -/
theorem ipEnd_of_stepEnd {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' ∈ antStepTypes)
    (h0 : m.Term' ≠ W64 0) (hctx : m.Type' = MsgHeartbeatResp → ctx = [])
    (hwf : m.Type' = MsgApp → PlogWf (entryID.mk m.LogTerm' m.Index') ents)
    (hp : uint.Z s.logst.prev.index' = 0) (hlo : 1 ≤ uint.Z s.logst.inprogress)
    (hhi : uint.Z s.logst.inprogress ≤ ((s.logst.sents ++ s.logst.uents).length : Int) + 1)
    (h : StepEnd c id m ents ctx s s') (hnx : ¬ XtRec id m s := by xtrec_tac) :
    uint.nat s'.logst.inprogress - 1 =
      min (uint.nat s.logst.inprogress - 1)
        (lcpLen (s.logst.sents ++ s.logst.uents) (s'.logst.sents ++ s'.logst.uents)) := by
  have hT : StepEndTy m.Type' := by
    unfold antStepTypes at hty
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hty
    unfold StepEndTy
    rcases hty with e | e | e | e | e | e <;> rw [e] <;> se_tyclose MsgApp
  have hkeep : s'.logst = s.logst → uint.nat s'.logst.inprogress - 1 =
      min (uint.nat s.logst.inprogress - 1)
        (lcpLen (s.logst.sents ++ s.logst.uents) (s'.logst.sents ++ s'.logst.uents)) := fun he =>
    ip_of_logGrow (ls' := s'.logst) (LogGrow.keep (by rw [he]) (by rw [he])) hhi
  obtain ⟨hst, -, hv, hfn⟩ := h hT (by xtrec_tac)
  by_cases hs : StaleMsg s m
  · exact hkeep (logst_of_stale (hst hs))
  unfold antStepTypes at hty
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hty
  have hh : m.Type' ≠ MsgHup := by
    rcases hty with e | e | e | e | e | e <;> rw [e] <;> se_tyclose MsgHup
  rcases hty with e | e | e | e | e | e
  · -- `MsgApp`
    obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    have hl0 := preState_logst s m pvs
    rcases app_fn_logst (FnScope.of_preState hsc pvs) e H with he | ⟨lni, es', Hma, Hes, Hip⟩
    · exact hkeep (he.trans hl0)
    · rw [hl0] at Hma Hip
      rw [Hes, Hip]
      exact maybeAppendIp_lcp Hma hp (hwf e) hlo hhi
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    have := logGrow_fn_appResp (FnScope.of_preState hsc pvs) e H
    rw [preState_logst] at this
    exact ip_of_logGrow this hhi
  · obtain ⟨pvs, H⟩ := hv hs e |>.resolve_left (fun h => by have hcq := h.1; rw [hsc.2.1] at hcq; cases hcq)
    have := logGrow_vote H
    rw [preState_logst] at this
    exact ip_of_logGrow this hhi
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    have := logGrow_fn_voteResp (FnScope.of_preState hsc pvs) e H
    rw [preState_logst] at this
    exact ip_of_logGrow this hhi
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    have := logGrow_fn_heartbeat (FnScope.of_preState hsc pvs) e H
    rw [preState_logst] at this
    exact ip_of_logGrow this hhi
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    have := logGrow_fn_heartbeatResp (FnScope.of_preState hsc pvs) e (hctx e) H
    rw [preState_logst] at this
    exact ip_of_logGrow this hhi

/-- **A proposal's step** (term `0`, no preamble): the log appended to (a leader's `proposed`) or kept
(a forward, a drop), the in-progress boundary kept. -/
theorem logGrow_of_stepEnd_prop {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgProp)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') : LogGrow s.logst s'.logst := by
  obtain ⟨hf, hc, hl⟩ := ie_fn_local (by unfold StepEndTy; se_tyclose hty)
    (by rw [hty]; se_tyclose MsgHup) (by rw [hty]; se_tyclose MsgVote) h0 h
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, hres⟩ := hres
    split at hres <;> (obtain ⟨-, hs⟩ := hres; rw [hs]; exact LogGrow.keep rfl rfl)
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, hs⟩ := hres
    rw [hs]; exact LogGrow.keep rfl rfl
  | preCandidate => exact absurd hr hsc.2.2.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨cs, -, -, hres⟩ := hres
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte] at hres
      obtain ⟨ms, pvs, rfl, -, -⟩ := hres
      exact ⟨rfl, _, (List.append_assoc _ _ _).symm⟩
    · simp only [↓reduceIte] at hres
      rcases hres with rfl | rfl <;> exact LogGrow.keep rfl rfl

/-! ### The exact effect, at the harness's configuration -/

/-- (#33 S4, destinations) `AppSendOk` reads the configuration's ids only. -/
theorem AppSendOk.of_ids {c c' : CfgM} {id : w64} {s : PState} {m : Msg} (hd : c.ids = c'.ids)
    (h : AppSendOk c id s m) : AppSendOk c' id s m :=
  ⟨h.1, h.2.1, hd ▸ h.2.2⟩

theorem SendsEnd.iff_of_ids {c c' : CfgM} (hd : c.ids = c'.ids) (id : w64) (s s' : PState) :
    SendsEnd c id s s' ↔ SendsEnd c' id s s' := by
  unfold SendsEnd AppSendOk; rw [hd]

theorem WinEnd.iff_of_ids {c c' : CfgM} (hd : c.ids = c'.ids) (id : w64) (s s' : PState) :
    WinEnd c id s s' ↔ WinEnd c' id s s' := by
  unfold WinEnd AppSendOk; rw [hd]

/-- (#33 S4, destinations) `ProposeEnd` reads the configuration's ids only. -/
theorem ProposeEnd.of_ids {c c' : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hd : c.ids = c'.ids) (h : ProposeEnd c id s m s') : ProposeEnd c' id s m s' := by
  unfold ProposeEnd at h ⊢
  by_cases hr : s.role = .leader
  · rw [if_pos hr] at h ⊢
    rcases h with h | ⟨es, ms, hp, hms, h⟩
    · exact .inl h
    · exact .inr ⟨es, ms, hp, fun x hx => (hms x hx).of_ids hd, h⟩
  · rw [if_neg hr] at h ⊢; exact h

/-- `HandleEnd` reads the configuration's halves and ids only, at the harness's types. -/
theorem HandleEnd.of_halves {c c' : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hi : c.incoming = c'.incoming) (ho : c.outgoing = c'.outgoing) (hd : c.ids = c'.ids)
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : HandleEnd k c id s m s') : HandleEnd k c' id s m s' := by
  unfold HandleEnd at h ⊢
  rcases hty with e | e | e | e | e | e <;> rw [e] at h ⊢ <;>
    simpa only [AppRespEnd, PCommitOk, JQuorum, JLost, hi, ho, SendsEnd.iff_of_ids hd,
      WinEnd.iff_of_ids hd, ReleaseEnd, HbSendOk, CfgSingle, ReadAckEnd, JQuorumAcked, hd] using h

/-- `RecvEnd` reads the configuration's halves and ids only, at the harness's types. -/
theorem RecvEnd.of_halves {c c' : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (hi : c.incoming = c'.incoming) (ho : c.outgoing = c'.outgoing) (hd : c.ids = c'.ids)
    (hty : m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : RecvEnd k c id s m s') : RecvEnd k c' id s m s' := by
  rcases h with ⟨h1, h2⟩ | h | h | ⟨h1, s1, h2, h3⟩
  · exact .inl ⟨h1, h2.of_halves hi ho hd hty⟩
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨h1, s1, h2, h3.of_halves hi ho hd hty⟩))

/-- **The exact effect of a `Step` of the harness's network types** (in the lifting lemmas'
scope; a heartbeat response with no context; nothing queued but no `MsgSnap`): `RecvEnd` at the
message's abstraction (`InputEndLift.lean`'s lemmas, by type). -/
theorem recvEnd_of_stepEnd_net {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' ∈ antStepTypes)
    (h0 : m.Term' ≠ W64 0) (hctx : m.Type' = MsgHeartbeatResp → ctx = [])
    (hns : NoSnapSent (toPState s) (toPState s')) (h : StepEnd c id m ents ctx s s') :
    ∀ ty, mtypeOf m.Type' = some ty →
      RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') ∧
      (ty = .app ∨ ty = .appResp ∨ ty = .vote ∨ ty = .voteResp ∨ ty = .heartbeat ∨
        ty = .heartbeatResp) := by
  intro ty hty'
  unfold antStepTypes at hty
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hty
  rcases hty with e | e | e | e | e | e <;> rw [e] at hty' <;> cases hty'
  · exact ⟨recvEnd_of_stepEnd_app hsc e h0 h, by simp⟩
  · exact ⟨recvEnd_of_stepEnd_appResp hsc e h0 hns h, by simp⟩
  · exact ⟨recvEnd_of_stepEnd_vote hsc e h0 h, by simp⟩
  · exact ⟨recvEnd_of_stepEnd_voteResp hsc e h0 hns h, by simp⟩
  · exact ⟨recvEnd_of_stepEnd_heartbeat hsc e h0 h, by simp⟩
  · exact ⟨recvEnd_of_stepEnd_heartbeatResp hsc e h0 (hctx e) hns h, by simp⟩

/-- A proposal's end relation keeps the read-index state. -/
theorem proposeEnd_rd {c : CfgM} {id : w64} {s : PState} {m : Msg} {s' : PState}
    (h : ProposeEnd c id s m s') :
    s'.rd = s.rd := by
  unfold ProposeEnd at h
  split at h
  · rcases h with rfl | ⟨es, ms, -, -, rfl⟩ <;> rfl
  · split at h <;> (subst h; rfl)

/-! ### The `RState` ends (antithesis parity B1, design §4): the bookkeeping from `BkStep` -/

/-- `logLast` is the protocol reading's last index (`TracedRaftStepPropBundle.lean`'s, restated: that
module is in the traced cone). -/
theorem logLast_eq_plastIndex' (s : NState) : logLast s.logst = plastIndex (toPState s) := by
  simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
  congr 1; push_cast; omega

/-- `pendingConfIndex` after a step as `PciNext` reads it, from `BkStep`. -/
theorem pciR_of_bk {rs : RNState} {fp : List EntryM} {s s' : NState} (h : BkStep s s') :
    pciR s' = PciNext (toRState rs fp s) (toPState s') := by
  have e' : (toPState s').role = .leader ↔ s'.role = .leader := proleRole_leader _
  have e : (toPState s).role = .leader ↔ s.role = .leader := proleRole_leader _
  show pciR s' = (if (toPState s').role = .leader then
      (if (toPState s).role = .leader then pciR s
       else W64 (plogLastIndexZ (toPState s).base (toPState s).log)) else W64 0)
  unfold pciR
  by_cases h1 : s'.role = .leader
  · rw [if_pos h1, if_pos (e'.2 h1)]
    rcases h.2 h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [if_pos (e.2 h2), if_pos h2, h3]
    · rw [if_neg (fun h => h2 (e.1 h)), h3, logLast_eq_plastIndex']; rfl
  · rw [if_neg h1, if_neg (fun h => h1 (e'.1 h))]

/-- **A received message's `RState` end** (not a proposal): `RecvEnd` at the node's configuration,
the bookkeeping from `BkStep`, the log's boundary and the pending snapshot kept (`FpNext`'s first
arm, at every `Adm`). -/
theorem recvEndR_of_bk {Adm : List EntryM → CCState → Prop} {id : w64}
    {rs rs' : RNState} {fp : List EntryM} {s s' : NState} {m : Msg}
    (hR : RecvEnd k rs.cfg.cfg id (toPState s) m (toPState s')) (hbk : BkStep s s')
    (hsn : s'.logst.snap = s.logst.snap) (hprev : s'.logst.prev = s.logst.prev)
    (hcf : rs'.capplied = rs.capplied ∧ rs'.cfg = rs.cfg) (hnp : m.ty ≠ .propose) :
    RecvEndR Adm k id (toRState rs fp s) m (toRState rs' fp s') := by
  refine ⟨hR, ⟨hbk.1, hcf.1, hcf.2⟩, .inl ⟨hprev, rfl, by simp only [toRState_snap, hsn]⟩,
    fun h => absurd h.1 hnp, fun _ => pciR_of_bk hbk⟩

/-- **A tick's `RState` end**: `TickEnd` at the node's configuration, the bookkeeping from `BkStep`. -/
theorem tickEndR_of_bk {id : w64} {rs rs' : RNState} {fp : List EntryM} {s s' : NState}
    (hT : TickEnd k rs.cfg.cfg id (toPState s) (toPState s')) (hbk : BkStep s s')
    (hsn : s'.logst.snap = s.logst.snap) (hcf : rs'.capplied = rs.capplied ∧ rs'.cfg = rs.cfg) :
    TickEndR k id (toRState rs fp s) (toRState rs' fp s') :=
  ⟨hT, ⟨hbk.1, hcf.1, hcf.2⟩, rfl, by simp only [toRState_snap, hsn], pciR_of_bk hbk⟩

/-- `PropRepl` with no conf-change entry is the identity. -/
theorem PropRepl.eq_of_noConf {es es' : List EntryM} (h : PropRepl es es')
    (hnc : ∀ e ∈ es, ¬ IsConfEnt e) : es' = es := by
  induction h with
  | nil => rfl
  | @cons e e' es es' h1 _ ih =>
    rcases h1 with rfl | ⟨hc, -⟩
    · rw [ih (fun x hx => hnc x (List.mem_cons_of_mem _ hx))]
    · exact absurd hc (hnc e List.mem_cons_self)

/-- No conf-change entry: the conf-change loop returns the batch and `pendingConfIndex`. -/
theorem propBatch_noConf (r : RState) (ents : List EntryM) (cs : List (Option ConfChangeIM))
    (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    propBatch r ents cs = (ents, r.pci) := by
  unfold propBatch propConf
  rw [bk_propConf_noConf_fold _ _ _ ents cs hct hnc]
  simp

/-- The all-`none` decoding is well typed for a batch with no conf-change entry. -/
theorem cctypesOk_none (ents : List EntryM) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    CCTypesOk ents (ents.map fun _ => none) := by
  induction ents with
  | nil => exact List.Forall₂.nil
  | cons e es ih =>
    refine List.Forall₂.cons ?_ (ih fun x hx => hnc x (List.mem_cons_of_mem _ hx))
    simp only [Option.isSome_none]
    exact (decide_eq_false (hnc e List.mem_cons_self)).symm

/-- **A proposal's `RState` end** (no conf-change entry): `ProposeEnd` at the node's configuration,
the bookkeeping from `BkStep`; a leader's appended batch is the conf-change loop's (`propBatch`, at
the all-`none` decoding) and keeps `pendingConfIndex`. -/
theorem recvEndR_of_prop {Adm : List EntryM → CCState → Prop} {id : w64}
    {rs rs' : RNState} {fp : List EntryM} {s s' : NState} {m : Msg}
    (hty : m.ty = .propose) (h0 : m.term = W64 0)
    (hP : ProposeEnd rs.cfg.cfg id (toPState s) m (toPState s')) (hbk : BkStep s s')
    (hsn : s'.logst.snap = s.logst.snap) (hprev : s'.logst.prev = s.logst.prev)
    (hcf : rs'.capplied = rs.capplied ∧ rs'.cfg = rs.cfg) (hnc : ∀ e ∈ m.entries, ¬ IsConfEnt e) :
    RecvEndR Adm k id (toRState rs fp s) m (toRState rs' fp s') := by
  have hR : RecvEnd k rs.cfg.cfg id (toPState s) m (toPState s') :=
    Or.inl ⟨h0, by unfold HandleEnd; rw [hty]; exact hP⟩
  refine ⟨hR, ⟨hbk.1, hcf.1, hcf.2⟩, .inl ⟨hprev, rfl, by simp only [toRState_snap, hsn]⟩,
    fun ⟨_, hl, hne⟩ => ?_, fun _ => pciR_of_bk hbk⟩
  simp only [toRState_p] at hl hne ⊢
  unfold ProposeEnd at hP
  rw [if_pos hl] at hP
  rcases hP with he | ⟨es, ms, hrep, -, he⟩
  · exact absurd (by rw [he]) hne
  have hes := hrep.eq_of_noConf hnc
  subst hes
  refine ⟨m.entries.map fun _ => none, cctypesOk_none _ hnc, ?_, ?_⟩
  · rw [propBatch_noConf _ _ _ (cctypesOk_none _ hnc) hnc, he]; rfl
  · rw [propBatch_noConf _ _ _ (cctypesOk_none _ hnc) hnc]
    have hl' : s'.role = .leader := by
      have : (toPState s').role = .leader := by rw [he]; exact hl
      exact (proleRole_leader _).1 this
    have hsl : s.role = .leader := (proleRole_leader _).1 hl
    rcases hbk.2 hl' with ⟨-, h3⟩ | ⟨h2, -⟩
    · simp only [toRState_pci, pciR, if_pos hl', if_pos hsl, h3]
    · exact absurd hsl h2


/-- (antithesis parity B1, phase 2) **`RawNode.Campaign`'s `RState` end** (`MsgHup`, no ghost prefix at
the boundary `0`, the node constant's pre-vote flag the node's): `hup`'s guard (`HupGuard`, at `hupType s`)
read as `CampaignEndR`'s, nothing done, an election with no context, or (pre-vote on) a pre-election,
with `hasUnappliedConfChanges`' answer on the full log (`noConfIn_of_unapplied`), the log kept. -/
theorem campaignEndR_of_stepEnd_hup {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {rs rs' : RNState} {s s' : NState} (hk : k.prevote = s.prevote)
    (hc : rs.cfg.cfg = c) (hty : m.Type' = MsgHup) (h0 : m.Term' = W64 0)
    (hprev : uint.Z s.logst.prev.index' = 0)
    (hac : uint.Z s.logst.applied ≤ uint.Z s.logst.committed)
    (hnw : uint.Z s.logst.committed + 1 < 2 ^ 64)
    (h : StepEnd c id m ents ctx s s') (hcf : rs'.capplied = rs.capplied ∧ rs'.cfg = rs.cfg) :
    CampaignEndR k id (toRState rs [] s) (toRState rs' [] s') := by
  have hl := logst_of_stepEnd_hup hty h0 h
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  obtain ⟨-, hhup, -, -⟩ := h (by unfold StepEndTy; se_tyclose hty) (by xtrec_tac)
  obtain ⟨-, -, -, -, hg⟩ := hhup hst hty
  have hbk : BkStep s s' := ⟨by rw [hl], fun hl' => by
    rcases hg.exists_pre_ctx with ⟨-, rfl⟩ | ⟨-, pre, peers, pvs, cl, -, -, rfl⟩
    · exact .inl ⟨hl', rfl⟩
    · exfalso
      cases pre <;> simp [campaignState, sendMsgs, becomeCandidate, becomePrecandidate] at hl'⟩
  refine ⟨?_, ⟨hbk.1, hcf.1, hcf.2⟩, rfl, by simp only [toRState_snap, hl], pciR_of_bk hbk⟩
  rcases hg with ⟨-, rfl⟩ | ⟨⟨hnl, hv, hsn, hno⟩, -, peers, pvs, hperm, rfl⟩
  · left
    unfold toRState
    rw [hcf.1, hcf.2]
  · right
    refine ⟨by rw [toRState_p, toPState_role]; exact proleRole_not_leader _ hnl, ?_,
      by simp only [toRState_snap, hsn, Option.isSome_none], ?_⟩
    · rintro ⟨kk, e, h1, h2, h3, h4⟩
      exact noConfIn_of_unapplied s.logst [] (by simp [hprev])
        (by rw [hprev]; exact uint_Z_nonneg _) hac hnw hno kk e h1 h2 h3 h4
    · rw [hupType_pre_iff, hupType_ctx, toRState_p, toRState_p, toRState_cfg, hc, hk]
      cases hpv : s.prevote
      · refine Or.inl ⟨rfl, hv, peers, hperm, ?_⟩
        rw [toPState_prvals_nl _ _ (by simp [campaignState, sendMsgs, becomeCandidate])]
        simp only [campaignState, Bool.false_eq_true, ↓reduceIte]
        rw [toPState_sendMsgs, toPState_becomeCandidate]
        rfl
      · refine Or.inr ⟨rfl, hv, peers, hperm, ?_⟩
        rw [toPState_prvals_nl _ _ (by simp [campaignState, sendMsgs, becomePrecandidate])]
        simp only [campaignState, ↓reduceIte]
        rw [toPState_sendMsgs, toPState_becomePrecandidate]
        have hm : (toPState s).matched = ∅ := by simp [toPState, hnl]
        have hr : (toPState s).rd = rdNL s.rd := by simp [toPState, hnl]
        have ht : (toPState s).term = s.term := rfl
        simp only [pbecomeFollower, ht, eq_self_iff_true, ite_true, ↓reduceIte, hm, hr, rdNL_rdNL]
        rfl

end pure

section ghost
variable {k : NodeK}
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode

/-- **No automatic leave at a non-joint configuration** (`CfgInv`'s last clause, the tracker's): what
`AckScope` asks of a static node. -/
theorem ownRaftPhysC_ackScope (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜c.outgoing = ∅ → c.autoLeave = false⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_tracker c r id s $$ H with ⟨%tv, Hf, Htrk, Hback⟩
  icases ownTrackerC_pure c tv _ $$ Htrk with ⟨%Hp, Htrk⟩
  isplitr
  · ipureintro; exact fun h => (Hp.1.2.2.2 h).2
  iapply Hback $$ %tv %s.votes Hf Htrk

/-- The basic scope's storage cap, read out (persistent). -/
theorem rnScopeAt_cap {γ : RaftNames} {id : w64} {sc : Bool} (h : sc = true) (rs : RNState)
    (s : NState) :
    rnScopeAt (GF := GF) γ id (basicScope sc) rs s ⊢
      storCapF s.logst.storage 0 ∗ rnScopeAt γ id (basicScope sc) rs s := by
  subst h
  unfold rnScopeAt basicScope
  iintro ⟨%H, #Hc⟩
  isplitr
  · iapply Hc; ipureintro; rfl
  · isplitr
    · ipureintro; exact H
    · imodintro; iexact Hc

end ghost

end EtcdGrove
end Perennial
