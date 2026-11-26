/-
Lean-first (#33 S4). **What `Step` does to the bookkeeping `toRState` reads beyond `toPState`**:
`applied` (`raftLog.applied`) and `pendingConfIndex`, read off `Step`'s exact end state (`StepEnd`,
`LemmasStepGates.lean`) in the lifting lemmas' scope (`LiftScope`, `InputEndLift.lean`), for the
harness's inputs: a network message (`bk_of_stepEnd_net`), a tick's `MsgHup` and `MsgBeat`
(`bk_of_stepEnd_hup`, `bk_of_stepEnd_beat`) and a proposal with no conf-change entry
(`bk_of_stepEnd_prop`). `applied` is kept by every arm (`handleAppendEntries` keeps it,
`HandleAppResult`); a leader after the step was one before, with `pendingConfIndex` kept, or is a
candidate that won its election (`becomeLeader`: `pendingConfIndex` at the log's last index).

The case analysis walks `StepEnd`'s arms as `StepEndIp.lean`'s `LogGrow` lemmas do.
-/
module

public import Proof.go_etcd_io.raft.v3.InputEndLift

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

set_option autoImplicit false

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

/-! ### The relations -/

/-- What a step does to the bookkeeping `toRState` reads beyond `toPState`: `applied` kept, and a
leader after the step was a leader before with `pendingConfIndex` kept, or became one with it at the
log's last index before the step (`becomeLeader`). -/
def BkStep (s s' : NState) : Prop :=
  s'.logst.applied = s.logst.applied ∧
  (s'.role = .leader →
    (s.role = .leader ∧ s'.pci = s.pci) ∨ (s.role ≠ .leader ∧ s'.pci = logLast s.logst))

/-- `BkStep` at the step function's state `t` (after the preamble): a new leader was a candidate
there, which the preamble's step-down does not make. -/
def BkFn (t s' : NState) : Prop :=
  s'.logst.applied = t.logst.applied ∧
  (s'.role = .leader →
    (t.role = .leader ∧ s'.pci = t.pci) ∨ (t.role = .candidate ∧ s'.pci = logLast t.logst))

theorem BkFn.keep {t s' : NState} (ha : s'.logst.applied = t.logst.applied) (hr : s'.role = t.role)
    (hp : s'.pci = t.pci) : BkFn t s' :=
  ⟨ha, fun h => .inl ⟨by rw [← hr]; exact h, hp⟩⟩

theorem BkFn.nl {t s' : NState} (ha : s'.logst.applied = t.logst.applied)
    (hr : s'.role ≠ .leader) : BkFn t s' :=
  ⟨ha, fun h => absurd h hr⟩

/-- At the state the step started in. -/
theorem BkFn.step {s s' : NState} (h : BkFn s s') : BkStep s s' := by
  refine ⟨h.1, fun hl => ?_⟩
  rcases h.2 hl with h' | ⟨hc, hp⟩
  · exact .inl h'
  · exact .inr ⟨by rw [hc]; decide, hp⟩

/-- Through `Step`'s preamble (`becomeFollower` at a higher term: the log kept, a follower). -/
theorem BkFn.ofPre {s s' : NState} {m : MessageM} {pvs : GMap w64 Progress}
    (h : BkFn (preState s m pvs) s') : BkStep s s' := by
  by_cases hb : PreBF m s
  · have hr : (preState s m pvs).role = .follower := by simp [preState, hb, becomeFollower]
    have hl : (preState s m pvs).logst = s.logst := by unfold preState; split <;> rfl
    refine ⟨by rw [h.1, hl], fun hl' => ?_⟩
    rcases h.2 hl' with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [hr] at h' <;> cases h'
  · rw [ie_preState_nobf hb] at h; exact h.step

theorem BkStep.of_stale {id : w64} {s s' : NState} {m : MessageM}
    (h : s' = s ∨ ∃ (ty : w32) (mm : Msg), LowSend id s m ty mm ∧ s' = sendMsgs s [mm]) :
    BkStep s s' := by
  rcases h with rfl | ⟨-, -, -, rfl⟩ <;> exact ⟨rfl, fun h => .inl ⟨h, rfl⟩⟩

/-- `handleAppendEntries` keeps the role and `applied` (`HandleAppResult`). -/
theorem bk_handleApp {id : w64} {t1 : NState} {m : MessageM} {ents : List EntryM} {s' : NState}
    (h : HandleAppResult id t1 m ents s') :
    s'.role = t1.role ∧ s'.logst.applied = t1.logst.applied := by
  unfold HandleAppResult at h
  rcases h with ⟨-, rfl⟩ | ⟨-, _, _, ls', -, -, -, Hap, -, -, -, rfl⟩ | ⟨-, -, -, -, -, -, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, Hap⟩
  · exact ⟨rfl, rfl⟩

/-! ### By type, at the step function's state -/

theorem bk_fn_heartbeat {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgHeartbeat)
    (H : StepFnEnd c id t m ents ctx s') : BkFn t s' := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.nl rfl (by simp [heartbeatResult, sendMsgs, hr])
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, pvs, rfl⟩ := hres
    exact BkFn.nl rfl (by simp [heartbeatResult, sendMsgs, becomeFollower])
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl

theorem bk_fn_app {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgApp)
    (H : StepFnEnd c id t m ents ctx s') : BkFn t s' := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    obtain ⟨hro, hap⟩ := bk_handleApp hres
    exact BkFn.nl hap (by rw [hro]; simp [hr])
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, pvs, hres⟩ := hres
    obtain ⟨hro, hap⟩ := bk_handleApp hres
    exact BkFn.nl hap (by rw [hro]; simp [becomeFollower])
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl

theorem bk_fn_appResp {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgAppResp)
    (H : StepFnEnd c id t m ents ctx s') : BkFn t s' := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, hres⟩ := hres
    rcases hres with ⟨-, rfl⟩ | ⟨-, -, ms, pvs, rfl, -, -⟩ | ⟨-, -, hA⟩
    · exact BkFn.keep rfl rfl rfl
    · exact BkFn.keep rfl rfl rfl
    · obtain ⟨x, pvs, n, hb, ms, -, -, -, -, -, -, hif⟩ := hA
      by_cases hnc : n = t.logst.committed
      · rw [if_pos hnc] at hif
        obtain ⟨-, rfl⟩ := hif
        exact BkFn.keep rfl rfl rfl
      · rw [if_neg hnc] at hif
        rcases hif with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
        · exact BkFn.keep rfl rfl rfl
        · obtain ⟨o, r, he⟩ := readRespondAll_eq id
            { t with logst := { t.logst with committed := n }, rd := { t.rd with pend := [] } }
            (pendReqs { t with logst := { t.logst with committed := n } })
          rw [he]
          exact BkFn.keep rfl rfl rfl

theorem bk_fn_heartbeatResp {c : CfgM} {id : w64} {t : NState} {m : MessageM}
    {ents : List EntryM} {ctx : List w8} {s' : NState} (hsc : FnScope c id t)
    (hty : m.Type' = MsgHeartbeatResp) (hctx : ctx = []) (H : StepFnEnd c id t m ents ctx s') :
    BkFn t s' := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, ms, pvs, -, -, hres⟩ := hres
    rcases hres with ⟨-, rfl⟩ | ⟨hne, -⟩
    · exact BkFn.keep rfl rfl rfl
    · exact absurd hctx hne

theorem bk_fn_voteResp {c : CfgM} {id : w64} {t : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} (hsc : FnScope c id t) (hty : m.Type' = MsgVoteResp)
    (H : StepFnEnd c id t m ents ctx s') : BkFn t s' := by
  obtain ⟨hf, hc, hl⟩ := H
  cases hr : t.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, hres⟩ := hres
    rw [if_neg (by rw [hr]; decide)] at hres
    obtain ⟨won, lost, ms, pvs, -, -, -, rfl⟩ := hres
    cases won
    · cases lost
      · exact BkFn.keep rfl rfl rfl
      · exact BkFn.nl rfl (by simp [voteRespResult, becomeFollower])
    · exact ⟨rfl, fun _ => .inr ⟨hr, rfl⟩⟩
  | preCandidate => exact absurd hr hsc.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl

theorem bk_vote {id : w64} {t : NState} {m : MessageM} {s' : NState} (H : VoteEnd id t m s') :
    BkFn t s' := by
  rcases H with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact BkFn.keep rfl rfl rfl

/-! ### The harness's inputs -/

/-- **A network message's step** (the harness's six protocol types, term nonzero, a
`MsgHeartbeatResp` with no read-index context). -/
theorem bk_of_stepEnd_net {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s)
    (hty : m.Type' = MsgApp ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgVote ∨ m.Type' = MsgVoteResp ∨
      m.Type' = MsgHeartbeat ∨ m.Type' = MsgHeartbeatResp)
    (h0 : m.Term' ≠ W64 0) (hctx : m.Type' = MsgHeartbeatResp → ctx = [])
    (h : StepEnd c id m ents ctx s s') : BkStep s s' := by
  have hT : StepEndTy m.Type' := by
    unfold StepEndTy
    rcases hty with e | e | e | e | e | e <;> rw [e] <;> se_tyclose MsgApp
  obtain ⟨hst, -, hv, hfn⟩ := h hT
  by_cases hs : StaleMsg s m
  · exact BkStep.of_stale (hst hs)
  have hh : m.Type' ≠ MsgHup := by
    rcases hty with e | e | e | e | e | e <;> rw [e] <;> se_tyclose MsgHup
  rcases hty with e | e | e | e | e | e
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    exact (bk_fn_app (FnScope.of_preState hsc pvs) e H).ofPre
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    exact (bk_fn_appResp (FnScope.of_preState hsc pvs) e H).ofPre
  · obtain ⟨pvs, H⟩ := hv hs e |>.resolve_left
      (fun h => by have hcq := h.1; rw [hsc.2.1] at hcq; cases hcq)
    exact (bk_vote H).ofPre
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    exact (bk_fn_voteResp (FnScope.of_preState hsc pvs) e H).ofPre
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    exact (bk_fn_heartbeat (FnScope.of_preState hsc pvs) e H).ofPre
  · obtain ⟨pvs, H⟩ := hfn hs hh (by rw [e]; se_tyclose MsgVote)
    exact (bk_fn_heartbeatResp (FnScope.of_preState hsc pvs) e (hctx e) H).ofPre

/-- **A tick's `MsgHup`**: the log kept (`HupOkC`), nothing done or a campaign (no leader). -/
theorem bk_of_stepEnd_hup {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgHup)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') : BkStep s s' := by
  have hst : ¬ StaleMsg s m := fun hs => hs.1 h0
  obtain ⟨-, hhup, -, -⟩ := h (by unfold StepEndTy; se_tyclose hty)
  obtain ⟨-, -, ⟨hlog, -⟩, -, hg⟩ := hhup hst hty
  refine ⟨by rw [hlog], fun hl => ?_⟩
  rcases hg.exists_pre_ctx with ⟨-, rfl⟩ | ⟨-, pre, peers, pvs, cl, -, -, rfl⟩
  · exact .inl ⟨hl, rfl⟩
  · exfalso
    cases pre <;> simp [campaignState, sendMsgs, becomeCandidate, becomePrecandidate] at hl

/-- **A tick's `MsgBeat`**: a leader's heartbeats; nothing elsewhere. -/
theorem bk_of_stepEnd_beat {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgBeat)
    (h0 : m.Term' = W64 0) (h : StepEnd c id m ents ctx s s') : BkStep s s' := by
  obtain ⟨hf, hc, hl⟩ := ie_fn_local (by unfold StepEndTy; se_tyclose hty)
    (by rw [hty]; se_tyclose MsgHup) (by rw [hty]; se_tyclose MsgVote) h0 h
  refine BkFn.step ?_
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | preCandidate => exact absurd hr hsc.2.2.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC LeaderNonpropResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, ms, pvs, rfl, -, -⟩ := hres
    exact BkFn.keep rfl rfl rfl

/-- The conf-change loop on a batch with no conf-change entry keeps it and `pendingConfIndex`
(`TracedRaftStepProp.lean`'s `propConf_noConf_fold'`, restated: that module is in the traced
cone). -/
theorem bk_propConf_noConf_fold (joint : Bool) (applied li : w64) (ents : List EntryM)
    (cs : List (Option ConfChangeIM)) (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    ∀ acc : List EntryM × w64,
      (ents.zip cs).foldl (propConfStep joint applied li) acc = (acc.1 ++ ents, acc.2) := by
  revert hnc
  induction hct with
  | nil => intro _ acc; simp
  | @cons e o es os ho _ ih =>
    intro hnc acc
    have hn : o = none := by
      have h1 : o.isSome = false := by
        rw [ho]; simp only [decide_eq_false_iff_not]; exact hnc e (List.mem_cons_self ..)
      cases o with
      | none => rfl
      | some _ => simp at h1
    subst hn
    simp only [List.zip_cons_cons, List.foldl_cons, propConfStep]
    rw [ih (fun e' he' => hnc e' (List.mem_cons_of_mem _ he'))]
    simp

theorem bk_leaderPropConf_noConf (s : NState) (ents : List EntryM) (cs : List (Option ConfChangeIM))
    (joint : Bool) (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    leaderPropConf s ents cs joint = (ents, s.pci) := by
  unfold leaderPropConf propConf
  rw [bk_propConf_noConf_fold joint _ _ ents cs hct hnc]
  simp

/-- **A proposal's step** (term `0`, no preamble), with no conf-change entry: a leader keeps
`pendingConfIndex` (`leaderPropConf … = (ents, s.pci)`); a forward or a drop changes nothing
read here. -/
theorem bk_of_stepEnd_prop {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScope c id s) (hty : m.Type' = MsgProp)
    (h0 : m.Term' = W64 0) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) (h : StepEnd c id m ents ctx s s') :
    BkStep s s' := by
  obtain ⟨hf, hc, hl⟩ := ie_fn_local (by unfold StepEndTy; se_tyclose hty)
    (by rw [hty]; se_tyclose MsgHup) (by rw [hty]; se_tyclose MsgVote) h0 h
  refine BkFn.step ?_
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    unfold FollowerStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, hres⟩ := hres
    split at hres <;> (obtain ⟨-, rfl⟩ := hres; exact BkFn.keep rfl rfl rfl)
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    unfold CandidateStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨-, -, rfl⟩ := hres
    exact BkFn.keep rfl rfl rfl
  | preCandidate => exact absurd hr hsc.2.2.1
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC at hres
    se_tysimp hty at hres
    obtain ⟨cs, hct, -, hres⟩ := hres
    rw [bk_leaderPropConf_noConf s ents cs c.joint hct hnc] at hres
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte] at hres
      obtain ⟨ms, pvs, rfl, -, -⟩ := hres
      exact BkFn.keep rfl rfl rfl
    · simp only [↓reduceIte] at hres
      rcases hres with rfl | rfl <;> exact BkFn.keep rfl rfl rfl

end pure

end EtcdGrove
end Perennial
