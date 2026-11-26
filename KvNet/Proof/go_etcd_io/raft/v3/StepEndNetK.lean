-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/StepEndNetK.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Antithesis parity B1, phase 2 (#33, `notes/antithesis-parity-design.md` §4, §5), step B. **A network
message's `Step` at the node's flags**: the dispatchers over the B1 network types (`netTypesK`: the six
of `antStepTypes`, the pre-vote request and response, the read-index request and response, the transfer
request and `MsgTimeoutNow`), over `LiftScopeK` (check-quorum and pre-vote the node's `k`), from
`StepEnd`: the protocol end `RecvEnd` at the message's abstraction (`recvEnd_of_stepEnd_netK`, by
type: `InputEndLift.lean`'s `*K` arms, `recvEnd_of_stepEnd_readIndex`), the bookkeeping `BkStep`
(`bk_of_stepEnd_netK`), the log grown (`logGrow_of_stepEnd_netK`) and the in-progress boundary
(`ipEnd_of_stepEnd_netK`). The `RawNode.Step` proofs at a mode read them.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.RawNode__ReadIndexAbs
public import KvNet.Proof.go_etcd_io.raft.v3.RawNode__TransferLeaderAbs

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

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The B1 network types** a `RawNode.Step` at a mode without snapshots, forwarding or asynchronous
storage takes (`stepTypes md` at those flags off is a sublist). -/
def netTypesK : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgPreVote,
    MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp, MsgTransferLeader, MsgTimeoutNow]

theorem netTypesK_cases {t : w32} (h : t ∈ netTypesK) :
    t = MsgApp ∨ t = MsgAppResp ∨ t = MsgVote ∨ t = MsgVoteResp ∨ t = MsgHeartbeat ∨
      t = MsgHeartbeatResp ∨ t = MsgPreVote ∨ t = MsgPreVoteResp ∨ t = MsgReadIndex ∨
      t = MsgReadIndexResp ∨ t = MsgTransferLeader ∨ t = MsgTimeoutNow := by
  unfold netTypesK at h
  simpa only [List.mem_cons, List.not_mem_nil, _root_.or_false] using h

theorem antStepTypes_sub_netTypesK {t : w32} (h : t ∈ antStepTypes) : t ∈ netTypesK := by
  unfold antStepTypes at h; unfold netTypesK
  simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at h ⊢
  rcases h with e | e | e | e | e | e <;> simp [e]

/-- (antithesis parity B1) **`RawNode.Step`'s types at a mode without snapshots, forwarding or
asynchronous storage** are B1's network types. -/
theorem stepTypes_sub {md : RnMode} (hs : md.snapshots = false) (hf : md.forwarding = false)
    (ha : md.async = false) {t : w32} (h : t ∈ stepTypes md) : t ∈ netTypesK := by
  unfold stepTypes at h
  simp only [hs, hf, ha, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.not_mem_nil,
    _root_.or_false] at h
  rcases h with ((h | h) | h) | h
  · exact antStepTypes_sub_netTypesK h
  all_goals
    revert h
    split
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at h
      rcases h with rfl | rfl <;> simp [netTypesK]
    · intro h; simp at h

theorem LogGrow.of_eq {ls ls' : LogState} (h : ls' = ls) : LogGrow ls ls' :=
  LogGrow.keep (by rw [h]) (by rw [h])

/-- `BkStep` and the log kept, at a step that changes neither (up to the outbox and the ghost state). -/
theorem bkLog_keep {s s' : NState} (ha : s'.logst = s.logst) (hr : s'.role = s.role)
    (hp : s'.pci = s.pci) : BkStep s s' ∧ LogGrow s.logst s'.logst :=
  ⟨(BkFn.keep (by rw [ha]) hr hp).step, LogGrow.of_eq ha⟩

/-- Through `Step`'s preamble, from the step function's state: `BkFn` and the log kept there. -/
theorem bkLog_ofPre {s s' : NState} {m : MessageM} {pvs : GMap w64 Progress}
    (h : s'.logst = (preState s m pvs).logst ∧ BkFn (preState s m pvs) s') :
    BkStep s s' ∧ LogGrow s.logst s'.logst :=
  ⟨h.2.ofPre, LogGrow.of_eq (h.1.trans (preState_logst s m pvs))⟩

/-- The log grown from the step function's state, through the preamble (which keeps the log). -/
theorem logGrow_ofPre {s s' : NState} {m : MessageM} {pvs : GMap w64 Progress}
    (h : LogGrow (preState s m pvs).logst s'.logst) : LogGrow s.logst s'.logst := by
  rw [preState_logst] at h; exact h

/-- `bkLog_gated`'s continuation from a step function's lemma giving the log and `BkFn`. -/
theorem bkLog_of_fn {s s' t : NState} {m : MessageM} {pvs : GMap w64 Progress}
    (ht : t = preState s m pvs) (h : s'.logst = t.logst ∧ BkFn t s') :
    BkStep s s' ∧ (m.Type' ≠ MsgApp → LogGrow s.logst s'.logst) := by
  subst ht; exact ⟨(bkLog_ofPre h).1, fun _ => (bkLog_ofPre h).2⟩

end pure

section proof
-- the instances `RawNode__ReadIndexAbs`/`RawNode__TransferLeaderAbs` state their lemmas at
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

variable {k : NodeK}

/-- **A network message's protocol end** at the node's flags (`LiftScopeK`): `RecvEnd` at the message's
abstraction, by type (`InputEndLift.lean`'s `*K` arms; a forwarded `MsgReadIndex`, term `0`, at any
sender: `recvEnd_of_stepEnd_readIndex`). A stamped type's term is past `0` (`NetMsgOk`); a
pre-candidate's tally is not a quorum (`hq`, `RnScope`). The transfer types have no protocol reading
(`mtypeOf … = none`): vacuous. -/
theorem recvEnd_of_stepEnd_netK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s)
    (hq : s.role = .preCandidate → ¬ JQuorum c (granted s.votes)) (hty : m.Type' ∈ netTypesK)
    (h0 : ¬ UnstampedType m.Type' → m.Term' ≠ W64 0) (h0r : m.Type' = MsgReadIndex → m.Term' = W64 0)
    (hns : NoSnapSent (toPState s) (toPState s')) (h : StepEnd c id m ents ctx s s') :
    ∀ ty, mtypeOf m.Type' = some ty →
      RecvEnd k c id (toPState s) (absMsg ty m ents ctx) (toPState s') := by
  intro ty hty'
  rcases netTypesK_cases hty with e | e | e | e | e | e | e | e | e | e | e | e <;>
    rw [e] at hty' <;> cases hty'
  · exact recvEnd_of_stepEnd_appK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) h
  · exact recvEnd_of_stepEnd_appRespK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) hns h
  · exact recvEnd_of_stepEnd_voteK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) h
  · exact recvEnd_of_stepEnd_voteRespK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) hns h
  · exact recvEnd_of_stepEnd_heartbeatK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) h
  · exact recvEnd_of_stepEnd_heartbeatRespK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) hns h
  · exact recvEnd_of_stepEnd_preVoteK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) h
  · exact recvEnd_of_stepEnd_preVoteRespK hsc hq e (h0 (by rw [e]; nk_tyclose MsgApp)) h
  · exact (recvEnd_of_stepEnd_readIndex e (h0r e) hsc.2.2.2.2.2.2 h).1
  · exact recvEnd_of_stepEnd_readIndexRespK hsc e (h0 (by rw [e]; nk_tyclose MsgApp)) h

/-- A gated type's step (not `MsgHup`, not `MsgVote`) at the state with the transferee's
acknowledgement recorded (`StepEnd.body_xt`): stale, the state kept but the outbox; else the step
function's result `hfn` gives. -/
theorem bkLog_gated {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hT : StepEndTy m.Type') (hh : m.Type' ≠ MsgHup) (hv : m.Type' ≠ MsgVote)
    (h : StepEnd c id m ents ctx s s')
    (hfn : ∀ (Y : GMap (w64 × w64) Unit) (pvs : GMap w64 Progress),
      StepFnEnd c id (preState { s with gh := { s.gh with xt := Y } } m pvs) m ents ctx s' →
      BkStep s s' ∧ (m.Type' ≠ MsgApp → LogGrow s.logst s'.logst)) :
    BkStep s s' ∧ (m.Type' ≠ MsgApp → LogGrow s.logst s'.logst) := by
  obtain ⟨Y, hst, -, -, hf⟩ := h.body_xt hT
  by_cases hs : StaleMsg s m
  · rcases hst hs with h' | ⟨_, _, -, h'⟩ <;> subst h' <;>
      exact ⟨(bkLog_keep rfl rfl rfl).1, fun _ => (bkLog_keep rfl rfl rfl).2⟩
  · obtain ⟨pvs, H⟩ := hf hs hh hv
    exact hfn Y pvs H

set_option maxHeartbeats 1000000 in
/-- **A network message's bookkeeping and log** at the node's flags (`LiftScopeK`): `BkStep`, and but
for a `MsgApp` the log grown (`LogGrow`; kept on every B1 type). By type: the step function's
(`bk_fn_*`, `logGrow_fn_*`, at the state with the transferee's acknowledgement recorded,
`StepEnd.body_xt`); a vote or pre-vote request's answer queued; a transfer request stale
(`StepEnd.xstale`), of a higher term (`transferEnd_of_stepEnd_gt`) or kept by the preamble
(`transferEnd_of_stepEnd_cur`). -/
theorem bkLog_of_stepEnd_netK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s) (hty : m.Type' ∈ netTypesK)
    (hns : NoSnapL s'.outbox) (h : StepEnd c id m ents ctx s s') :
    BkStep s s' ∧ (m.Type' ≠ MsgApp → LogGrow s.logst s'.logst) := by
  have hpc : domSet s.progress = c.ids := hsc.2.2.2.2.2.2
  have hkeep : ∀ s1 : NState, s1.logst = s.logst → s1.role = s.role → s1.pci = s.pci →
      BkStep s s1 ∧ (m.Type' ≠ MsgApp → LogGrow s.logst s1.logst) := fun s1 ha hr hp =>
    ⟨(bkLog_keep ha hr hp).1, fun _ => (bkLog_keep ha hr hp).2⟩
  have hF : ∀ (Y : GMap (w64 × w64) Unit) (pvs : GMap w64 Progress),
      FnScope c id (preState { s with gh := { s.gh with xt := Y } } m pvs) := fun Y pvs =>
    FnScope.of_preStateK (s := { s with gh := { s.gh with xt := Y } }) hsc pvs
  have hT : ∀ t : w32, m.Type' = t → StepEndTy t → StepEndTy m.Type' := fun t e h => e ▸ h
  rcases netTypesK_cases hty with e | e | e | e | e | e | e | e | e | e | e | e
  · -- `MsgApp`
    refine bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y pvs H => ⟨(bk_fn_app (hF Y pvs) e H).ofPre, fun hn => absurd e hn⟩
  · refine bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y pvs H => ⟨(bk_fn_appResp (hF Y pvs) e H).ofPre, fun _ =>
        logGrow_ofPre (s := { s with gh := { s.gh with xt := Y } }) (logGrow_fn_appResp (hF Y pvs) e H)⟩
  · -- `MsgVote`
    obtain ⟨Y, hst, -, hv, -⟩ := h.body_xt (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp))
    by_cases hs : StaleMsg s m
    · rcases hst hs with h' | ⟨_, _, -, h'⟩ <;> subst h' <;> exact hkeep _ rfl rfl rfl
    rcases hv hs e with ⟨-, -, -, -, rfl⟩ | ⟨pvs, H⟩
    · exact hkeep _ rfl rfl rfl
    · exact ⟨(bk_vote H).ofPre, fun _ =>
        logGrow_ofPre (s := { s with gh := { s.gh with xt := Y } }) (logGrow_vote H)⟩
  · refine bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y pvs H => ⟨(bk_fn_voteResp (hF Y pvs) e H).ofPre, fun _ =>
        logGrow_ofPre (s := { s with gh := { s.gh with xt := Y } }) (logGrow_fn_voteResp (hF Y pvs) e H)⟩
  · refine bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y pvs H => ⟨(bk_fn_heartbeat (hF Y pvs) e H).ofPre, fun _ =>
        logGrow_ofPre (s := { s with gh := { s.gh with xt := Y } }) (logGrow_fn_heartbeat (hF Y pvs) e H)⟩
  · refine bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y pvs H => ⟨(bk_fn_heartbeatResp (hF Y pvs) e H).ofPre, fun _ =>
        logGrow_ofPre (s := { s with gh := { s.gh with xt := Y } }) (logGrow_fn_heartbeatResp (hF Y pvs) e H)⟩
  · -- `MsgPreVote`
    obtain ⟨hstl, hfr⟩ := h.prevote e
    by_cases hs : StaleMsg s m
    · rw [hstl hs]; exact hkeep _ rfl rfl rfl
    · rcases hfr hs with ⟨-, -, -, -, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hkeep _ rfl rfl rfl
  · exact bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y _ H => bkLog_of_fn (s := { s with gh := { s.gh with xt := Y } }) rfl (bk_fn_preVoteResp e H)
  · exact bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y _ H => bkLog_of_fn (s := { s with gh := { s.gh with xt := Y } }) rfl (bk_fn_readIndex e H)
  · exact bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y _ H => bkLog_of_fn (s := { s with gh := { s.gh with xt := Y } }) rfl (bk_fn_readIndexResp e H)
  · -- `MsgTransferLeader`
    by_cases hst : StaleMsg s m
    · obtain ⟨X, Y, b, rfl⟩ := h.xstale hst e
      exact hkeep _ rfl rfl rfl
    by_cases hb : PreBF m s
    · obtain ⟨g, pvs, rfl⟩ := transferEnd_of_stepEnd_gt e hst hb h
      exact ⟨(BkFn.nl (t := s) (by simp [becomeFollower, resetTo, resetTo0])
          (by simp [becomeFollower, resetTo, resetTo0])).step,
        fun _ => LogGrow.of_eq (by simp [becomeFollower, resetTo, resetTo0])⟩
    · obtain ⟨g, l, o, pvs, rfl, -, -⟩ := transferEnd_of_stepEnd_cur e hst hb hpc hns h
      exact hkeep _ rfl rfl rfl
  · exact bkLog_gated (hT _ e (by unfold StepEndTy; nk_tyclose MsgApp)) (by rw [e]; nk_tyclose MsgHup)
      (by rw [e]; nk_tyclose MsgVote) h fun Y _ H => bkLog_of_fn (s := { s with gh := { s.gh with xt := Y } }) rfl (bk_fn_timeoutNow e H)

/-- **The in-progress boundary after a network message's `Step`** at the node's flags: as
`ipEnd_of_stepEnd`, a `MsgApp` by `maybeAppendIp_lcp`, the other types by `LogGrow`
(`bkLog_of_stepEnd_netK`). -/
theorem ipEnd_of_stepEnd_netK {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s s' : NState} (hsc : LiftScopeK k c id s) (hty : m.Type' ∈ netTypesK)
    (hns : NoSnapL s'.outbox)
    (hwf : m.Type' = MsgApp → PlogWf (entryID.mk m.LogTerm' m.Index') ents)
    (hp : uint.Z s.logst.prev.index' = 0) (hlo : 1 ≤ uint.Z s.logst.inprogress)
    (hhi : uint.Z s.logst.inprogress ≤ ((s.logst.sents ++ s.logst.uents).length : Int) + 1)
    (h : StepEnd c id m ents ctx s s') :
    uint.nat s'.logst.inprogress - 1 =
      min (uint.nat s.logst.inprogress - 1)
        (lcpLen (s.logst.sents ++ s.logst.uents) (s'.logst.sents ++ s'.logst.uents)) := by
  by_cases e : m.Type' = MsgApp
  · have hT : StepEndTy m.Type' := by unfold StepEndTy; rw [e]; nk_tyclose MsgApp
    obtain ⟨hst, -, -, hfn⟩ := h hT (XtRec.of_ne (by rw [e]; nk_tyclose MsgApp))
    by_cases hs : StaleMsg s m
    · exact ip_of_logGrow (LogGrow.of_eq (logst_of_stale (hst hs))) hhi
    obtain ⟨pvs, H⟩ := hfn hs (by rw [e]; nk_tyclose MsgHup) (by rw [e]; nk_tyclose MsgVote)
    have hl0 := preState_logst s m pvs
    rcases app_fn_logst (FnScope.of_preStateK hsc pvs) e H with he | ⟨lni, es', Hma, Hes, Hip⟩
    · exact ip_of_logGrow (LogGrow.of_eq (he.trans hl0)) hhi
    · rw [hl0] at Hma Hip
      rw [Hes, Hip]
      exact maybeAppendIp_lcp Hma hp (hwf e) hlo hhi
  · exact ip_of_logGrow ((bkLog_of_stepEnd_netK hsc hty hns h).2 e) hhi

/-- (antithesis parity B1, phase 2) **A received `MsgTimeoutNow`'s `RState` end** (`x` its transfer
reading): `TimeoutNowEndR`, from `timeoutNowEnd_of_stepEnd` (the protocol part; stale: `Step` keeps the
state) and the bookkeeping (`bkLog_of_stepEnd_netK`, `pciR_of_bk`). -/
theorem timeoutNowEndR_of_stepEnd {rs rs' : RNState} {fp : List EntryM} {c : CfgM} {id : w64}
    {m : MessageM} {ents : List EntryM} {ctx : List w8} {s s' : NState} {x : XMsg}
    (hsc : LiftScopeK k c id s) (hc : rs.cfg.cfg = c) (hty : m.Type' = MsgTimeoutNow)
    (h0 : m.Term' ≠ W64 0) (hxt : x.term = m.Term') (hns : NoSnapL s'.outbox)
    (hsn : s'.logst.snap = s.logst.snap) (hcf : rs'.capplied = rs.capplied ∧ rs'.cfg = rs.cfg)
    (h : StepEnd c id m ents ctx s s') :
    TimeoutNowEndR id (toRState rs fp s) x (toRState rs' fp s') := by
  have hbk := (bkLog_of_stepEnd_netK hsc (by rw [hty]; unfold netTypesK; simp) hns h).1
  rcases timeoutNowEnd_of_stepEnd hsc hty h0 (noSnapSent_of_noSnapL hns) h with ⟨hlt, -⟩ |
      ⟨hle, p1, hp1, hr⟩
  · refine .inl ⟨by rw [hxt]; exact hlt, ?_⟩
    have hst : StaleMsg s m := ⟨h0, hlt⟩
    obtain ⟨hs, -⟩ := h (by unfold StepEndTy; rw [hty]; nk_tyclose MsgApp)
      (XtRec.of_ne (by rw [hty]; nk_tyclose MsgApp))
    rcases hs hst with rfl | ⟨_, _, hlow, -⟩
    · simp only [toRState, hcf.1, hcf.2]
    · exfalso
      rcases hlow with ⟨-, -, hha, -⟩ | ⟨-, hp, -⟩
      · rcases hha with e | e <;> rw [hty] at e <;> exact absurd e (by nk_tyclose MsgApp)
      · rw [hty] at hp; exact absurd hp (by nk_tyclose MsgApp)
  · refine .inr ⟨by rw [hxt]; exact hle, ⟨p1, by rw [hxt]; exact hp1, ?_⟩, ⟨hbk.1, hcf.1, hcf.2⟩, rfl,
      by simp only [toRState_snap, hsn], pciR_of_bk hbk⟩
    show toPState s' = p1 ∨ (p1.role = .leader ∧ SendsEnd rs.cfg.cfg id p1 (toPState s')) ∨
      (p1.role = .follower ∧ CampaignEnd rs.cfg.cfg id p1 ctxTransfer (toPState s'))
    rw [hc]; exact hr

end proof

end EtcdGrove
end Perennial
