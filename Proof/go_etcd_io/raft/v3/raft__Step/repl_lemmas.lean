/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_repl_lemmas.v.

Pure lemmas shared by `Step`'s `MsgApp` and `MsgHeartbeat` branches
(`proof_raft__Step_MsgApp*.v`, `proof_raft__Step_MsgHeartbeat*.v`).

Proof structure, not specification: no `Module Type`, no `Parameter`, no Hoare triple.
Each lemma is about the result relations the `stepX` specs return
(`FollowerStepResult`, `CandidateStepResult`, `LeaderStepResult`) and the model rules
they refine, and is proved here, outside any WP, where the `decide` chains are cheap to
take apart. Only files in this directory may `Require` it.

Lean notes:
* Rocq's section variable `cfg` is an explicit first argument of every lemma that uses
  it.
* `toPState_sendMsgs'` is `Defs.lean`'s `toPState_sendMsgs` without the
  `GoSemanticsFunctions` binder its section adds (these lemmas have no such instance).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section repl
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

/-! ## The model side

`t` is the physical state the handler (`handleAppendEntries` / `handleHeartbeat`)
starts in, after the node has adopted `m.From` as leader: `stepFollower`'s
`r.lead = m.From`, or `stepCandidate`'s / the term preamble's
`becomeFollower(_, m.From)`. All three are `padoptLeader` of the protocol state before
the adoption; the `stepX`-specific lemmas below establish that equation. -/

/-- `Defs.lean`'s `toPState_sendMsgs`, without its `GoSemanticsFunctions` binder. -/
private theorem toPState_sendMsgs' (s : NState) (ms : List Msg) :
    toPState (sendMsgs s ms) = psendMsgs (toPState s) ms := rfl

theorem step_eq (cfg : GSet w64) (id : w64) (ps : PState) (recv : List Msg)
    (ps1 ps2 : PState) :
    Step cfg id ps recv ps1 → ps1 = ps2 → Step cfg id ps recv ps2 := by
  intro H He; subst He; exact H

/-- `HandleAppResult` refines `Step.appStale` / `Step.appAccept` / `Step.appReject` at
`ps`. -/
theorem step_handle_app (cfg : GSet w64) (id : w64) (ps : PState) (t : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (s' : NState) :
    toPState t = padoptLeader ps m.From' →
    m.To' = id →
    m.Term' = ps.term →
    ps.role ≠ .leader →
    (uint.Z ps.commit ≤ uint.Z m.Index' →
     PlogMatches ps.base ps.log (entryID.mk m.LogTerm' m.Index') →
     plogFindConflict ps.base ps.log ents = W64 0 ∨
     uint.Z ps.commit < uint.Z (plogFindConflict ps.base ps.log ents)) →
    HandleAppResult id t m ents s' →
    m.From' ≠ id →
    Step cfg id ps [absMsg .app m ents] (toPState s') := by
  intro Ht Hto Hterm Hnl Hconf Hres Hfid
  have Htm : t.term = ps.term := congrArg PState.term Ht
  have Hb : t.logst.prev = ps.base := congrArg PState.base Ht
  have Hl : t.logst.sents ++ t.logst.uents = ps.log := congrArg PState.log Ht
  have Hc : t.logst.committed = ps.commit := congrArg PState.commit Ht
  unfold HandleAppResult at Hres
  simp only [Hb, Hl] at Hres
  rw [Hc] at Hres
  rcases Hres with ⟨Hlt, rfl⟩ | ⟨Hle, lastnewi, es', ls', Happ, Hprev', Hes, -, Hcm', -, rfl⟩ |
      ⟨Hle, Hnm, hint, hintterm, rfl⟩
  · -- stale
    refine step_eq cfg id _ _ _ _
      (Step.appStale (absMsg .app m ents) ps rfl Hto Hfid Hterm Hnl Hlt) ?_
    rw [toPState_sendMsgs', Ht]
    simp only [appResp, Htm, Hc, absMsg, absMsgFrom]
  · -- accept
    have Hm : PlogMatches ps.base ps.log (entryID.mk m.LogTerm' m.Index') := by
      refine Classical.byContradiction fun Hn => ?_
      simp [plogMaybeAppend, Hn] at Happ
    refine step_eq cfg id _ _ _ _
      (Step.appAccept (absMsg .app m ents) ps lastnewi es' rfl Hto Hfid Hterm Hnl Hle Happ
        (Hconf Hle Hm)) ?_
    rw [toPState_sendMsgs']
    have Hs : toPState { t with logst := ls' } =
        { toPState t with base := ls'.prev, log := ls'.sents ++ ls'.uents,
                          commit := ls'.committed } := rfl
    rw [Hs, Ht, Hprev', Hes, Hcm']
    simp only [appResp, Htm, absMsg, absMsgFrom, padoptLeader]
    rfl
  · -- reject
    refine step_eq cfg id _ _ _ _
      (Step.appReject (absMsg .app m ents) ps hint hintterm rfl Hto Hfid Hterm Hnl Hle Hnm) ?_
    rw [toPState_sendMsgs', Ht]
    simp only [appResp, Htm, absMsg, absMsgFrom]

/-- `heartbeatResult` refines `Step.heartbeat` at `ps`. -/
theorem step_handle_heartbeat (cfg : GSet w64) (id : w64) (ps : PState) (t : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (ctx : List w8) :
    toPState t = padoptLeader ps m.From' →
    m.To' = id →
    m.Term' = ps.term →
    ps.role ≠ .leader →
    uint.Z m.Commit' ≤ plogLastIndexZ ps.base ps.log →
    m.From' ≠ id →
    Step cfg id ps [absMsg .heartbeat m ents ctx] (toPState (heartbeatResult id t m ctx)) := by
  intro Ht Hto Hterm Hnl Hcm Hfid
  have Htm : t.term = ps.term := congrArg PState.term Ht
  refine step_eq cfg id _ _ _ _
    (Step.heartbeat (absMsg .heartbeat m ents ctx) ps rfl Hto Hfid Hterm Hnl Hcm) ?_
  unfold heartbeatResult
  rw [toPState_sendMsgs']
  have Hs : toPState { t with logst := { t.logst with
        committed := plogCommitTo t.logst.committed m.Commit' } } =
      { toPState t with commit := plogCommitTo (toPState t).commit m.Commit' } := rfl
  rw [Hs, Ht]
  simp only [Htm, absMsg, absMsgFrom, padoptLeader]

/-- The term preamble's step-down for a message only a leader sends. -/
theorem step_higher_term_leader (cfg : GSet w64) (id : w64) (ps : PState) (ty : MsgType)
    (m : raftpb.Message) (ents : List raftpb.Entry) (ctx : List w8 := []) :
    fromLeader ty = true →
    uint.Z ps.term < uint.Z m.Term' →
    m.To' = id →
    m.From' ≠ id →
    Step cfg id ps [absMsg ty m ents ctx] (pbecomeFollower ps m.Term' m.From') := by
  intro Hfl Hgt Hto Hfid
  refine step_eq cfg id _ _ _ _
    (Step.higherTerm (absMsg ty m ents ctx) ps Hgt Hto (fun _ => Hfid)) ?_
  simp only [absMsg, absMsgFrom, Hfl, ↓reduceIte]

/-! ## The three adoptions are `padoptLeader` -/

/-- After the term preamble's `becomeFollower(m.Term, m.From)`, with `stepFollower`'s
`r.lead = m.From` on top (a no-op there). -/
theorem adopt_after_stepdown (s : NState) (term src : w64) (pvs : GMap w64 Progress) :
    toPState { becomeFollower s term src with prvals := pvs, lead := src }
    = padoptLeader (pbecomeFollower (toPState s) term src) src := by
  simp [toPState, padoptLeader, pbecomeFollower, becomeFollower, resetTo, resetTo0, proleRole]

/-- `stepFollower`'s `r.lead = m.From` at the current term. A follower's tally is empty
-- `padoptLeader` clears it -- which `NState` does not record by itself; it is the
premise `Hv`. -/
theorem adopt_follower (s : NState) (src : w64) :
    s.role = .follower →
    s.votes = ∅ →
    toPState { s with lead := src } = padoptLeader (toPState s) src := by
  intro Hr Hv
  simp [toPState, padoptLeader, Hr, Hv, proleRole]

/-- `stepCandidate`'s `becomeFollower(r.Term, m.From)`: the term does not move, so the
vote is kept, and the tally is cleared. -/
theorem adopt_candidate (s : NState) (src : w64) (pvs : GMap w64 Progress) :
    toPState { becomeFollower s s.term src with prvals := pvs }
    = padoptLeader (toPState s) src := by
  simp [toPState, padoptLeader, becomeFollower, resetTo, resetTo0, proleRole]

/-! ## Well-formedness is preserved by the handlers -/

theorem nstateWf_handle_app (id : w64) (t : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (s' : NState) :
    NStateWf t → HandleAppResult id t m ents s' → NStateWf s' := by
  intro Hwf Hres
  unfold HandleAppResult at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨-, _, _, _, -, -, -, -, -, -, rfl⟩ | ⟨-, -, _, _, rfl⟩ <;>
    exact Hwf

/-- `handleAppendEntries` keeps the term and `NetFrame`'s fields (2026-10-09). -/
theorem frame_handle_app (id : w64) (t : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (s' : NState) :
    HandleAppResult id t m ents s' → NetFrame t s' ∧ s'.term = t.term := by
  intro Hres
  unfold HandleAppResult at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨-, _, _, _, -, -, -, -, -, Hfr, rfl⟩ | ⟨-, -, _, _, rfl⟩
  · exact ⟨NetFrame.refl _, rfl⟩
  · obtain ⟨H1, H2, H3, H4, H5, H6⟩ := Hfr
    exact ⟨⟨H1, H2, H3, H4, H5, H6, rfl, rfl⟩, rfl⟩
  · exact ⟨NetFrame.refl _, rfl⟩

/-- A `MsgApp` branch's frame and term step: the adoption `s → t` (at most a step-down
to the message's term), then the handler. -/
theorem app_frame {id : w64} {m : raftpb.Message} {ents : List raftpb.Entry}
    {s t s' : NState} (Happ : m.Type' = MsgApp) (Hres : HandleAppResult id t m ents s')
    (Hft : NetFrame s t) (H1 : uint.Z s.term ≤ uint.Z t.term)
    (H2 : uint.Z t.term ≤ max (uint.Z s.term) (uint.Z m.Term')) :
    NetFrame s s' ∧ TermStep m s s' := by
  obtain ⟨Hf, Ht⟩ := frame_handle_app id t m ents s' Hres
  refine ⟨Hft.trans Hf, by rw [Ht]; exact H1, fun h => ?_, fun _ _ => by rw [Ht]; exact H2,
    fun h => absurd Happ h⟩
  rw [Happ] at h; exact absurd h (by w32_ne)

theorem nstateWf_heartbeatResult (id : w64) (t : NState) (m : raftpb.Message)
    (cl : List w8 := []) :
    NStateWf t → NStateWf (heartbeatResult id t m cl) := by
  intro Hwf; exact Hwf

/-! ## Taking the `stepX` results apart, by type -/

theorem followerStepResult_app (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    m.Type' = MsgApp →
    FollowerStepResult id s m ents sv dropped s' →
    dropped = false ∧ HandleAppResult id { s with lead := m.From' } m ents s' := by
  intro Hty H
  unfold FollowerStepResult at H
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem followerStepResult_heartbeat (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8) :
    m.Type' = MsgHeartbeat →
    FollowerStepResult id s m ents sv dropped s' cl →
    dropped = false ∧ s' = heartbeatResult id { s with lead := m.From' } m cl := by
  intro Hty H
  unfold FollowerStepResult at H
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem candidateStepResult_app (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgApp →
    CandidateStepResult cfg id s m ents sv dropped s' →
    dropped = false ∧
    ∃ pvs, HandleAppResult id { becomeFollower s s.term m.From' with prvals := pvs }
      m ents s' := by
  intro Hty H
  unfold CandidateStepResult at H
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem candidateStepResult_heartbeat (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) (cl : List w8) :
    m.Type' = MsgHeartbeat →
    CandidateStepResult cfg id s m ents sv dropped s' cl →
    dropped = false ∧
    ∃ pvs, s' = heartbeatResult id { becomeFollower s s.term m.From' with prvals := pvs } m cl := by
  intro Hty H
  unfold CandidateStepResult at H
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

/-- A leader ignores a `MsgApp` or `MsgHeartbeat` of its own term. -/
theorem leaderStepResult_app_hb (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (dropped : Bool) (s' : NState) :
    m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat →
    LeaderStepResult cfg id s m ents dropped s' →
    dropped = false ∧ s' = s := by
  intro Hty H
  have Hnp : m.Type' ≠ MsgProp := by rcases Hty with h | h <;> rw [h] <;> w32_ne
  unfold LeaderStepResult at H
  rw [ite_eq_right Hnp] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩
  · rfl
  all_goals exfalso; rcases Hty with h | h <;> rw [h] at Hc <;> exact absurd Hc (by w32_ne)

/-! ## Snapshots (2026-10-02)

`HandleSnapResult` at the adopted state `t` refines the three `Step.snap*` rules at
`ps`; the term preamble's step-down for a `MsgSnap` is `Step.higherTerm` at
`absSnap`. -/

theorem step_handle_snap (cfg : GSet w64) (id : w64) (ps : PState) (t : NState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters : List w64) (s' : NState) :
    toPState t = padoptLeader ps m.From' →
    m.To' = id →
    m.Term' = ps.term →
    ps.role ≠ .leader →
    m.From' ≠ id →
    SnapScope cfg sv voters →
    id ∈ cfg →
    HandleSnapResult id t m sv s' →
    Step cfg id ps [absSnap m sv voters] (toPState s') := by
  intro Ht Hto Hterm Hnl Hfid Hscope Hin Hres
  have Hperm : voters ≡ₚ elements cfg := Hscope.1
  have Htm : t.term = ps.term := congrArg PState.term Ht
  have Hb : t.logst.prev = ps.base := congrArg PState.base Ht
  have Hl : t.logst.sents ++ t.logst.uents = ps.log := congrArg PState.log Ht
  have Hc : t.logst.committed = ps.commit := congrArg PState.commit Ht
  have Hrl : t.role ≠ .leader := by
    intro h
    have := congrArg PState.role Ht
    simp [toPState, h, proleRole, padoptLeader] at this
  unfold HandleSnapResult at Hres
  rcases Hres with ⟨Hle, rfl⟩ | ⟨Hlt, Hm, rfl⟩ | ⟨Hlt, Hnm, prs, pvs, rfl⟩
  · -- obsolete
    rw [Hc] at Hle
    refine step_eq cfg id _ _ _ _
      (Step.snapStale (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hle) ?_
    rw [toPState_sendMsgs', Ht]
    simp only [appResp, Htm, Hc, absSnap, absSnapFrom]
  · -- fast-forward
    rw [Hc] at Hlt; rw [Hb, Hl] at Hm
    refine step_eq cfg id _ _ _ _
      (Step.snapFastfwd (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hperm Hin Hlt Hm) ?_
    rw [toPState_sendMsgs']
    have Hs : toPState { t with logst := { t.logst with committed := (snapId sv).index' } } =
        { toPState t with commit := (snapId sv).index' } := rfl
    rw [Hs, Ht]
    simp only [appResp, Htm, absSnap, absSnapFrom, padoptLeader, snapId]
  · -- restore
    rw [Hc] at Hlt; rw [Hb, Hl] at Hnm
    refine step_eq cfg id _ _ _ _
      (Step.snapRestore (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hperm Hin Hlt Hnm) ?_
    rw [toPState_sendMsgs']
    have Hs : toPState
        { t with progress := prs, prvals := pvs, logst := logRestore t.logst (snapId sv) } =
        { toPState t with
            base := snapId sv
            log := ([] : List raftpb.Entry)
            commit := (snapId sv).index' } := by
      simp [toPState, Hrl, logRestore]
    rw [Hs, Ht]
    simp only [appResp, Htm, absSnap, absSnapFrom, padoptLeader, snapId]

theorem step_higher_term_snap (cfg : GSet w64) (id : w64) (ps : PState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters : List w64) :
    uint.Z ps.term < uint.Z m.Term' →
    m.To' = id →
    m.From' ≠ id →
    Step cfg id ps [absSnap m sv voters] (pbecomeFollower ps m.Term' m.From') := by
  intro Hgt Hto Hfid
  refine step_eq cfg id _ _ _ _
    (Step.higherTerm (absSnap m sv voters) ps Hgt Hto (fun _ => Hfid)) ?_
  simp only [absSnap, absSnapFrom, fromLeader, ↓reduceIte]

theorem nstateWf_handle_snap (id : w64) (t : NState) (m : raftpb.Message)
    (sv : raftpb.Snapshot) (s' : NState) :
    NStateWf t → HandleSnapResult id t m sv s' → NStateWf s' := by
  intro Hwf Hres
  unfold HandleSnapResult at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, _, _, rfl⟩ <;> exact Hwf

theorem followerStepResult_snap (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    m.Type' = MsgSnap →
    FollowerStepResult id s m ents sv dropped s' →
    dropped = false ∧ HandleSnapResult id { s with lead := m.From' } m sv s' := by
  intro Hty H
  unfold FollowerStepResult at H
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem candidateStepResult_snap (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgSnap →
    CandidateStepResult cfg id s m ents sv dropped s' →
    dropped = false ∧
    ∃ pvs, HandleSnapResult id { becomeFollower s s.term m.From' with prvals := pvs }
      m sv s' := by
  intro Hty H
  unfold CandidateStepResult at H
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

end StepProof

end repl

end EtcdGrove
end Perennial
