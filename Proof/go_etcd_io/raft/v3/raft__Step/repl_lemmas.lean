/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_repl_lemmas.v.

Pure lemmas shared by `Step`'s `MsgApp` and `MsgHeartbeat` branches
(`proof_raft__Step_MsgApp*.v`, `proof_raft__Step_MsgHeartbeat*.v`).

Proof structure, not specification: no `Module Type`, no `Parameter`, no Hoare triple.
Each lemma is about the result relations the `stepX` specs return
(`FollowerStepResult`, `CandidateStepResult`, `LeaderStepResult`) and the model rules
they refine, and is proved here, outside any WP, where the `decide` chains are cheap to
take apart. Only files in this directory may `Require` it.

Lean notes:
* Rocq's section variable `c` is an explicit first argument of every lemma that uses
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

theorem stepCF_eq (c : CfgM) (id : w64) (ps : PState) (recv : List Msg)
    (ps1 ps2 : PState) :
    StepCF c id ps recv ps1 → ps1 = ps2 → StepCF c id ps recv ps2 := by
  intro H He; subst He; exact H

theorem step_eq (c : CfgM) (id : w64) (ps : PState) (recv : List Msg)
    (ps1 ps2 : PState) :
    StepC c id ps recv ps1 → ps1 = ps2 → StepC c id ps recv ps2 := by
  intro H He; subst He; exact H

/-- `HandleAppResult` refines `StepC.appStale` / `StepC.appAccept` / `StepC.appReject` at
`ps`. -/
theorem step_handle_app (c : CfgM) (id : w64) (ps : PState) (t : NState)
    (m : MessageM) (ents : List EntryM) (s' : NState) :
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
    StepCF c id ps [absMsg .app m ents] (toPState s') := by
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
    refine stepCF_eq c id _ _ _ _
      (StepCF.appStale (absMsg .app m ents) ps rfl Hto Hfid Hterm Hnl Hlt) ?_
    rw [toPState_sendMsgs', Ht]
    simp only [appResp, Htm, absMsg, absMsgFrom]
  · -- accept
    have Hm : PlogMatches ps.base ps.log (entryID.mk m.LogTerm' m.Index') := by
      refine Classical.byContradiction fun Hn => ?_
      simp [plogMaybeAppend, Hn] at Happ
    refine stepCF_eq c id _ _ _ _
      (StepCF.appAccept (absMsg .app m ents) ps lastnewi es' rfl Hto Hfid Hterm Hnl Hle Happ
        (Hconf Hle Hm)) ?_
    rw [toPState_sendMsgs']
    -- (raft#140) `logSynced` is invisible to the protocol
    have Hs : toPState { t with logst := ls', logSynced := true } =
        { toPState t with base := ls'.prev, log := ls'.sents ++ ls'.uents,
                          commit := ls'.committed } := rfl
    rw [Hs, Ht, Hprev', Hes, Hcm']
    simp only [appResp, Htm, absMsg, absMsgFrom, padoptLeader]
    rfl
  · -- reject
    refine stepCF_eq c id _ _ _ _
      (StepCF.appReject (absMsg .app m ents) ps hint hintterm rfl Hto Hfid Hterm Hnl Hle Hnm) ?_
    rw [toPState_sendMsgs', Ht]
    simp only [appResp, Htm, absMsg, absMsgFrom]

/-- `heartbeatResult` refines `StepC.heartbeat` at `ps` (raft#140): at `cm = min(m.Commit,
lastIndex())` when `logSynced`, at `cm = 0` (no commit) otherwise. -/
theorem step_handle_heartbeat (c : CfgM) (id : w64) (ps : PState) (t : NState)
    (m : MessageM) (ents : List EntryM) (ctx : List w8) :
    toPState t = padoptLeader ps m.From' →
    m.To' = id →
    m.Term' = ps.term →
    ps.role ≠ .leader →
    m.From' ≠ id →
    StepCF c id ps [absMsg .heartbeat m ents ctx] (toPState (heartbeatResult id t m ctx)) := by
  intro Ht Hto Hterm Hnl Hfid
  have Htm : t.term = ps.term := congrArg PState.term Ht
  have Hb : t.logst.prev = ps.base := congrArg PState.base Ht
  have Hl : t.logst.sents ++ t.logst.uents = ps.log := congrArg PState.log Ht
  let cm : w64 := if t.logSynced then w64Min m.Commit' (logLast t.logst) else W64 0
  have Hmin := w64Min_spec m.Commit' (logLast t.logst)
  have Hlast := logLast_le_Z t.logst
  have Hcm1 : uint.Z cm ≤ uint.Z m.Commit' := by
    simp only [cm]; split
    · omega
    · have := uint_Z_nonneg m.Commit'; simp only [show uint.Z (W64 0) = 0 from rfl]; omega
  have Hcm2 : uint.Z cm ≤ plogLastIndexZ ps.base ps.log := by
    rw [← Hb, ← Hl]; unfold plogLastIndexZ; rw [List.length_append]; push_cast
    simp only [cm]; split
    · omega
    · have := uint_Z_nonneg t.logst.prev.index'; simp only [show uint.Z (W64 0) = 0 from rfl]; omega
  refine stepCF_eq c id _ _ _ _
    (StepCF.heartbeat (absMsg .heartbeat m ents ctx) ps cm rfl Hto Hfid Hterm Hnl Hcm1 Hcm2) ?_
  unfold heartbeatResult
  rw [toPState_sendMsgs']
  have Hs : toPState { t with logst := { t.logst with
        committed := if t.logSynced then plogCommitTo t.logst.committed
          (w64Min m.Commit' (logLast t.logst)) else t.logst.committed } } =
      { toPState t with commit := plogCommitTo (toPState t).commit cm } := by
    simp only [cm]
    split
    · rfl
    · have H0 : plogCommitTo t.logst.committed (W64 0) = t.logst.committed := by
        unfold plogCommitTo
        rw [if_neg (by have := uint_Z_nonneg t.logst.committed; simp only [show uint.Z (W64 0) = 0 from rfl]; omega)]
      show toPState { t with logst := { t.logst with committed := t.logst.committed } } =
        { toPState t with commit := plogCommitTo t.logst.committed (W64 0) }
      rw [H0]; rfl
  rw [Hs, Ht]
  simp only [Htm, absMsg, absMsgFrom, padoptLeader]

/-- The term preamble's step-down for a message only a leader sends. -/
theorem step_higher_term_leader (c : CfgM) (id : w64) (ps : PState) (ty : MsgType)
    (m : MessageM) (ents : List EntryM) (ctx : List w8 := []) :
    fromLeader ty = true →
    uint.Z ps.term < uint.Z m.Term' →
    m.To' = id →
    m.From' ≠ id →
    StepCF c id ps [absMsg ty m ents ctx] (pbecomeFollower ps m.Term' m.From') := by
  intro Hfl Hgt Hto Hfid
  refine stepCF_eq c id _ _ _ _
    (StepCF.higherTerm (absMsg ty m ents ctx) ps Hgt Hto (fun _ => Hfid)) ?_
  simp only [absMsg, absMsgFrom, Hfl, ↓reduceIte]

/-! ## The three adoptions are `padoptLeader` -/

/-- After the term preamble's `becomeFollower(m.Term, m.From)`, with `stepFollower`'s
`r.lead = m.From` on top (a no-op there). -/
theorem adopt_after_stepdown (s : NState) (term src : w64) (pvs : GMap w64 Progress) :
    toPState { becomeFollower s term src with prvals := pvs, lead := src }
    = padoptLeader (pbecomeFollower (toPState s) term src) src := by
  simp only [pbecomeFollower, padoptLeader, rdNL_toPState]
  simp [toPState, becomeFollower, resetTo, resetTo0, proleRole, rdNL]

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
theorem adopt_candidate (s : NState) (src : w64) (pvs : GMap w64 Progress)
    (Hnl : s.role ≠ .leader) :
    toPState { becomeFollower s s.term src with prvals := pvs }
    = padoptLeader (toPState s) src := by
  simp [toPState, padoptLeader, becomeFollower, resetTo, resetTo0, proleRole, rdNL, Hnl]

/-! ## Well-formedness is preserved by the handlers -/

theorem nstateWf_handle_app (id : w64) (t : NState) (m : MessageM)
    (ents : List EntryM) (s' : NState) :
    NStateWf t → HandleAppResult id t m ents s' → NStateWf s' := by
  intro Hwf Hres
  unfold HandleAppResult at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨-, _, _, _, -, -, -, -, -, -, rfl⟩ | ⟨-, -, _, _, rfl⟩ <;>
    exact Hwf

/-- `handleAppendEntries` keeps the term and `NetFrame`'s fields (2026-10-09). -/
theorem frame_handle_app (id : w64) (t : NState) (m : MessageM)
    (ents : List EntryM) (s' : NState) :
    HandleAppResult id t m ents s' → NetFrame t s' ∧ s'.term = t.term := by
  intro Hres
  unfold HandleAppResult at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨-, _, _, _, -, -, -, -, -, Hfr, rfl⟩ | ⟨-, -, _, _, rfl⟩
  · exact ⟨NetFrame.refl _, rfl⟩
  · obtain ⟨H1, H2, H3, H4, H5, H6⟩ := Hfr
    exact ⟨⟨H1, H2, H3, H4, H5, H6, rfl, rfl⟩, rfl⟩
  · exact ⟨NetFrame.refl _, rfl⟩

/-- `handleAppendEntries` keeps what `rOf` reads beyond `toPState` (stage B7). -/
theorem rframe_handle_app (id : w64) (t : NState) (m : MessageM)
    (ents : List EntryM) (s' : NState) (H : HandleAppResult id t m ents s') :
    RFrame t s' := by
  unfold HandleAppResult at H
  rcases H with ⟨-, rfl⟩ | ⟨-, _, _, ls', -, -, -, Ha, -, Hfr, rfl⟩ | ⟨-, -, _, _, rfl⟩
  · exact ⟨rfl, rfl, fun h => ⟨h, rfl⟩⟩
  · exact ⟨Ha, Hfr.2.1, fun h => ⟨h, rfl⟩⟩
  · exact ⟨rfl, rfl, fun h => ⟨h, rfl⟩⟩

/-- A `MsgApp` branch's frame and term step: the adoption `s → t` (at most a step-down
to the message's term), then the handler. -/
theorem app_frame {id : w64} {m : MessageM} {ents : List EntryM}
    {s t s' : NState} (Happ : m.Type' = MsgApp) (Hres : HandleAppResult id t m ents s')
    (Hft : NetFrame s t) (H1 : uint.Z s.term ≤ uint.Z t.term)
    (H2 : uint.Z t.term ≤ max (uint.Z s.term) (uint.Z m.Term')) :
    NetFrame s s' ∧ TermStep m s s' := by
  obtain ⟨Hf, Ht⟩ := frame_handle_app id t m ents s' Hres
  refine ⟨Hft.trans Hf, by rw [Ht]; exact H1, fun h => ?_, fun _ _ _ => by rw [Ht]; exact H2,
    fun h => absurd Happ h, fun h => ?_⟩
  · rw [Happ] at h; exact absurd h (by w32_ne)
  · rw [Happ] at h; exact absurd h (by w32_ne)

theorem nstateWf_heartbeatResult (id : w64) (t : NState) (m : MessageM)
    (cl : List w8 := []) :
    NStateWf t → NStateWf (heartbeatResult id t m cl) := by
  intro Hwf; exact Hwf

/-! ## Taking the `stepX` results apart, by type -/

theorem followerStepResult_app (c : CfgM) {scfg : CSLists} {c' : CfgM} {cl : List w8} (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sv : SnapshotM) (dropped : Bool) (s' : NState) :
    m.Type' = MsgApp →
    FollowerStepResultC c scfg id s m ents sv dropped s' c' cl →
    c = c' ∧ dropped = false ∧ HandleAppResult id { s with lead := m.From' } m ents s' := by
  intro Hty H
  unfold FollowerStepResultC at H
  refine ⟨(FollowerStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem followerStepResult_heartbeat (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sv : SnapshotM) (dropped : Bool) (s' : NState)
    (cl : List w8) :
    m.Type' = MsgHeartbeat →
    FollowerStepResultC c scfg id s m ents sv dropped s' c' cl →
    c = c' ∧ dropped = false ∧ s' = heartbeatResult id { s with lead := m.From' } m cl := by
  intro Hty H
  unfold FollowerStepResultC at H
  refine ⟨(FollowerStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem candidateStepResult_app (c : CfgM) {scfg : CSLists} {c' : CfgM} {cl : List w8} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (sv : SnapshotM) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgApp →
    CandidateStepResultC c scfg id s m ents sv dropped s' c' cl →
    c = c' ∧ dropped = false ∧
    ∃ pvs, HandleAppResult id { becomeFollower s s.term m.From' with prvals := pvs }
      m ents s' := by
  intro Hty H
  unfold CandidateStepResultC at H
  refine ⟨(CandidateStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem candidateStepResult_heartbeat (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (sv : SnapshotM) (dropped : Bool)
    (s' : NState) (cl : List w8) :
    m.Type' = MsgHeartbeat →
    CandidateStepResultC c scfg id s m ents sv dropped s' c' cl →
    c = c' ∧ dropped = false ∧
    ∃ pvs, s' = heartbeatResult id { becomeFollower s s.term m.From' with prvals := pvs } m cl := by
  intro Hty H
  unfold CandidateStepResultC at H
  refine ⟨(CandidateStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

/-- A leader ignores a `MsgApp` or `MsgHeartbeat` of its own term. -/
theorem leaderStepResult_app_hb (c : CfgM) {ctx : List w8} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (dropped : Bool) (s' : NState) :
    m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat →
    LeaderStepResultC c id s m ents dropped s' ctx →
    dropped = false ∧ s' = s := by
  intro Hty H
  have Hnp : m.Type' ≠ MsgProp := by rcases Hty with h | h <;> rw [h] <;> w32_ne
  unfold LeaderStepResultC at H
  rw [ite_eq_right Hnp] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResultC at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩
  rotate_right
  · exfalso
    rcases Hty with h' | h' <;> rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;>
      rw [h'] at h6 <;> exact absurd h6 (by w32_ne)
  · rfl
  all_goals exfalso; rcases Hty with h | h <;> rw [h] at Hc <;> exact absurd Hc (by w32_ne)

/-! ## Snapshots (2026-10-02)

`HandleSnapResult` at the adopted state `t` refines the three `Step.snap*` rules at
`ps`; the term preamble's step-down for a `MsgSnap` is `StepC.higherTerm` at
`absSnap`. -/

theorem step_handle_snap (c : CfgM) (id : w64) (ps : PState) (t : NState)
    (m : MessageM) (sv : SnapshotM) (voters : CSLists) (s' : NState) :
    toPState t = padoptLeader ps m.From' →
    m.To' = id →
    m.Term' = ps.term →
    ps.role ≠ .leader →
    m.From' ≠ id →
    HandleSnapResult id t m sv voters s' →
    StepC c id ps [absSnap m sv voters] (toPState s') := by
  intro Ht Hto Hterm Hnl Hfid Hres
  have Htm : t.term = ps.term := congrArg PState.term Ht
  have Hb : t.logst.prev = ps.base := congrArg PState.base Ht
  have Hl : t.logst.sents ++ t.logst.uents = ps.log := congrArg PState.log Ht
  have Hc : t.logst.committed = ps.commit := congrArg PState.commit Ht
  have Hrl : t.role ≠ .leader := by
    intro h
    have := congrArg PState.role Ht
    simp [toPState, h, proleRole, padoptLeader] at this
  unfold HandleSnapResult at Hres
  rcases Hres with ⟨Hle, rfl⟩ | ⟨Hlt, Hm, rfl⟩ | ⟨Hlt, Hnm, prs, pvs, il, rfl⟩
  · -- obsolete
    rw [Hc] at Hle
    refine step_eq c id _ _ _ _
      (StepC.snapStale (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hle) ?_
    rw [toPState_sendMsgs', Ht]
    simp only [appResp, Htm, Hc, absSnap, absSnapFrom]
  · -- fast-forward
    rw [Hc] at Hlt; rw [Hb, Hl] at Hm
    refine step_eq c id _ _ _ _
      (StepC.snapFastfwd (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hlt Hm) ?_
    rw [toPState_sendMsgs']
    have Hs : toPState { t with logst := { t.logst with committed := (snapId sv).index' } } =
        { toPState t with commit := (snapId sv).index' } := rfl
    rw [Hs, Ht]
    simp only [appResp, Htm, absSnap, absSnapFrom, padoptLeader, snapId]
  · -- restore
    rw [Hc] at Hlt; rw [Hb, Hl] at Hnm
    refine step_eq c id _ _ _ _
      (StepC.snapRestore (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hlt Hnm) ?_
    rw [toPState_sendMsgs']
    have Hs : toPState
        { t with progress := prs, prvals := pvs, logst := logRestore t.logst (snapTrip sv voters),
                 isLearner := il } =
        { toPState t with
            base := snapId sv
            log := ([] : List EntryM)
            commit := (snapId sv).index' } := by
      simp [toPState, Hrl, logRestore, snapTrip]
    rw [Hs, Ht]
    simp only [appResp, Htm, absSnap, absSnapFrom, padoptLeader, snapId]

theorem step_higher_term_snap (c : CfgM) (id : w64) (ps : PState)
    (m : MessageM) (sv : SnapshotM) (voters : CSLists) :
    uint.Z ps.term < uint.Z m.Term' →
    m.To' = id →
    m.From' ≠ id →
    StepC c id ps [absSnap m sv voters] (pbecomeFollower ps m.Term' m.From') := by
  intro Hgt Hto Hfid
  refine step_eq c id _ _ _ _
    (StepC.higherTerm (absSnap m sv voters) ps Hgt Hto (fun _ => Hfid)) ?_
  simp only [absSnap, absSnapFrom, fromLeader, ↓reduceIte]

/-- `step_handle_snap`'s two exits that keep the configuration, as `StepCF` steps. -/
theorem stepCF_handle_snap_keep (c : CfgM) (id : w64) (ps : PState) (t : NState)
    (m : MessageM) (sv : SnapshotM) (voters : CSLists) (s' : NState) :
    toPState t = padoptLeader ps m.From' →
    m.To' = id →
    m.Term' = ps.term →
    ps.role ≠ .leader →
    m.From' ≠ id →
    HandleSnapResult id t m sv voters s' →
    ¬ SnapRestores t sv →
    StepCF c id ps [absSnap m sv voters] (toPState s') := by
  intro Ht Hto Hterm Hnl Hfid Hres Hnr
  have Htm : t.term = ps.term := congrArg PState.term Ht
  have Hb : t.logst.prev = ps.base := congrArg PState.base Ht
  have Hl : t.logst.sents ++ t.logst.uents = ps.log := congrArg PState.log Ht
  have Hc : t.logst.committed = ps.commit := congrArg PState.commit Ht
  unfold HandleSnapResult at Hres
  rcases Hres with ⟨Hle, rfl⟩ | ⟨Hlt, Hm, rfl⟩ | ⟨Hlt, Hnm, -⟩
  · -- obsolete
    rw [Hc] at Hle
    refine stepCF_eq c id _ _ _ _
      (StepCF.snapStale (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hle) ?_
    rw [toPState_sendMsgs', Ht]
    simp only [appResp, Htm, Hc, absSnap, absSnapFrom]
  · -- fast-forward
    rw [Hc] at Hlt; rw [Hb, Hl] at Hm
    refine stepCF_eq c id _ _ _ _
      (StepCF.snapFastfwd (absSnap m sv voters) ps rfl Hto Hfid Hterm Hnl Hlt Hm) ?_
    rw [toPState_sendMsgs']
    have Hs : toPState { t with logst := { t.logst with committed := (snapId sv).index' } } =
        { toPState t with commit := (snapId sv).index' } := rfl
    rw [Hs, Ht]
    simp only [appResp, Htm, absSnap, absSnapFrom, padoptLeader, snapId]
  · exact absurd ⟨Hlt, Hnm⟩ Hnr

section snapCDS
variable [GoGlobalContext] [GoSemanticsFunctions]

/-- `handleSnapshot`'s three exits as a `StepCDS` step (2026-10-14, reconfiguration stage B8):
the obsolete and fast-forward exits are frame steps at `c`; a restore is `StepR.snapRestore`,
the node at the configuration `cn` the `ConfState` denotes. `t` is the state `handleSnapshot`
ran on: the sender adopted as leader (`padoptLeader`), the log untouched. -/
theorem stepCDS_handle_snap (c cn c' : CfgM) (id : w64) (s t : NState) (m : MessageM)
    (sv : SnapshotM) (voters : CSLists) (s' : NState) :
    toPState t = padoptLeader (toPState s) m.From' →
    t.logst = s.logst →
    s.role ≠ .leader →
    t.role = .follower →
    m.To' = id →
    m.Term' = (toPState s).term →
    m.From' ≠ id →
    HandleSnapResult id t m sv voters s' →
    ((SnapRestores s sv ∧ c' = cn) ∨ (¬ SnapRestores s sv ∧ c' = c)) →
    StepCDS c c' cn id (snapId sv) s [absSnap m sv voters] s' := by
  intro Ht Htl Hnls Htr Hto Hterm Hfid Hres Hc'
  have Hst : SnapRestores t sv ↔ SnapRestores s sv := by unfold SnapRestores; rw [Htl]
  rw [← Hst] at Hc'
  have Hnl : (toPState s).role ≠ .leader := by
    rw [toPState_role]; exact proleRole_not_leader _ Hnls
  by_cases Hr : SnapRestores t sv
  · -- a restore: `StepR.snapRestore`
    have Hcn : c' = cn := by
      rcases Hc' with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd Hr h
    subst Hcn
    have Hstep := step_handle_snap c id _ _ m sv voters s' Ht Hto Hterm Hnl Hfid Hres
    refine ⟨Hstep, fun Adm dec g fp' cs' _ hfp hcs hid hA => ?_⟩
    have Htm : t.term = (toPState s).term := congrArg PState.term Ht
    have Hb : t.logst.prev = (toPState s).base := congrArg PState.base Ht
    have Hl : t.logst.sents ++ t.logst.uents = (toPState s).log := congrArg PState.log Ht
    have Hc : t.logst.committed = (toPState s).commit := congrArg PState.commit Ht
    have Hrl : t.role ≠ .leader := by rw [Htr]; decide
    unfold HandleSnapResult at Hres
    rcases Hres with ⟨Hle, -⟩ | ⟨Hlt, Hm, -⟩ | ⟨Hlt, Hnm, prs, pvs, il, rfl⟩
    · exact absurd Hr.1 (Int.not_lt.2 Hle)
    · exact absurd Hm Hr.2
    refine ⟨⟨uint.nat (snapId sv).index', cs', fp'⟩, hcs, ?_⟩
    rw [Hc] at Hlt; rw [Hb, Hl] at Hnm
    have Hp : toPState (sendMsgs { t with progress := prs, prvals := pvs, logst := logRestore t.logst (snapTrip sv voters), isLearner := il }
        [appResp id t m.From' false (snapId sv).index' (W64 0) (W64 0)]) =
        psendMsgs
          { padoptLeader (toPState s) (absSnap m sv voters).src with
              base := entryID.mk (absSnap m sv voters).logterm (absSnap m sv voters).index,
              log := [], commit := (absSnap m sv voters).index }
          [Msg.mk .appResp id (absSnap m sv voters).src (toPState s).term false
            (absSnap m sv voters).index (W64 0) (W64 0) (W64 0) []] := by
      rw [toPState_sendMsgs']
      have Hs : toPState
          { t with progress := prs, prvals := pvs, logst := logRestore t.logst (snapTrip sv voters),
                   isLearner := il } =
          { toPState t with
              base := snapId sv
              log := ([] : List EntryM)
              commit := (snapId sv).index' } := by
        simp [toPState, Hrl, logRestore, snapTrip]
      rw [Hs, Ht]
      simp only [appResp, Htm, absSnap, absSnapFrom, padoptLeader, snapId]
    exact stepR_snap_restore s _ g (absSnap m sv voters) fp' cs' rfl Hto Hfid Hterm Hnls Hlt Hnm
      hfp (by rw [hcs]; exact hid) hA Hp
      (by simp [sendMsgs, logRestore, Htl]) (by simp [sendMsgs, logRestore])
      (by simp [sendMsgs, Htr])
  · -- no restore: a frame step at `c`
    have Hcc : c' = c := by
      rcases Hc' with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h Hr
      · exact h
    subst Hcc
    refine StepCDS.frame (stepCF_handle_snap_keep c' id _ _ m sv voters s' Ht Hto Hterm Hnl Hfid
      Hres Hr) ?_
    unfold HandleSnapResult at Hres
    rcases Hres with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨Hlt, Hnm, -⟩
    · exact ⟨by simp [sendMsgs, Htl], by simp [sendMsgs, Htl],
        fun h => absurd h (by simp [sendMsgs, Htr])⟩
    · exact ⟨by simp [sendMsgs, Htl], by simp [sendMsgs, Htl],
        fun h => absurd h (by simp [sendMsgs, Htr])⟩
    · exact absurd ⟨Hlt, Hnm⟩ Hr

end snapCDS

/-- `step_higher_term_snap` as a `StepCF` step (2026-10-14, stage B8). -/
theorem stepCF_higher_term_snap (c : CfgM) (id : w64) (ps : PState)
    (m : MessageM) (sv : SnapshotM) (voters : CSLists) :
    uint.Z ps.term < uint.Z m.Term' →
    m.To' = id →
    m.From' ≠ id →
    StepCF c id ps [absSnap m sv voters] (pbecomeFollower ps m.Term' m.From') := by
  intro Hgt Hto Hfid
  refine stepCF_eq c id _ _ _ _
    (StepCF.higherTerm (absSnap m sv voters) ps Hgt Hto (fun _ => Hfid)) ?_
  simp only [absSnap, absSnapFrom, fromLeader, ↓reduceIte]

/-- The configuration after `handleSnapshot`: the old one or the snapshot's. -/
theorem snapCfgOk_cases {c : CfgM} {s : NState} {sv : SnapshotM} {scfg : CSLists}
    {c' : CfgM} (h : SnapCfgOk c s sv scfg c') : c' = c ∨ c' = snapCfg sv scfg := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact .inr h
  · exact .inl h

theorem nstateWf_handle_snap (id : w64) (t : NState) (m : MessageM)
    (sv : SnapshotM) (s' : NState) {voters : CSLists} :
    NStateWf t → HandleSnapResult id t m sv voters s' → NStateWf s' := by
  intro Hwf Hres
  unfold HandleSnapResult at Hres
  rcases Hres with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, _, _, _, rfl⟩ <;> exact Hwf

theorem followerStepResult_snap (c : CfgM) {scfg : CSLists} {c' : CfgM} {cl : List w8} (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sv : SnapshotM) (dropped : Bool) (s' : NState) :
    m.Type' = MsgSnap →
    FollowerStepResultC c scfg id s m ents sv dropped s' c' cl →
    SnapCfgOk c s sv scfg c' ∧
    dropped = false ∧ HandleSnapResult id { s with lead := m.From' } m sv scfg s' := by
  intro Hty H
  refine ⟨?_, ?_⟩
  · have h1 := H.1
    rw [ite_eq_left Hty] at h1
    exact h1
  unfold FollowerStepResultC at H
  replace H := H.2
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

theorem candidateStepResult_snap (c : CfgM) {scfg : CSLists} {c' : CfgM} {cl : List w8} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (sv : SnapshotM) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgSnap →
    CandidateStepResultC c scfg id s m ents sv dropped s' c' cl →
    SnapCfgOk c s sv scfg c' ∧
    dropped = false ∧
    ∃ pvs, HandleSnapResult id { becomeFollower s s.term m.From' with prvals := pvs }
      m sv scfg s' := by
  intro Hty H
  refine ⟨?_, ?_⟩
  · have h1 := H.1
    rw [ite_eq_left Hty] at h1
    exact h1
  unfold CandidateStepResultC at H
  replace H := H.2
  simpa [Hty, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, W32] using H

end StepProof

end repl

end EtcdGrove
end Perennial
