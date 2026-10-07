/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_repl_lemmas.v.

Pure lemmas shared by `Step`'s `MsgApp` and `MsgHeartbeat` branches
(`proof_raft__Step_MsgApp*.v`, `proof_raft__Step_MsgHeartbeat*.v`).

Proof structure, not specification: no `Module Type`, no `Parameter`, no Hoare triple.
Each lemma is about the result relations the `stepX` specs return
(`FollowerStepResult`, `CandidateStepResult`, `LeaderStepResult`) and the model rules
they refine, and is proved here, outside any WP, where the `decide` chains are cheap to
take apart. Only files in this directory may `Require` it.

Lean notes: Rocq's section variable `cfg` is an explicit first argument of every lemma
that uses it.
-/
import EtcdGrove.Raft.ElectionProof.Proof.raft__Step.Base

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section repl
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

namespace StepProof

/-! ## The model side

`t` is the physical state the handler (`handleAppendEntries` / `handleHeartbeat`)
starts in, after the node has adopted `m.From` as leader: `stepFollower`'s
`r.lead = m.From`, or `stepCandidate`'s / the term preamble's
`becomeFollower(_, m.From)`. All three are `padoptLeader` of the protocol state before
the adoption; the `stepX`-specific lemmas below establish that equation. -/

theorem step_eq (cfg : GSet w64) (id : w64) (ps : PState) (recv : List Msg)
    (ps1 ps2 : PState) :
    Step cfg id ps recv ps1 → ps1 = ps2 → Step cfg id ps recv ps2 := by
  -- PORT: proof
  sorry

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
  -- PORT: proof
  sorry

/-- `heartbeatResult` refines `Step.heartbeat` at `ps`. -/
theorem step_handle_heartbeat (cfg : GSet w64) (id : w64) (ps : PState) (t : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) :
    toPState t = padoptLeader ps m.From' →
    m.To' = id →
    m.Term' = ps.term →
    ps.role ≠ .leader →
    uint.Z m.Commit' ≤ plogLastIndexZ ps.base ps.log →
    m.From' ≠ id →
    Step cfg id ps [absMsg .heartbeat m ents] (toPState (heartbeatResult id t m)) := by
  -- PORT: proof
  sorry

/-- The term preamble's step-down for a message only a leader sends. -/
theorem step_higher_term_leader (cfg : GSet w64) (id : w64) (ps : PState) (ty : MsgType)
    (m : raftpb.Message) (ents : List raftpb.Entry) :
    fromLeader ty = true →
    uint.Z ps.term < uint.Z m.Term' →
    m.To' = id →
    m.From' ≠ id →
    Step cfg id ps [absMsg ty m ents] (pbecomeFollower ps m.Term' m.From') := by
  -- PORT: proof
  sorry

/-! ## The three adoptions are `padoptLeader` -/

/-- After the term preamble's `becomeFollower(m.Term, m.From)`, with `stepFollower`'s
`r.lead = m.From` on top (a no-op there). -/
theorem adopt_after_stepdown (s : NState) (term src : w64) (pvs : GMap w64 Progress) :
    toPState { becomeFollower s term src with prvals := pvs, lead := src }
    = padoptLeader (pbecomeFollower (toPState s) term src) src := by
  -- PORT: proof
  sorry

/-- `stepFollower`'s `r.lead = m.From` at the current term. A follower's tally is empty
-- `padoptLeader` clears it -- which `NState` does not record by itself; it is the
premise `Hv`. -/
theorem adopt_follower (s : NState) (src : w64) :
    s.role = .follower →
    s.votes = ∅ →
    toPState { s with lead := src } = padoptLeader (toPState s) src := by
  -- PORT: proof
  sorry

/-- `stepCandidate`'s `becomeFollower(r.Term, m.From)`: the term does not move, so the
vote is kept, and the tally is cleared. -/
theorem adopt_candidate (s : NState) (src : w64) (pvs : GMap w64 Progress) :
    toPState { becomeFollower s s.term src with prvals := pvs }
    = padoptLeader (toPState s) src := by
  -- PORT: proof
  sorry

/-! ## Well-formedness is preserved by the handlers -/

theorem nstateWf_handle_app (id : w64) (t : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (s' : NState) :
    NStateWf t → HandleAppResult id t m ents s' → NStateWf s' := by
  -- PORT: proof
  sorry

theorem nstateWf_heartbeatResult (id : w64) (t : NState) (m : raftpb.Message) :
    NStateWf t → NStateWf (heartbeatResult id t m) := by
  -- PORT: proof
  sorry

/-! ## Taking the `stepX` results apart, by type -/

theorem followerStepResult_app (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    m.Type' = MsgApp →
    FollowerStepResult id s m ents sv dropped s' →
    dropped = false ∧ HandleAppResult id { s with lead := m.From' } m ents s' := by
  -- PORT: proof
  sorry

theorem followerStepResult_heartbeat (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    m.Type' = MsgHeartbeat →
    FollowerStepResult id s m ents sv dropped s' →
    dropped = false ∧ s' = heartbeatResult id { s with lead := m.From' } m := by
  -- PORT: proof
  sorry

theorem candidateStepResult_app (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgApp →
    CandidateStepResult cfg id s m ents sv dropped s' →
    dropped = false ∧
    ∃ pvs, HandleAppResult id { becomeFollower s s.term m.From' with prvals := pvs }
      m ents s' := by
  -- PORT: proof
  sorry

theorem candidateStepResult_heartbeat (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgHeartbeat →
    CandidateStepResult cfg id s m ents sv dropped s' →
    dropped = false ∧
    ∃ pvs, s' = heartbeatResult id { becomeFollower s s.term m.From' with prvals := pvs } m := by
  -- PORT: proof
  sorry

/-- A leader ignores a `MsgApp` or `MsgHeartbeat` of its own term. -/
theorem leaderStepResult_app_hb (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (dropped : Bool) (s' : NState) :
    m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat →
    LeaderStepResult cfg id s m ents dropped s' →
    dropped = false ∧ s' = s := by
  -- PORT: proof
  sorry

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
  -- PORT: proof
  sorry

theorem step_higher_term_snap (cfg : GSet w64) (id : w64) (ps : PState)
    (m : raftpb.Message) (sv : raftpb.Snapshot) (voters : List w64) :
    uint.Z ps.term < uint.Z m.Term' →
    m.To' = id →
    m.From' ≠ id →
    Step cfg id ps [absSnap m sv voters] (pbecomeFollower ps m.Term' m.From') := by
  -- PORT: proof
  sorry

theorem nstateWf_handle_snap (id : w64) (t : NState) (m : raftpb.Message)
    (sv : raftpb.Snapshot) (s' : NState) :
    NStateWf t → HandleSnapResult id t m sv s' → NStateWf s' := by
  -- PORT: proof
  sorry

theorem followerStepResult_snap (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    m.Type' = MsgSnap →
    FollowerStepResult id s m ents sv dropped s' →
    dropped = false ∧ HandleSnapResult id { s with lead := m.From' } m sv s' := by
  -- PORT: proof
  sorry

theorem candidateStepResult_snap (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgSnap →
    CandidateStepResult cfg id s m ents sv dropped s' →
    dropped = false ∧
    ∃ pvs, HandleSnapResult id { becomeFollower s s.term m.From' with prvals := pvs }
      m sv s' := by
  -- PORT: proof
  sorry

end StepProof

end repl

end EtcdGrove
end Perennial
