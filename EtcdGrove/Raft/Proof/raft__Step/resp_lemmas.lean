/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_resp_lemmas.v.

Pure lemmas shared by `Step`'s `MsgAppResp`, `MsgHeartbeatResp` and `MsgBeat` branches:
what the three `stepX` result relations say for those three types, turned into the
`Step` witness `Step` needs. Proof structure, not specification: no `Module Type`, no
`Parameter`; only files in this directory may `Require` it.

Lean notes:
* Rocq's section variable `cfg` is an explicit argument of the lemmas that use it.
* Rocq's `Local Ltac kill_type_arms` is not needed: the ported proofs `simp` the type
  tests away.
* Rocq's `Local Lemma`s are `private theorem`s.
-/
import EtcdGrove.Raft.Proof.raft__Step.Base

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section resp_lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

namespace StepProof

/-- `MsgBeat`, `MsgAppResp` and `MsgHeartbeatResp` reach no arm of `stepFollower`. -/
theorem followerStepResult_noop (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (Hty : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp)
    (H : FollowerStepResult id s m ents sv dropped s') : dropped = false ∧ s' = s := by
  unfold FollowerStepResult at H
  rcases Hty with h | h | h <;>
    simp [h, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
      MsgHeartbeatResp, W32] at H <;> exact H

/-- Nor of `stepCandidate`. -/
theorem candidateStepResult_noop (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState)
    (Hty : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp)
    (H : CandidateStepResult cfg id s m ents sv dropped s') : dropped = false ∧ s' = s := by
  unfold CandidateStepResult at H
  rcases Hty with h | h | h <;>
    simp [h, MsgBeat, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgAppResp,
      MsgHeartbeatResp, W32] at H <;> exact H

/-- `stepLeader` on `MsgBeat`: the heartbeats are `Step.beat`'s. -/
theorem leader_beat_step (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (dropped : Bool) (s' : NState)
    (Hr : s.role = .leader) (Hty : m.Type' = MsgBeat) (Hwf : NStateWf s)
    (H : LeaderStepResult cfg id s m ents dropped s') :
    dropped = false ∧ NStateWf s' ∧ Step cfg id (toPState s) [] (toPState s') := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  unfold LeaderStepResult at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨-, ms, pvs, rfl, Hok, Hpm⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩
  · exfalso; rw [Hty] at Hc
    rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
  · refine ⟨Hwf, ?_⟩
    rw [toPState_prvals (sendMsgs s ms) pvs (fun _ => Hpm), toPState_sendMsgs]
    exact .beat _ ms Hpr Hok
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)

/-- `stepLeader` on `MsgHeartbeatResp`: `sendAppend`'s messages, no `Match` moved --
`Step.sendApps`. -/
theorem leader_hbresp_step (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (dropped : Bool) (s' : NState)
    (Hr : s.role = .leader) (Hty : m.Type' = MsgHeartbeatResp) (Hwf : NStateWf s)
    (H : LeaderStepResult cfg id s m ents dropped s') :
    dropped = false ∧ NStateWf s' ∧ Step cfg id (toPState s) [] (toPState s') := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  unfold LeaderStepResult at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨-, ms, pvs, rfl, Hok, Hpm⟩ | ⟨Hc, -⟩
  · exfalso; rw [Hty] at Hc
    rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  · refine ⟨Hwf, ?_⟩
    rw [toPState_prvals (sendMsgs s ms) pvs (fun _ => Hpm), toPState_sendMsgs]
    exact .sendApps _ ms Hpr Hok
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)

/-- A leader's `matched` is its `Progress` values' `Match`. -/
private theorem toPState_matched_leader (s : NState) (Hr : s.role = .leader) :
    (toPState s).matched = prvalsMatch s.prvals := by
  simp [toPState, Hr]

/-- New `Progress` values at a leader: only `matched` moves. -/
private theorem toPState_prvals_leader (s : NState) (pvs : GMap w64 Progress)
    (Hr : s.role = .leader) :
    toPState { s with prvals := pvs } = { toPState s with matched := prvalsMatch pvs } := by
  simp [toPState, Hr]

/-- A protocol state with its commit index set to what it already is. -/
private theorem pstate_commit_same (ps : PState) : { ps with commit := ps.commit } = ps := by
  cases ps; rfl

/-- `stepLeader` on `MsgAppResp` of the current term:

- no `Progress` for the sender: nothing changes, `Step.refl`;
- rejected: `Next` moves, `Match` does not, and the retries are `ReplOk` --
  `Step.sendApps` alone;
- accepted: `Step.appResp` (the sender's `Match` raised, which is `toPState` at the new
  `Progress` values), then `Step.commit` if `maybeCommit` moved the commit index
  (its premises, judged at the raised `Match` map), then `Step.sendApps`
  for what was sent after the commit. -/
theorem leader_appresp_step (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents0 ents : List raftpb.Entry) (dropped : Bool) (s' : NState)
    (Hr : s.role = .leader) (Hty : m.Type' = MsgAppResp) (Hto : m.To' = id)
    (Hteq : m.Term' = s.term) (Hwf : NStateWf s)
    (H : LeaderStepResult cfg id s m ents0 dropped s') :
    dropped = false ∧ NStateWf s' ∧
    ∃ recv, (∀ m' ∈ recv, m' = absMsg .appResp m ents) ∧
      Step cfg id (toPState s) recv (toPState s') := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  unfold LeaderStepResult at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨-, Hres⟩
  · exfalso; rw [Hty] at Hc
    rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  rcases Hres with ⟨-, rfl⟩ | ⟨-, -, ms, pvs, rfl, Hok, Hpm⟩ | ⟨-, Hrej, Hacc⟩
  · -- no `Progress` for the sender
    exact ⟨Hwf, [], fun _ Hin => absurd Hin (List.not_mem_nil), .refl _⟩
  · -- rejected
    refine ⟨Hwf, [], fun _ Hin => absurd Hin (List.not_mem_nil), ?_⟩
    rw [toPState_prvals (sendMsgs s ms) pvs (fun _ => Hpm), toPState_sendMsgs]
    exact .sendApps _ ms Hpr Hok
  · -- accepted
    obtain ⟨x, pvs, c, ms, Hx, Hpvs, Hc, Hms, rfl⟩ := Hacc
    refine ⟨Hwf, ?_⟩
    have Hpr1 : (toPState { s with prvals := pvs }).role = .leader := Hpr
    have H1 : Step cfg id (toPState s) [absMsg .appResp m ents]
        (toPState { s with prvals := pvs }) := by
      rw [toPState_prvals_leader s pvs Hr, Hpvs, ← toPState_matched_leader s Hr]
      exact .appResp (absMsg .appResp m ents) (toPState s) x rfl Hto Hteq Hpr Hrej
        (by rw [toPState_matched_leader s Hr]; exact Hx)
    have H2 : Step cfg id (toPState { s with prvals := pvs }) []
        { toPState { s with prvals := pvs } with commit := c } := by
      rcases Hc with rfl | ⟨Hlt, Hle, Hterm, Hq⟩
      · rw [show s.logst.committed = (toPState { s with prvals := pvs }).commit from rfl,
          pstate_commit_same (toPState { s with prvals := pvs })]
        exact .refl _
      · exact .commit _ c Hpr1 Hlt Hle Hterm Hq
    have H3 : Step cfg id { toPState { s with prvals := pvs } with commit := c } []
        (psendMsgs { toPState { s with prvals := pvs } with commit := c } ms) :=
      .sendApps _ ms Hpr1 (fun m' Hm' =>
        replOk_proper _ _ _ _ rfl rfl rfl rfl (Hms m' Hm'))
    refine ⟨[absMsg .appResp m ents] ++ ([] ++ []), ?_, ?_⟩
    · intro m' Hin; simpa using Hin
    · have He : toPState { sendMsgs { s with logst := { s.logst with committed := c } } ms with
            prvals := pvs } =
          psendMsgs { toPState { s with prvals := pvs } with commit := c } ms := by
        simp [toPState, sendMsgs, psendMsgs, Hr]
      rw [He]
      exact .trans _ _ _ _ _ H1 (.trans _ _ _ _ _ H2 H3)

end StepProof

end resp_lemmas

end EtcdGrove
end Perennial
