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
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section resp_lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

/-- `MsgBeat`, `MsgAppResp` and `MsgHeartbeatResp` reach no arm of `stepFollower`. -/
theorem followerStepResult_noop (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (Hty : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp)
    (H : FollowerStepResult cfg id s m ents sv dropped s') : dropped = false ∧ s' = s := by
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

theorem toPState_rd_leader (s : NState) (Hr : s.role = .leader) : (toPState s).rd = s.rd := by
  simp [toPState, Hr]

/-- `readRespond` changes only the outbox and the read state (2026-10-13). -/
theorem readRespond_eq (id : w64) (s : NState) (q : ReadReq) :
    ∃ o r, readRespond id s q = { s with outbox := o, rd := r } := by
  unfold readRespond
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨s.outbox, s.rd, by cases s; rfl⟩
  · exact ⟨_, _, rfl⟩

theorem readRespondAll_eq (id : w64) (s : NState) (qs : List ReadReq) :
    ∃ o r, readRespondAll id s qs = { s with outbox := o, rd := r } := by
  unfold readRespondAll
  induction qs generalizing s with
  | nil => exact ⟨s.outbox, s.rd, by cases s; rfl⟩
  | cons q qs ih =>
    rw [List.foldl_cons]
    obtain ⟨o1, r1, h1⟩ := readRespond_eq id s q
    rw [h1]
    exact ih { s with outbox := o1, rd := r1 }

theorem toPState_readRespond (id : w64) (s : NState) (Hr : s.role = .leader) (q : ReadReq) :
    toPState (readRespond id s q) = preadRespond id (toPState s) q := by
  unfold readRespond preadRespond
  by_cases h : q.src = W64 0 ∨ q.src = id
  · simp only [h, ↓reduceIte]
    cases q.ents with
    | nil => rfl
    | cons e es => simp [addReadState, toPState, Hr]
  · simp only [h, ↓reduceIte]
    simp [toPState, sendMsgs, psendMsgs, Hr]

theorem toPState_readRespondAll (id : w64) (s : NState) (Hr : s.role = .leader)
    (qs : List ReadReq) :
    toPState (readRespondAll id s qs) = preadRespondAll id (toPState s) qs := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
    have e1 : readRespondAll id s (q :: qs) = readRespondAll id (readRespond id s q) qs := rfl
    rw [e1, preadRespondAll_cons, ← toPState_readRespond id s Hr q]
    obtain ⟨o1, r1, h1⟩ := readRespond_eq id s q
    apply ih
    rw [h1]; exact Hr

theorem readRespondAll_frame (id : w64) (t : NState) (qs : List ReadReq) :
    readRespondAll id t qs = { t with outbox := (readRespondAll id t qs).outbox,
                                      rd := (readRespondAll id t qs).rd } := by
  obtain ⟨o, r, h⟩ := readRespondAll_eq id t qs
  rw [h]

theorem nstateWf_readRespondAll (id : w64) (t : NState) (qs : List ReadReq) (H : NStateWf t) :
    NStateWf (readRespondAll id t qs) := by
  obtain ⟨o, r, h⟩ := readRespondAll_eq id t qs
  rw [h]; exact H

/-- The read path of a `MsgHeartbeatResp` at a leader: `Step.readAck`. -/
theorem readAck_step (cfg : GSet w64) (id : w64) (s1 : NState) (Hr : s1.role = .leader)
    (a : Msg) (N : w64) (Hty : a.ty = .heartbeatResp) (Hto : a.dst = id)
    (Hterm : a.term = s1.term) (Hne : a.ctx ≠ [])
    (HQ : IsQuorumIndex cfg
      (fun v => ((readonlyRecvAck s1.rd.ro a.src a.ctx).acks !! v).getD (W64 0)) N) :
    Step cfg id (toPState s1) [a]
      (toPState (readRespondAll id
        { s1 with rd := { s1.rd with
            ro := (readonlyAdvance (readonlyRecvAck s1.rd.ro a.src a.ctx) N).1 } }
        (readonlyAdvance (readonlyRecvAck s1.rd.ro a.src a.ctx) N).2)) := by
  rw [toPState_readRespondAll id _ (by exact Hr)]
  have Hrd := toPState_rd_leader s1 Hr
  have e : toPState { s1 with rd := { s1.rd with
        ro := (readonlyAdvance (readonlyRecvAck s1.rd.ro a.src a.ctx) N).1 } } =
      { toPState s1 with rd := { (toPState s1).rd with
          ro := (readonlyAdvance (readonlyRecvAck (toPState s1).rd.ro a.src a.ctx) N).1 } } := by
    rw [Hrd]; simp [toPState, Hr]
  rw [e]
  have Hro : (toPState s1).rd.ro = s1.rd.ro := by rw [Hrd]
  have := Step.readAck (cfg := cfg) (id := id) a (toPState s1) N Hty Hto
    (by exact Hterm) (by simp [toPState, Hr, proleRole]) Hne
    (by
      rw [Hro]
      obtain ⟨-, HQq, -⟩ := HQ
      refine ⟨_, HQq, fun v hv => ?_⟩
      have h := (GMap.elem_of_gset _ _).mp hv
      rw [GMap.lookup_filter] at h
      cases hc : cfg !! v with
      | none => rw [hc] at h; cases h
      | some u =>
        rw [hc] at h
        simp only [Option.filter] at h
        split at h
        · rename_i hp; simpa using hp
        · cases h)
  rw [Hro] at this ⊢
  exact this

/-- `stepLeader` on `MsgBeat`: the heartbeats are `Step.beat`'s. -/
theorem leader_beat_step (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (dropped : Bool) (s' : NState)
    (Hr : s.role = .leader) (Hty : m.Type' = MsgBeat) (Hwf : NStateWf s)
    (H : LeaderStepResult cfg id s m ents dropped s') :
    dropped = false ∧ NStateWf s' ∧ Step cfg id (toPState s) [] (toPState s') ∧
      s'.logst = s.logst ∧ s'.term = s.term ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  unfold LeaderStepResult at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨-, ms, pvs, rfl, Hok, Hpm⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩
  rotate_right
  · exfalso
    rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> rw [Hty] at h6 <;> exact absurd h6 (by w32_ne)
  · exfalso; rw [Hty] at Hc
    rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
  · refine ⟨Hwf, ?_, rfl, rfl, rfl, rfl⟩
    rw [toPState_prvals (sendMsgs s ms) pvs (fun _ => Hpm), toPState_sendMsgs]
    exact .beat _ ms Hpr (fun m' h => (Hok m' h).1)
      (fun m' h => by rw [toPState_rd_leader s Hr]; exact (Hok m' h).2)
  all_goals exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)

/-- `stepLeader` on `MsgHeartbeatResp` (of the current term, to this node):
`sendAppend`'s messages, no `Match` moved -- `Step.sendApps`; then (2026-10-13), with a
context, the read path -- `Step.readAck`, receiving the message. -/
theorem leader_hbresp_step (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8) (dropped : Bool) (s' : NState)
    (Hr : s.role = .leader) (Hty : m.Type' = MsgHeartbeatResp) (Hto : m.To' = id)
    (Hteq : m.Term' = s.term) (Hwf : NStateWf s)
    (H : LeaderStepResult cfg id s m ents dropped s' ctx) :
    dropped = false ∧ NStateWf s' ∧
    (∃ recv, (∀ m' ∈ recv, m' = absMsg .heartbeatResp m ents ctx) ∧
      Step cfg id (toPState s) recv (toPState s')) ∧
      s'.logst = s.logst ∧ s'.term = s.term ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  unfold LeaderStepResult at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨-, ms, pvs, Hok, Hpm, Hrd⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩
  rotate_right
  · exfalso
    rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> rw [Hty] at h6 <;> exact absurd h6 (by w32_ne)
  all_goals try (exfalso; rw [Hty] at Hc; first
    | exact absurd Hc (by w32_ne)
    | (rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)))
  have H1 : Step cfg id (toPState s) [] (toPState { sendMsgs s ms with prvals := pvs }) := by
    rw [toPState_prvals (sendMsgs s ms) pvs (fun _ => Hpm), toPState_sendMsgs]
    exact .sendApps _ ms Hpr Hok
  rcases Hrd with ⟨-, rfl⟩ | ⟨Hne, N, HN, Hs'⟩
  · exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, H1⟩, rfl, rfl, rfl, rfl⟩
  · -- the read path
    rw [Hs']
    refine ⟨nstateWf_readRespondAll id _ _ Hwf, ⟨[] ++ [absMsg .heartbeatResp m ents ctx], ?_, ?_⟩,
      by rw [readRespondAll_frame]; try rfl, by rw [readRespondAll_frame]; try rfl,
      by rw [readRespondAll_frame]; try rfl, by rw [readRespondAll_frame]; try rfl⟩
    · intro m' h; simpa using h
    · exact .trans _ _ _ _ _ H1 (readAck_step cfg id { sendMsgs s ms with prvals := pvs }
        (by exact Hr) (absMsg .heartbeatResp m ents ctx) N rfl Hto Hteq Hne HN)

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
    (∃ recv, (∀ m' ∈ recv, m' = absMsg .appResp m ents) ∧
      Step cfg id (toPState s) recv (toPState s')) ∧
    NetFrame s s' ∧ TermStep m s s' := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  unfold LeaderStepResult at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨-, Hres⟩ | ⟨Hc6, -⟩
  rotate_right
  · exfalso
    rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> rw [Hty] at h6 <;> exact absurd h6 (by w32_ne)
  · exfalso; rw [Hty] at Hc
    rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  · exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  rcases Hres with ⟨-, rfl⟩ | ⟨-, -, ms, pvs, rfl, Hok, Hpm⟩ | ⟨-, Hrej, Hacc⟩
  · -- no `Progress` for the sender
    exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin (List.not_mem_nil), .refl _⟩,
      keep_frame rfl rfl rfl rfl rfl⟩
  · -- rejected
    refine ⟨Hwf, ⟨[], fun _ Hin => absurd Hin (List.not_mem_nil), ?_⟩,
      keep_frame rfl rfl rfl rfl rfl⟩
    rw [toPState_prvals (sendMsgs s ms) pvs (fun _ => Hpm), toPState_sendMsgs]
    exact .sendApps _ ms Hpr Hok
  · -- accepted
    obtain ⟨x, pvs, c, hb, ms, Hx, Hpvs, Hc, Hms, Hrel⟩ := Hacc
    by_cases Hcc : c ≠ s.logst.committed
    · -- a commit, which releases the pending read-index requests (2026-10-13)
      rw [if_neg Hcc] at Hrel
      obtain ⟨Hhb, rfl⟩ := Hrel
      rcases Hc with Hc | ⟨Hlt, Hle, Hterm, Hq⟩
      · exact absurd Hc Hcc
      refine ⟨Hwf, ?_, keep_frame rfl rfl rfl rfl rfl⟩
      have Hpr1 : (toPState { s with prvals := pvs }).role = .leader := Hpr
      have H1 : Step cfg id (toPState s) [absMsg .appResp m ents]
          (toPState { s with prvals := pvs }) := by
        rw [toPState_prvals_leader s pvs Hr, Hpvs, ← toPState_matched_leader s Hr]
        exact .appResp (absMsg .appResp m ents) (toPState s) x rfl Hto Hteq Hpr Hrej
          (by rw [toPState_matched_leader s Hr]; exact Hx)
      have H2 : Step cfg id (toPState { s with prvals := pvs }) []
          { toPState { s with prvals := pvs } with commit := c } :=
        .commit _ c Hpr1 Hlt Hle Hterm Hq
      let ps2 : PState := { toPState { s with prvals := pvs } with commit := c }
      have H3 : Step cfg id ps2 []
          { ps2 with rd := { ps2.rd with
              pend := []
              ro := readonlyRelease ps2.rd.ro id ps2.commit ps2.rd.pend } } :=
        .readRelease _ Hpr1 Hterm
      let ps3 : PState := { ps2 with rd := { ps2.rd with
              pend := []
              ro := readonlyRelease ps2.rd.ro id ps2.commit ps2.rd.pend } }
      have Hps2rd : ps2.rd = s.rd := by simp [ps2, toPState, Hr]
      have H4 : Step cfg id ps3 [] (psendMsgs ps3 hb) :=
        .beat _ hb Hpr1
          (fun m' h => by
            have := (Hhb m' h).1
            unfold HeartbeatOk matchOf at this ⊢
            simpa [ps3, ps2, toPState, Hr] using this)
          (fun m' h => by
            obtain ⟨k, -, -, Hk⟩ := (Hhb m' h).2
            rw [Hk]
            have : ps3.rd.ro = readonlyRelease s.rd.ro id c s.rd.pend := by
              simp [ps3, ps2, toPState, Hr]
            rw [this]
            exact HbCtxOk_release _ _ _ _ k)
      have H5 : Step cfg id (psendMsgs ps3 hb) [] (psendMsgs (psendMsgs ps3 hb) ms) :=
        .sendApps _ ms Hpr1 (fun m' Hm' =>
          replOk_proper _ _ _ _ rfl rfl rfl rfl (Hms m' Hm'))
      refine ⟨[absMsg .appResp m ents] ++ ([] ++ ([] ++ ([] ++ []))), ?_, ?_⟩
      · intro m' Hin; simpa using Hin
      · have He : toPState { sendMsgs (sendMsgs (releasedState id
              { s with logst := { s.logst with committed := c } }) hb) ms with prvals := pvs } =
            psendMsgs (psendMsgs ps3 hb) ms := by
          simp [ps3, ps2, toPState, sendMsgs, psendMsgs, releasedState, Hr]
        rw [He]
        exact .trans _ _ _ _ _ H1 (.trans _ _ _ _ _ H2 (.trans _ _ _ _ _ H3
          (.trans _ _ _ _ _ H4 H5)))
    rw [if_pos (Classical.not_not.mp Hcc)] at Hrel
    obtain ⟨-, rfl⟩ := Hrel
    refine ⟨Hwf, ?_, keep_frame rfl rfl rfl rfl rfl⟩
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
