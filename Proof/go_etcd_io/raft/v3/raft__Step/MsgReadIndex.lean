/- `Step`'s `MsgReadIndex` branch (2026-10-13, no Rocq counterpart): a read-index
request, local (`ReadIndex`, `From = 0`) or forwarded by a follower; `Term = 0`, so the term
preamble is skipped and `r.step(r, m)` runs:

- `stepFollower` forwards it to the leader (`Step.readFwd`) or, with no leader known,
  drops it (`Step.refl`);
- `stepCandidate` ignores it;
- `stepLeader` queues it as pending while no entry of its term is committed
  (`Step.readPend`), or lets it arrive (`Step.readArrive`) and broadcasts heartbeats
  carrying the new position (`Step.beat`).

Proof structure, not specification: only `Proof/raft__Step.lean` may import this module.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

theorem followerStepResult_readIndex (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8) (Hty : m.Type' = MsgReadIndex)
    (H : FollowerStepResult id s m ents sv dropped s' cl) :
    dropped = false ∧
    (if s.lead = W64 0 then s' = s else s' = sendMsgs s [readForward id s.lead m ents cl]) := by
  unfold FollowerStepResult at H
  simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, W32] at H
  simpa using H

theorem candidateStepResult_readIndex (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) (cl : List w8)
    (Hty : m.Type' = MsgReadIndex ∨ m.Type' = MsgReadIndexResp)
    (H : CandidateStepResult cfg id s m ents sv dropped s' cl) : dropped = false ∧ s' = s := by
  unfold CandidateStepResult at H
  rcases Hty with h | h <;>
  simp only [h, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp, W32] at H <;>
  simpa using H

theorem toPState_rd_leader' (s : NState) (Hr : s.role = .leader) : (toPState s).rd = s.rd := by
  simp [toPState, Hr]

/-- The read-index request `Step` receives. -/
theorem wp_Step_MsgReadIndex (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (ctx : List w8) :
    m.Type' = MsgReadIndex →
    m.Term' = W64 0 →
    1 < GMap.size cfg →
    ents ≠ [] →
    (s.role = .follower → s.lead ≠ id) →
    (s.role = .leader → RdOk cfg s.rd ∧ s.term ≠ W64 0) →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ ents ∗
        "#Hctx" ∷ m.Context' ↦*□ ctx }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .readIndex m ents ctx) ∧
            recv.length ≤ 1 ∧ Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hterm Hsz Hne Hlok Hlrd Hcfg Hwf
  wp_start as ⟨Hphys, #Hents, #Hctx⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_true Hterm]
  wp_auto
  rw [Hty]
  wp_auto
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  have HnVR : m.Type' ≠ MsgVoteResp := by rw [Hty]; w32_ne
  cases Hrole : s.role
  · -- Follower: forward to the leader, or drop
    simp only [stepFuncOf]
    wp_apply _P.stepFollower cfg r id s m ents (zero_val _) [] ctx
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
        (fun _ => ⟨Hterm, Hlok Hrole⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro _; iexact Hctx
      isplitl []
      · iintro _; iexact Hents
      isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs1⟩ := followerStepResult_readIndex _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    by_cases Hl0 : s.lead = W64 0
    · rw [if_pos Hl0] at Hs1
      subst s1
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], by simp, by simp, .refl _⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩
    · rw [if_neg Hl0] at Hs1
      subst s1
      iapply HΦ $$ %interface.nil %(sendMsgs s [readForward id s.lead m ents ctx])
      iframe Hphys
      ipureintro
      have Hld : (toPState s).lead = s.lead :=
        toPState_lead_nonpre s (by rw [Hrole]; exact PRole.noConfusion)
      refine ⟨nstateWf_sendMsgs _ _ Hwf, ⟨[absMsg .readIndex m ents ctx], by simp, by simp, ?_⟩,
        rfl, NetFrame.of_logst rfl, TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
      rw [toPState_sendMsgs]
      have := Step.readFwd (cfg := cfg) (id := id) (absMsg .readIndex m ents ctx) (toPState s)
        rfl (by simp [toPState, Hrole, proleRole]) (by rw [Hld]; exact Hl0)
      rw [Hld] at this
      have He : readForward id s.lead m ents ctx =
          { absMsg .readIndex m ents ctx with
            src := if (absMsg .readIndex m ents ctx).src = W64 0 then id
                   else (absMsg .readIndex m ents ctx).src
            dst := s.lead
            term := W64 0 } := by
        first
          | rfl
          | (simp only [readForward, absMsg, absMsgFrom, Msg.mkV]; rfl)
          | (simp [readForward, absMsg, absMsgFrom]; split <;> rfl)
      rw [He]
      exact this
  · -- a candidate (a pre-candidate is one too) ignores it
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m ents (zero_val _) [] ctx
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inl Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs1⟩ := candidateStepResult_readIndex _ _ _ _ _ _ _ _ _ (.inl Hty) Hres
    subst s1
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], by simp, by simp, .refl _⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩
  · -- Leader: pending, or arrival and heartbeats
    simp only [stepFuncOf]
    have Hpr : (toPState s).role = .leader := by simp [toPState, Hrole, proleRole]
    have Hrd := toPState_rd_leader' s Hrole
    wp_apply _P.stepLeader cfg r id s m ents ctx
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))))
        Hrole Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => Hlrd Hrole)
        (fun _ => ⟨Hsz, Hne⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro _; iexact Hents
    unfold LeaderStepResult at Hres
    rw [ite_eq_right (by rw [Hty]; w32_ne)] at Hres
    obtain ⟨rfl, Hres⟩ := Hres
    unfold LeaderNonpropResult at Hres
    rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨-, Hri⟩ | ⟨Hc, -⟩
    all_goals try (exfalso; rw [Hty] at Hc; first
      | exact absurd Hc (by w32_ne)
      | (rcases Hc with Hc | Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)))
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    rcases Hri with ⟨Hnct, rfl⟩ | ⟨Hct, ms, pvs, rfl, Hms, Hpm⟩
    · -- no entry of the term committed: pending
      iapply HΦ $$ %interface.nil %({ s with rd := { s.rd with pend := s.rd.pend ++ [(m, ents)] } })
      iframe Hphys
      ipureintro
      refine ⟨Hwf, ⟨[absMsg .readIndex m ents ctx], by simp, by simp, ?_⟩, rfl,
        NetFrame.of_logst rfl, TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
      have e : toPState { s with rd := { s.rd with pend := s.rd.pend ++ [(m, ents)] } } =
          { toPState s with rd := { (toPState s).rd with
              pend := (toPState s).rd.pend ++ [(m, (absMsg .readIndex m ents ctx).entries)] } } := by
        rw [Hrd]; simp [toPState, Hrole, absMsg, absMsgFrom]
      rw [e]
      exact Step.readPend (absMsg .readIndex m ents ctx) (toPState s) m rfl Hpr rfl
    · -- arrival, then the heartbeats
      iapply HΦ $$ %interface.nil %({ sendMsgs (arriveState id s m ents) ms with prvals := pvs })
      iframe Hphys
      ipureintro
      refine ⟨nstateWf_prvals _ _ (nstateWf_sendMsgs _ _ Hwf),
        ⟨[absMsg .readIndex m ents ctx] ++ [], by simp, by simp, ?_⟩, rfl,
        NetFrame.of_logst rfl, TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
      let ps1 : PState := { toPState s with rd := { (toPState s).rd with
          ro := readonlyArrive (toPState s).rd.ro id
            ⟨(toPState s).commit, (absMsg .readIndex m ents ctx).src,
             (absMsg .readIndex m ents ctx).entries⟩ } }
      have H1 : Step cfg id (toPState s) [absMsg .readIndex m ents ctx] ps1 :=
        Step.readArrive (absMsg .readIndex m ents ctx) (toPState s) rfl Hpr Hct
      have Hps1ro : ps1.rd.ro = readonlyArrive s.rd.ro id (arriveReq s m ents) := by
        simp [ps1, arriveReq, toPState, Hrole, absMsg, absMsgFrom]
      have H2 : Step cfg id ps1 [] (psendMsgs ps1 ms) :=
        .beat _ ms Hpr
          (fun m' h => by
            have := (Hms m' h).1
            unfold HeartbeatOk matchOf at this ⊢
            simpa [ps1] using this)
          (fun m' h => by
            rw [(Hms m' h).2, Hps1ro]
            have : hbCtx (readonlyAdd s.rd.ro (arriveReq s m ents)) =
                hbCtx (readonlyArrive s.rd.ro id (arriveReq s m ents)) := by
              unfold readonlyArrive; rw [hbCtx_recvAck]
            rw [this]
            exact hbCtx_ok _)
      have He : toPState { sendMsgs (arriveState id s m ents) ms with prvals := pvs } =
          psendMsgs ps1 ms := by
        rw [toPState_prvals (sendMsgs (arriveState id s m ents) ms) pvs (fun _ => Hpm),
          toPState_sendMsgs]
        congr 1
        simp [ps1, arriveState, arriveReq, toPState, Hrole, absMsg, absMsgFrom]
      rw [He]
      exact .trans _ _ _ _ _ H1 H2
  · -- a candidate (a pre-candidate is one too) ignores it
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m ents (zero_val _) [] ctx
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inr Hrole) Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hs1⟩ := candidateStepResult_readIndex _ _ _ _ _ _ _ _ _ (.inl Hty) Hres
    subst s1
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], by simp, by simp, .refl _⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩

end StepProof

end branches

end EtcdGrove
end Perennial
