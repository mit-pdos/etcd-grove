/- `Step`'s `MsgReadIndex` branch (2026-10-13, no Rocq counterpart): a read-index
request, local (`ReadIndex`, `From = 0`) or forwarded by a follower; `Term = 0`, so the term
preamble is skipped and `r.step(r, m)` runs:

- `stepFollower` forwards it to the leader (`StepCF.readFwd`) or, with no leader known,
  drops it (`StepC.refl`);
- `stepCandidate` ignores it;
- `stepLeader` queues it as pending while no entry of its term is committed
  (`StepCF.readPend`), or lets it arrive (`StepCF.readArrive`) and broadcasts heartbeats
  carrying the new position (`StepC.beat`) -- or (2026-10-14, the pinned raft with the
  single-voter fix) at a configuration whose only voter is the leader itself answers it at once
  (`StepCF.readSingle`).

Proof structure, not specification: only `Proof/raft__Step.lean` may import this module.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas
public import Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

theorem followerStepResult_readIndex (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sv : SnapshotM) (dropped : Bool) (s' : NState)
    (cl : List w8) (Hty : m.Type' = MsgReadIndex)
    (H : FollowerStepResultC c scfg id s m ents sv dropped s' c' cl) :
    c = c' ∧ dropped = false ∧
    (if s.lead = W64 0 then s' = s else s' = sendMsgs s [readForward id s.lead m ents cl]) := by
  unfold FollowerStepResultC at H
  refine ⟨(FollowerStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp,MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, W32] at H
  simpa using H

theorem candidateStepResult_readIndex (c : CfgM) {scfg : CSLists} {c' : CfgM} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (sv : SnapshotM) (dropped : Bool)
    (s' : NState) (cl : List w8)
    (Hty : m.Type' = MsgReadIndex ∨ m.Type' = MsgReadIndexResp)
    (H : CandidateStepResultC c scfg id s m ents sv dropped s' c' cl) : c = c' ∧ dropped = false ∧ s' = s := by
  unfold CandidateStepResultC at H
  refine ⟨(CandidateStepResultC.cfg (by nonsnap Hty) H).symm, ?_⟩
  replace H := H.2
  rcases Hty with h | h <;>
  simp only [h, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp,MsgCheckQuorum, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp, W32] at H <;>
  simpa using H

theorem toPState_rd_leader' (s : NState) (Hr : s.role = .leader) : (toPState s).rd = s.rd := by
  simp [toPState, Hr]

set_option maxHeartbeats 1000000 in
/-- The read-index request `Step` receives. -/
theorem wp_Step_MsgReadIndex (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) :
    m.Type' = MsgReadIndex →
    m.Term' = W64 0 →
    ents ≠ [] →
    (s.role = .follower → s.lead ≠ id) →
    (s.role = .leader → RdOk c.voters s.rd ∧ s.term ≠ W64 0) →
    NStateWf s →
    -- (2026-10-22, D38a) a forwarded message has no responses (`stepFollower`'s premise)
    rs = [] →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .readIndex m ents ctx) ∧
            recv.length ≤ 1 ∧ StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  intro Hty Hterm Hne Hlok Hlrd Hwf Hnors
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  rw [decide_eq_true Hterm]
  wp_auto
  wp_drive _Q
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  have HnVR : m.Type' ≠ MsgVoteResp := by rw [Hty]; w32_ne
  cases Hrole : s.role
  · -- Follower: forward to the leader, or drop
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
        (fun _ => ⟨Hterm, Hlok Hrole⟩) (by intro Hc; first | (exfalso; rcases Hc with Hc | Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne)) | (exfalso; rcases Hc with Hc | Hc | Hc <;> simp_all [MsgApp, MsgHeartbeat, MsgSnap]) | simp_all [becomeFollower, resetTo, resetTo0])
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun _ => Hnors) $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := followerStepResult_readIndex _ _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    by_cases Hl0 : s.lead = W64 0
    · rw [ite_eq_left Hl0] at Hs1
      subst s1
      iapply HΦ $$ %interface.nil %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩
    · rw [ite_eq_right Hl0] at Hs1
      subst s1
      iapply HΦ $$ %interface.nil %(sendMsgs s [readForward id s.lead m ents ctx])
      iframe Hphys
      ipureintro
      have Hld : (toPState s).lead = s.lead :=
        toPState_lead_nonpre s (by rw [Hrole]; exact PRole.noConfusion)
      refine ⟨nstateWf_sendMsgs _ _ Hwf, ⟨[absMsg .readIndex m ents ctx], by simp, by simp, StepCD.frame ?_ (by rframe)⟩,
        rfl, NetFrame.of_logst rfl, TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
      rw [toPState_sendMsgs]
      have := StepCF.readFwd (c := c) (id := id) (absMsg .readIndex m ents ctx) (toPState s)
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
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inl Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_readIndex _ _ _ _ _ _ _ _ _ (.inl Hty) Hres
    subst s1
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩
  · -- Leader: pending, or arrival and heartbeats
    simp only [stepFuncOf]
    have Hpr : (toPState s).role = .leader := by simp [toPState, Hrole, proleRole]
    have Hrd := toPState_rd_leader' s Hrole
    imod (preceipt_zero (GF := GF)) with #Hrc00
    wp_apply _P.stepLeader c r id s ml m ents sn ctx rs 0
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))))
        Hrole (by intro Hc; exfalso; first | (rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne)) | (rcases Hc with Hc | Hc <;> simp_all [MsgBeat, MsgTransferLeader]))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => Hlrd Hrole)
        (fun _ => Hne)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys $Hrc00 Hm] as %err %s' %dropped ⟨Hphys, -, %Hres, Herrn⟩
    · isplitl [Hm]
      · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    unfold LeaderStepResultC at Hres
    rw [ite_eq_right (by rw [Hty]; w32_ne)] at Hres
    obtain ⟨rfl, Hres⟩ := Hres
    unfold LeaderNonpropResultC at Hres
    rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨-, Hri⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩ | ⟨Hc7, -⟩
    rotate_right
    · exfalso; first | (rw [Hty] at Hc7; exact absurd Hc7 (by w32_ne)) | (rcases Hty with h' | h' <;> rw [h'] at Hc7 <;> exact absurd Hc7 (by w32_ne)) | exact absurd Hc7 (by w32_ne)
    rotate_right
    · exfalso
      rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> rw [Hty] at h6 <;> exact absurd h6 (by w32_ne)
    all_goals try (exfalso; rw [Hty] at Hc; first
      | exact absurd Hc (by w32_ne)
      | (rcases Hc with Hc | Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)))
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    rcases Hri with ⟨Hnct, rfl⟩ | ⟨Hct, ⟨Hsg, rfl⟩ | ⟨-, ms, pvs, rfl, Hms, Hpm⟩⟩
    · -- no entry of the term committed: pending
      iapply HΦ $$ %interface.nil %({ s with rd := { s.rd with pend := s.rd.pend ++ [(m, ents)] } })
      iframe Hphys
      ipureintro
      refine ⟨Hwf, ⟨[absMsg .readIndex m ents ctx], by simp, by simp, StepCD.frame ?_ (by rframe)⟩, rfl,
        NetFrame.of_logst rfl, TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
      have e : toPState { s with rd := { s.rd with pend := s.rd.pend ++ [(m, ents)] } } =
          { toPState s with rd := { (toPState s).rd with
              pend := (toPState s).rd.pend ++ [(m, (absMsg .readIndex m ents ctx).entries)] } } := by
        rw [Hrd]; simp [toPState, Hrole, absMsg, absMsgFrom]
      rw [e]
      exact StepCF.readPend (absMsg .readIndex m ents ctx) (toPState s) m rfl Hpr rfl
    · -- (2026-10-14) the leader is the single voter: answered at once
      ihave Hphys := ownRaftPhysC_eq (V := c.voters) c r id (readRespond id s (arriveReq s m ents))
        (readRespondAll id s [arriveReq s m ents]) rfl $$ Hphys
      iapply HΦ $$ %interface.nil %(readRespondAll id s [arriveReq s m ents])
      iframe Hphys
      ipureintro
      refine ⟨nstateWf_readRespondAll id _ _ Hwf,
        ⟨[absMsg .readIndex m ents ctx], by simp, by simp, StepCD.frame ?_ ?_⟩, rfl, ?_, ?_⟩
      · rw [toPState_readRespondAll id s Hrole]
        have H1 := StepCF.readSingle (c := c) (id := id) (absMsg .readIndex m ents ctx)
          (toPState s) rfl Hpr Hct Hsg
        first
          | exact H1
          | (simp only [absMsg, absMsgFrom, toPState, arriveReq] at H1 ⊢; exact H1)
      · rw [readRespondAll_frame]
        exact ⟨rfl, rfl, fun _ => ⟨Hrole, rfl⟩⟩
      · rw [readRespondAll_frame]; exact NetFrame.of_logst rfl
      · rw [readRespondAll_frame]; exact TermStep.of_term rfl (fun _ => Int.le_refl _)
    · -- arrival, then the heartbeats
      iapply HΦ $$ %interface.nil %({ sendMsgs (arriveState id s m ents) ms with prvals := pvs })
      iframe Hphys
      ipureintro
      refine ⟨nstateWf_prvals _ _ (nstateWf_sendMsgs _ _ Hwf),
        ⟨[absMsg .readIndex m ents ctx] ++ [], by simp, by simp, StepCD.frame ?_ (by rframe)⟩, rfl,
        NetFrame.of_logst rfl, TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
      let ps1 : PState := { toPState s with rd := { (toPState s).rd with
          ro := readonlyArrive (toPState s).rd.ro id
            ⟨(toPState s).commit, (absMsg .readIndex m ents ctx).src,
             (absMsg .readIndex m ents ctx).entries⟩ } }
      have H1 : StepCF c id (toPState s) [absMsg .readIndex m ents ctx] ps1 :=
        StepCF.readArrive (absMsg .readIndex m ents ctx) (toPState s) rfl Hpr Hct
      have Hps1ro : ps1.rd.ro = readonlyArrive s.rd.ro id (arriveReq s m ents) := by
        simp [ps1, arriveReq, toPState, Hrole, absMsg, absMsgFrom]
      have H2 : StepCF c id ps1 [] (psendMsgs ps1 ms) :=
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
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inr Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_readIndex _ _ _ _ _ _ _ _ _ (.inl Hty) Hres
    subst s1
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩
  -/

end StepProof

end branches

end EtcdGrove
end Perennial
