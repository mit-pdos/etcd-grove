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
  · sorry
  · sorry
  · sorry

end StepProof

end branches

end EtcdGrove
end Perennial
