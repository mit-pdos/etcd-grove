/- `Step`'s `MsgReadIndexResp` branch (2026-10-13, no Rocq counterpart): a leader's answer
to a request this node forwarded, carrying the request's entry (its context) and the read
index.

- `m.Term > r.Term`: the preamble steps down (`becomeFollower(m.Term, None)`, the type is
  not `fromLeader`), then `stepFollower` records a `ReadState` (`Step.higherTerm`,
  `Step.readState`);
- `m.Term < r.Term`: logged and dropped (`Step.refl`);
- `m.Term = r.Term`: a follower records a `ReadState` (`Step.readState`); a candidate
  and a leader ignore it (`Step.refl`).

Proof structure, not specification: only `Proof/raft__Step.lean` may import this module.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.MsgReadIndex

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

theorem followerStepResult_readIndexResp (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (e : raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8) (Hty : m.Type' = MsgReadIndexResp)
    (H : FollowerStepResult cfg id s m [e] sv dropped s' cl) :
    dropped = false ∧ s' = addReadState s m.Index' e.Data' := by
  unfold FollowerStepResult at H
  simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp, W32] at H
  simpa using H

theorem toPState_addReadState (s : NState) (i : w64) (d : GoSlice) (Hr : s.role ≠ .leader) :
    toPState (addReadState s i d) =
      { toPState s with rd := { (toPState s).rd with
          states := (toPState s).rd.states ++ [⟨i, d⟩] } } := by
  simp [addReadState, toPState, Hr, rdNL]
  try exact ⟨rfl, rfl⟩

theorem wp_Step_MsgReadIndexResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (e : raftpb.Entry) (ctx : List w8) :
    m.Type' = MsgReadIndexResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    m.From' ≠ id →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "#Hents" ∷ m.Entries' ↦*□ [e] }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .readIndexResp m [e] ctx) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfid Hcfg Hwf
  wp_start as ⟨Hphys, #Hents⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  have Hfl : fromLeader MsgType.readIndexResp = false := rfl
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · -- a step-down, then a follower's `ReadState`
    rw [decide_eq_true Hgt]
    wp_auto
    iterate 6 (try (rw [Hty]; wp_auto))
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    iterate 6 (try (rw [Hty]; wp_auto))
    wp_apply _P.becomeFollower _ _ _ _ _ _ (by exact Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
    iterate 6 (try (rw [Hty]; wp_auto))
    wp_apply raft.wp_load_step $$ Hphys as Hphys
    rw [show ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).stepfn =
      stepFuncOf .follower from rfl]
    simp only [stepFuncOf]
    wp_apply _P.stepFollower cfg r id { becomeFollower s m.Term' (W64 0) with prvals := pvs }
        m [e] (zero_val _) [] []
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
      isplitl []
      · iintro _; iexact Hents
      isplitl []
      · iapply Hsnap0
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
    obtain ⟨rfl, rfl⟩ := followerStepResult_readIndexResp _ _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil
      %(addReadState { becomeFollower s m.Term' (W64 0) with prvals := pvs } m.Index' e.Data')
    iframe Hphys
    ipureintro
    have Hfr := stepdown_frame (m := m) (s := s)
      (s' := addReadState { becomeFollower s m.Term' (W64 0) with prvals := pvs } m.Index' e.Data')
      (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl
    refine ⟨⟨rfl, rfl⟩, ⟨[absMsg .readIndexResp m [e] ctx] ++ [absMsg .readIndexResp m [e] ctx],
      by simp, ?_⟩, rfl, Hfr.1, Hfr.2⟩
    rw [toPState_addReadState _ _ _ (by simp [becomeFollower]),
      toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs (by simp [becomeFollower]),
      toPState_becomeFollower]
    have Hst := Step.higherTerm (cfg := cfg) (id := id) (absMsg .readIndexResp m [e] ctx)
      (toPState s) Hgt Hto (fun h => by simp [absMsg, absMsgFrom, Hfl] at h)
    rw [show (if fromLeader (absMsg .readIndexResp m [e] ctx).ty then
        (absMsg .readIndexResp m [e] ctx).src else W64 0) = W64 0 by
      simp [absMsg, absMsgFrom, Hfl]] at Hst
    refine .trans _ _ _ _ _ Hst ?_
    exact Step.readState (absMsg .readIndexResp m [e] ctx) _ e rfl rfl
  · rw [decide_eq_false Hgt]
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · -- stale: dropped
      rw [decide_eq_true Hlt]
      wp_auto
      wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
      wp_apply raft.wp_load_preVote $$ Hphys as Hphys
      cases s.prevote <;> wp_auto
      all_goals iterate 6 (try (rw [Hty]; wp_auto))
      all_goals
        wp_apply raft.wp_load_id $$ Hphys as Hphys
        wp_apply raft.wp_load_Term $$ Hphys as Hphys
        wp_raft_log
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ Hin => absurd Hin List.not_mem_nil, .refl _⟩, rfl,
          NetFrame.refl _, TermStep.refl _ _⟩
    · -- the current term
      have Hteq : m.Term' = s.term := by word
      rw [decide_eq_false Hlt]
      wp_auto
      rw [Hty]
      wp_auto
      wp_apply raft.wp_load_step $$ Hphys as Hphys
      rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
      cases Hrole : s.role
      · -- Follower: a `ReadState`
        simp only [stepFuncOf]
        wp_apply _P.stepFollower cfg r id s m [e] (zero_val _) [] []
            (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
          $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
        · isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
          isplitl []
          · iintro _; iexact Hents
          isplitl []
          · iapply Hsnap0
          · iintro %Hc; exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
        obtain ⟨rfl, rfl⟩ := followerStepResult_readIndexResp _ _ _ _ _ _ _ _ _ Hty Hres
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %(addReadState s m.Index' e.Data')
        iframe Hphys
        ipureintro
        refine ⟨Hwf, ⟨[absMsg .readIndexResp m [e] ctx], by simp, ?_⟩, rfl,
          NetFrame.of_logst rfl, TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
        rw [toPState_addReadState _ _ _ (by rw [Hrole]; decide)]
        exact Step.readState (absMsg .readIndexResp m [e] ctx) _ e rfl rfl
      · -- Candidate: ignored
        simp only [stepFuncOf]
        wp_apply _P.stepCandidate cfg r id s m [e] (zero_val _) [] []
            (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))))
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
        obtain ⟨rfl, Hs1⟩ := candidateStepResult_readIndex _ _ _ _ _ _ _ _ _ (.inr Hty) Hres
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], by simp, .refl _⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩
      · -- Leader: ignored (neither switch has it)
        simp only [stepFuncOf]
        wp_apply _P.stepLeader cfg r id s m [e] []
            (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty))))))))))
            Hrole Hcfg
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by
              exfalso; rw [Hty] at Hc
              rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          $$ [$Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
        · isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        unfold LeaderStepResult at Hres
        rw [ite_eq_right (by rw [Hty]; w32_ne)] at Hres
        obtain ⟨rfl, Hres⟩ := Hres
        unfold LeaderNonpropResult at Hres
        rcases Hres with ⟨-, Hs'⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩
        rotate_right
        · exfalso
          rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> rw [Hty] at h6 <;> exact absurd h6 (by w32_ne)
        all_goals try (exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        subst s'
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], by simp, .refl _⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩
      · -- PreCandidate: ignored
        simp only [stepFuncOf]
        wp_apply _P.stepCandidate cfg r id s m [e] (zero_val _) [] []
            (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl Hty)))))))))
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
        obtain ⟨rfl, Hs1⟩ := candidateStepResult_readIndex _ _ _ _ _ _ _ _ _ (.inr Hty) Hres
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], by simp, .refl _⟩, rfl, NetFrame.refl _, TermStep.refl _ _⟩

end StepProof

end branches

end EtcdGrove
end Perennial
