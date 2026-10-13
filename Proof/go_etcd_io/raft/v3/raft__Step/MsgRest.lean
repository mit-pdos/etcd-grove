/- `Step`'s branches for the types it was extended to last (2026-10-13, no Rocq
counterpart): the local reports `MsgUnreachable` and `MsgSnapStatus` and `MsgForgetLeader`
(`Term = 0`), and leader transfer, `MsgTransferLeader` and `MsgTimeoutNow`. None of them is
in the model (`mtypeOf` is `none`): they carry no protocol fact.

- the local three run `r.step(r, m)`: a follower forgets its leader (`Step.abandon`); the
  reports change a leader's `Progress` states only (`Step.sendApps` of nothing);
- `MsgTransferLeader`: a stamped one of a later term makes the node step down
  (`Step.higherTerm`, justified by a free message, `stepdownMsg`) and, now leaderless,
  drop it; one of an earlier term is dropped; otherwise `r.step(r, m)`: a follower forwards
  it to its leader (nothing the model sees), a leader records the transferee and appends to
  it (`Step.sendApps`);
- `MsgTimeoutNow`: likewise, but a follower campaigns (`hup(campaignTransfer)`, an
  ordinary `Step.campaign`).

Proof structure, not specification: only `Proof/raft__Step.lean` may import this module.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The free message that justifies a step-down to the term of a message outside the model
(`Step.higherTerm`): a pre-vote of that term, which carries nothing (`MsgFree`) and is not a
leader's (so no leader is adopted, as `becomeFollower(m.Term, None)` adopts none). -/
def stepdownMsg (id : w64) (m : raftpb.Message) : Msg :=
  Msg.plain .preVote m.From' id m.Term' false

end results

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

theorem followerStepResult_forget (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8) (Hty : m.Type' = MsgForgetLeader)
    (H : FollowerStepResult cfg id s m ents sv dropped s' cl) :
    dropped = false ∧ s' = { s with lead := W64 0 } := by
  unfold FollowerStepResult at H
  simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
    MsgForgetLeader, W32] at H
  simpa using H

theorem followerStepResult_rnoop (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8)
    (Hty : m.Type' = MsgTransferLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus)
    (H : FollowerStepResult cfg id s m ents sv dropped s' cl) : dropped = false ∧ s' = s := by
  unfold FollowerStepResult at H
  rcases Hty with h | h | h <;>
  simp only [h, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
    MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, W32] at H <;>
  simpa using H

theorem followerStepResult_timeout (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState)
    (cl : List w8) (Hty : m.Type' = MsgTimeoutNow)
    (H : FollowerStepResult cfg id s m ents sv dropped s' cl) :
    dropped = false ∧ HupOk cfg id s s' := by
  unfold FollowerStepResult at H
  simp only [Hty, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
    MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, W32] at H
  simpa using H

theorem candidateStepResult_rest (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) (cl : List w8)
    (Hty : m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨
      m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader)
    (H : CandidateStepResult cfg id s m ents sv dropped s' cl) : dropped = false ∧ s' = s := by
  unfold CandidateStepResult at H
  rcases Hty with h | h | h | h | h <;>
  simp only [h, MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp,
    MsgHeartbeatResp, MsgSnap, MsgPreVoteResp, MsgReadIndex, MsgReadIndexResp,
    MsgForgetLeader, MsgTransferLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, W32] at H <;>
  simpa using H

/-- A leader's step for these types: some sends `ReplOk` allows, `Match` kept, `lt` and the
`Progress` states free. -/
theorem leaderStepResult_rest (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (dropped : Bool) (s' : NState) (ctx : List w8)
    (Hty : m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨
      m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader)
    (Hr : s.role = .leader) (Hwf : NStateWf s)
    (H : LeaderStepResult cfg id s m ents dropped s' ctx) :
    dropped = false ∧ NStateWf s' ∧ Step cfg id (toPState s) [] (toPState s') ∧
      s'.logst = s.logst ∧ s'.term = s.term ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh := by
  have Hnp : m.Type' ≠ MsgProp := by rcases Hty with h | h | h | h | h <;> rw [h] <;> w32_ne
  unfold LeaderStepResult at H
  rw [ite_eq_right Hnp] at H
  obtain ⟨rfl, Hres⟩ := H
  unfold LeaderNonpropResult at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ |
    ⟨-, lt', ms, pvs, rfl, Hms, Hpm⟩
  rotate_right
  · refine ⟨rfl, Hwf, ?_, rfl, rfl, rfl, rfl⟩
    have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
    rw [toPState_prvals (sendMsgs { s with lt := lt' } ms) pvs (fun _ => Hpm), toPState_sendMsgs]
    exact Step.sendApps _ ms Hpr Hms
  all_goals exfalso
  all_goals rcases Hty with h | h | h | h | h <;> rw [h] at Hc
  all_goals first
    | exact absurd Hc (by w32_ne)
    | (rcases Hc with Hc | Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
    | (rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))

/-- `MsgForgetLeader` at a follower is `Step.abandon`: the follower's tally is empty. -/
theorem toPState_forget (s : NState) (Hr : s.role = .follower) (Hv : s.votes = ∅) :
    toPState { s with lead := W64 0 } = pbecomeFollower (toPState s) (toPState s).term (W64 0) := by
  simp [toPState, pbecomeFollower, Hr, Hv, proleRole]

theorem isMessage_stepdown (γ : RaftNames) (id : w64) (m : raftpb.Message) :
    ⊢ isMessage (GF := GF) γ (stepdownMsg id m) :=
  isMessage_free γ _ rfl

set_option hygiene false in
/-- The type-switch premises of `stepFollower`/`stepCandidate`/`stepLeader` that are about
other types: refuted by `Hty`. -/
local macro "ty_other" : tactic => `(tactic| (intro Hc; exfalso; rw [Hty] at Hc; first
  | exact absurd Hc (by w32_ne)
  | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne))
  | (rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
  | (rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
  | (rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))))

set_option hygiene false in
/-- The same, inside the precondition (a wand from the type). -/
local macro "ity_other" : tactic => `(tactic| (iintro %Hc; exfalso; rw [Hty] at Hc; first
  | exact absurd Hc (by w32_ne)
  | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne))
  | (rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))))

set_option hygiene false in
/-- `wp_Step_MsgLocal` at a follower. -/
local macro "local_follower" : tactic => `(tactic| (
  wp_apply _P.stepFollower cfg r id s m [] (zero_val _) [] [] (by simp [Hty])
      (by ty_other) (by ty_other) (by ty_other) (by ty_other) (by ty_other)
    $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · iframe Hphys
    isplitl []
    · ity_other
    isplitl []
    · ity_other
    isplitl []
    · iapply Hsnap0
    · ity_other
  first
    | (obtain ⟨rfl, rfl⟩ := followerStepResult_forget _ _ _ _ _ _ _ _ _ Hty Hres
       simp only [Bool.false_eq_true, ↓reduceIte]
       icases Herrn with %Herrn
       subst Herrn
       wp_auto
       iapply HΦ $$ %interface.nil %{ s with lead := W64 0 }
       iframe Hphys
       ipureintro
       refine ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, ?_⟩, rfl, NetFrame.of_logst rfl,
         TermStep.of_term rfl (fun _ => Int.le_refl _)⟩
       rw [toPState_forget s Hrole (Hfv Hrole)]
       exact Step.abandon _ (by rw [toPState_role, Hrole]; decide))
    | (obtain ⟨rfl, Hs1⟩ := followerStepResult_rnoop _ _ _ _ _ _ _ _ _ (by simp [Hty]) Hres
       subst s1
       simp only [Bool.false_eq_true, ↓reduceIte]
       icases Herrn with %Herrn
       subst Herrn
       wp_auto
       iapply HΦ $$ %interface.nil %s
       iframe Hphys
       ipureintro
       exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl, NetFrame.refl _,
    TermStep.refl _ _⟩)))

set_option hygiene false in
/-- `wp_Step_MsgLocal` at a candidate or pre-candidate: nothing. -/
local macro "local_candidate" : tactic => `(tactic| (
  wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) [] [] (by simp [Hty])
      (by ty_other) (by simp [Hrole]) (by ty_other) (by ty_other)
      (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
    $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · iframe Hphys
    isplitl []
    · ity_other
    isplitl []
    · iapply Hsnap0
    · ity_other
  obtain ⟨rfl, Hs1⟩ := candidateStepResult_rest _ _ _ _ _ _ _ _ _ Hty5 Hres
  subst s1
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  iapply HΦ $$ %interface.nil %s
  iframe Hphys
  ipureintro
  exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl, NetFrame.refl _,
    TermStep.refl _ _⟩))

set_option hygiene false in
/-- `wp_Step_MsgLocal` at a leader: `leaderStepResult_rest`. -/
local macro "local_leader" : tactic => `(tactic| (
  wp_apply _P.stepLeader cfg r id s m [] [] (by simp [Hty]) Hrole
      (by ty_other) (by ty_other) (by ty_other) (by ty_other) (by ty_other) (by ty_other)
    $$ [Hphys] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
  · iframe Hphys
    isplitl []
    · ity_other
    isplitl []
    · ity_other
    · ity_other
  obtain ⟨rfl, Hwf', Hst, Hl, Ht, Hpv, Hg⟩ :=
    leaderStepResult_rest _ _ _ _ _ _ _ _ Hty5 Hrole Hwf Hres
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  iapply HΦ $$ %interface.nil %s'
  iframe Hphys
  ipureintro
  exact ⟨Hwf', ⟨[], fun _ h => absurd h List.not_mem_nil, Hst⟩, rfl, NetFrame.of_logst Hl Hpv Hg,
    TermStep.of_term Ht (fun _ => by rw [Hl]; exact Int.le_refl _)⟩))

set_option hygiene false in
/-- A leader-transfer request at a follower (at the state `s`): forwarded, or dropped. -/
local macro "transfer_follower " h:term : tactic => `(tactic| (
  wp_apply _P.stepFollower cfg r id s m [] (zero_val _) [] [] (by simp [Hty])
      (by ty_other) (by ty_other) (by ty_other) (by ty_other)
      (fun _ => ⟨fun _ => ⟨$h, Hent, Hctx0⟩, fun h' => absurd h' (by rw [Hty]; w32_ne)⟩)
    $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · iframe Hphys
    isplitl []
    · ity_other
    isplitl []
    · ity_other
    isplitl []
    · iapply Hsnap0
    · ity_other
  obtain ⟨rfl, Hs1⟩ := followerStepResult_rnoop _ _ _ _ _ _ _ _ _ (by simp [Hty]) Hres
  subst s1
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  iapply HΦ $$ %interface.nil %s
  iframe Hphys
  ipureintro
  exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl, NetFrame.refl _,
    TermStep.refl _ _⟩))

set_option hygiene false in
/-- `MsgTimeoutNow` at a follower (at the state `s`): `hup(campaignTransfer)`. -/
local macro "timeout_follower" : tactic => `(tactic| (
  wp_apply _P.stepFollower cfg r id s m [] (zero_val _) [] [] (by simp [Hty])
      (by ty_other) (by ty_other) (by ty_other) (by ty_other)
      (fun _ => ⟨fun h' => absurd h' (by rw [Hty]; w32_ne), fun _ => ⟨Hnw, Hwf⟩⟩)
    $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
  · iframe Hphys
    isplitl []
    · ity_other
    isplitl []
    · ity_other
    isplitl []
    · iapply Hsnap0
    · ity_other
  obtain ⟨rfl, Hwf1, Hst1, Hl1, Ht1, Ht2, Hpv1, Hg1⟩ :=
    followerStepResult_timeout _ _ _ _ _ _ _ _ _ Hty Hres
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Herrn with %Herrn
  subst Herrn
  wp_auto
  iapply HΦ $$ %interface.nil %s1
  iframe Hphys
  ipureintro
  exact ⟨Hwf1, ⟨[], fun _ h => absurd h List.not_mem_nil, Hst1⟩, rfl, NetFrame.of_logst Hl1 Hpv1 Hg1,
    ⟨Ht1, fun h => absurd h (by rw [Hty]; w32_ne), fun _ _ h => absurd Hty h,
     fun _ => by rw [Hl1]; exact Int.le_refl _,
     fun _ => by have := Int.le_max_left (uint.Z s.term) (uint.Z m.Term'); omega⟩⟩))

/-- `MsgForgetLeader`, `MsgUnreachable`, `MsgSnapStatus`: local (`Term = 0`). -/
theorem wp_Step_MsgLocal (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    (m.Type' = MsgForgetLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus) →
    m.Term' = W64 0 →
    NStateWf s →
    (s.role = .follower → s.votes = ∅) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = stepdownMsg id m) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty3 Hterm Hwf Hfv
  have Hty5 : m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨
      m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader := by
    rcases Hty3 with h | h | h <;> simp [h]
  wp_start as Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_true Hterm]
  wp_auto
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso
    rcases Hty3 with h | h | h <;> rw [h] at Hc <;> exact absurd Hc (by w32_ne)
  rcases Hty3 with Hty | Hty | Hty <;> rw [Hty] <;> wp_auto
  all_goals
    wp_apply raft.wp_load_step $$ Hphys as Hphys
    rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
    cases Hrole : s.role <;> simp only [stepFuncOf]
  -- per type: a follower, a candidate, a leader, a pre-candidate
  · local_follower
  · local_candidate
  · local_leader
  · local_candidate
  · local_follower
  · local_candidate
  · local_leader
  · local_candidate
  · local_follower
  · local_candidate
  · local_leader
  · local_candidate

/-- The preamble's step-down to a later term, for a type outside the model. -/
theorem stepdown_rest (cfg : GSet w64) (id : w64) (s : NState) (m : raftpb.Message)
    (pvs : GMap w64 Progress) (Hgt : uint.Z s.term < uint.Z m.Term') :
    Step cfg id (toPState s) [stepdownMsg id m]
      (toPState { becomeFollower s m.Term' (W64 0) with prvals := pvs }) := by
  rw [toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs (by simp [becomeFollower]),
    toPState_becomeFollower]
  have H := Step.higherTerm (cfg := cfg) (id := id) (stepdownMsg id m) (toPState s) Hgt rfl
    (fun h => by simp [stepdownMsg, Msg.plain, fromLeader] at h)
  rw [show (if fromLeader (stepdownMsg id m).ty then (stepdownMsg id m).src else W64 0) = W64 0 by
    simp [stepdownMsg, Msg.plain, fromLeader]] at H
  exact H

/-- `MsgTransferLeader`. -/
theorem wp_Step_MsgTransferLeader (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgTransferLeader →
    m.Entries' = slice.nil →
    m.Context' = slice.nil →
    (m.Term' ≠ W64 0 → m.Term' = s.term → s.role = .follower → s.lead = W64 0) →
    (s.role = .follower → s.lead ≠ id) →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = stepdownMsg id m) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hent Hctx0 Htr Hlok Hwf
  have Hty5 : m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨
      m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader := by simp [Hty]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  wp_start as Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  by_cases Hz : m.Term' = W64 0
  · -- local: `r.step(r, m)`
    rw [decide_eq_true Hz]
    wp_auto
    rw [Hty]
    wp_auto
    wp_apply raft.wp_load_step $$ Hphys as Hphys
    rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
    cases Hrole : s.role <;> simp only [stepFuncOf]
    · transfer_follower (if h : s.lead = W64 0 then .inl h else .inr ⟨Hz, Hlok Hrole⟩)
    · local_candidate
    · local_leader
    · local_candidate
  rw [decide_eq_false Hz]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · -- a later term: step down (no leader adopted), then drop it, leaderless
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
        m [] (zero_val _) [] [] (by simp [Hty])
        (by ty_other) (by ty_other) (by ty_other) (by ty_other)
        (fun _ => ⟨fun _ => ⟨.inl rfl, Hent, Hctx0⟩, fun h' => absurd h' (by rw [Hty]; w32_ne)⟩)
      $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · iframe Hphys
      isplitl []
      · ity_other
      isplitl []
      · ity_other
      isplitl []
      · iapply Hsnap0
      · ity_other
    obtain ⟨rfl, Hs1⟩ := followerStepResult_rnoop _ _ _ _ _ _ _ _ _ (by simp [Hty]) Hres
    subst s1
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %{ becomeFollower s m.Term' (W64 0) with prvals := pvs }
    iframe Hphys
    ipureintro
    have Hfr := stepdown_frame (m := m) (s := s)
      (s' := { becomeFollower s m.Term' (W64 0) with prvals := pvs })
      (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl
    exact ⟨⟨rfl, rfl⟩, ⟨[stepdownMsg id m], by simp, stepdown_rest cfg id s m pvs Hgt⟩, rfl,
      Hfr.1, Hfr.2⟩
  rw [decide_eq_false Hgt]
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
  -- the current term: `r.step(r, m)`; a follower of the term has no leader (the premise)
  have Hteq : m.Term' = s.term := by word
  rw [decide_eq_false Hlt]
  wp_auto
  rw [Hty]
  wp_auto
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  cases Hrole : s.role <;> simp only [stepFuncOf]
  · transfer_follower (.inl (Htr Hz Hteq Hrole))
  · local_candidate
  · local_leader
  · local_candidate

/-- `MsgTimeoutNow`. -/
theorem wp_Step_MsgTimeoutNow (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message) :
    m.Type' = MsgTimeoutNow →
    uint.Z s.term + 1 < 2 ^ 64 →
    uint.Z m.Term' + 1 < 2 ^ 64 →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = stepdownMsg id m) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hnw Hnwm Hwf
  have Hty5 : m.Type' = MsgForgetLeader ∨ m.Type' = MsgTimeoutNow ∨ m.Type' = MsgUnreachable ∨
      m.Type' = MsgSnapStatus ∨ m.Type' = MsgTransferLeader := by simp [Hty]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  wp_start as Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  by_cases Hz : m.Term' = W64 0
  · rw [decide_eq_true Hz]
    wp_auto
    rw [Hty]
    wp_auto
    wp_apply raft.wp_load_step $$ Hphys as Hphys
    rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
    cases Hrole : s.role <;> simp only [stepFuncOf]
    · timeout_follower
    · local_candidate
    · local_leader
    · local_candidate
  rw [decide_eq_false Hz]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · -- a later term: step down (no leader adopted), then campaign
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
        m [] (zero_val _) [] [] (by simp [Hty])
        (by ty_other) (by ty_other) (by ty_other) (by ty_other)
        (fun _ => ⟨fun h' => absurd h' (by rw [Hty]; w32_ne), fun _ => ⟨Hnwm, ⟨rfl, rfl⟩⟩⟩)
      $$ [Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · iframe Hphys
      isplitl []
      · ity_other
      isplitl []
      · ity_other
      isplitl []
      · iapply Hsnap0
      · ity_other
    obtain ⟨rfl, Hwf1, Hst1, Hl1, Ht1, Ht2, Hpv1, Hg1⟩ :=
      followerStepResult_timeout _ _ _ _ _ _ _ _ _ Hty Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s1
    iframe Hphys
    ipureintro
    have Hfr := stepdown_frame (m := m) (s := s)
      (s' := { becomeFollower s m.Term' (W64 0) with prvals := pvs })
      (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl
    refine ⟨Hwf1, ⟨[stepdownMsg id m] ++ [], by simp,
      .trans _ _ _ _ _ (stepdown_rest cfg id s m pvs Hgt) Hst1⟩, rfl,
      Hfr.1.trans (NetFrame.of_logst Hl1 Hpv1 Hg1), ?_⟩
    refine ⟨Int.le_trans (Int.le_of_lt Hgt) Ht1, fun h => absurd h (by rw [Hty]; w32_ne),
      fun _ _ h => absurd Hty h, fun _ => ?_, fun _ => ?_⟩
    · rw [Hl1]; exact Int.le_refl _
    · have := Int.le_max_right (uint.Z s.term) (uint.Z m.Term')
      have h2 : uint.Z ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).term
          = uint.Z m.Term' := rfl
      omega
  rw [decide_eq_false Hgt]
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
  rw [decide_eq_false Hlt]
  wp_auto
  rw [Hty]
  wp_auto
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  cases Hrole : s.role <;> simp only [stepFuncOf]
  · timeout_follower
  · local_candidate
  · local_leader
  · local_candidate

end StepProof

end branches

end EtcdGrove
end Perennial
