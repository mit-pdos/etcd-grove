/- `Step`'s `MsgCheckQuorum` branch (2026-10-17, `CheckQuorum` on; Lean-first), in its own file
so that it checks in parallel with the others; only `Proof/raft__Step.lean` may import this
module. `tickHeartbeat` steps it at a leader past its election timeout; it is local (`Term = 0`).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas
public import Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

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

/-- `stepLeader` on `MsgCheckQuorum` (2026-10-17, `CheckQuorum` on): the leader stays
(`StepC.refl`, its `Match` values unchanged) or steps down at its term (`StepC.stepDown`, and
`StepR.stepDown` in the dynamic model: `reset` clears `pendingConfIndex`). The log, the term, the
pre-vote setting and the ghost bounds are kept. -/
theorem leader_checkQuorum_step (c : CfgM) {ctx : List w8} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (dropped : Bool) (s' : NState)
    (Hr : s.role = .leader) (Hty : m.Type' = MsgCheckQuorum) (Hwf : NStateWf s)
    (H : LeaderStepResultC c id s m ents dropped s' ctx) :
    dropped = false ∧ NStateWf s' ∧ StepCD c id B m s [] s' ∧
      s'.logst = s.logst ∧ s'.term = s.term ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  unfold LeaderStepResultC at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResultC at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ |
    ⟨-, pvs, ⟨Hpm, rfl⟩ | rfl⟩
  rotate_right 2
  · -- the leader stays
    refine ⟨?_, StepCD.frame ?_ ⟨rfl, rfl, fun _ => ⟨Hr, rfl⟩⟩, rfl, rfl, rfl, rfl⟩
    · exact Hwf
    · rw [toPState_prvals s pvs (fun _ => Hpm)]
      exact .refl _
  · -- the step-down
    refine ⟨⟨rfl, rfl⟩, ⟨?_, fun Adm dec g _ _ => ⟨g.cidx, .inl rfl, ?_⟩⟩, rfl, rfl, rfl, rfl⟩
    · rw [toPState_prvals_nl _ pvs (by simp [becomeFollower]), toPState_becomeFollower]
      exact .stepDown _ Hpr
    · have Hrl : (rOf s g).p.role = .leader := by simp [rOf, toPState, Hr, proleRole]
      have HR := StepR.stepDown (Adm := Adm) (dec := dec) (id := id) (B := B) (rOf s g) Hrl
      have e : RState.mk (pbecomeFollower (rOf s g).p (rOf s g).p.term (W64 0))
          (rOf s g).applied (W64 0) (rOf s g).snap (rOf s g).cidx (rOf s g).cfg (rOf s g).fp =
          rOf ({ becomeFollower s s.term (W64 0) with prvals := pvs } : NState)
            { g with cidx := g.cidx } := by
        have h1 := toPState_prvals (becomeFollower s s.term (W64 0)) pvs
          (fun h => by simp [becomeFollower] at h)
        have h2 := toPState_becomeFollower s s.term (W64 0)
        unfold rOf
        rw [h1, h2]
        simp [pciR, becomeFollower, toPState, resetTo0, resetTo]
      rw [e] at HR
      exact HR
  all_goals
    exfalso; rw [Hty] at Hc; revert Hc
    simp only [MsgCheckQuorum, MsgVoteResp, MsgApp, MsgHeartbeat, MsgPreVoteResp,
      MsgReadIndexResp, MsgBeat, MsgHeartbeatResp,MsgCheckQuorum, MsgReadIndex, MsgAppResp, MsgForgetLeader,
      MsgTimeoutNow, MsgUnreachable, MsgSnapStatus, MsgTransferLeader, _root_.or_false,
      _root_.false_or, _root_.or_self]
    word

set_option maxHeartbeats 1000000 in
/-- `MsgCheckQuorum` is local (`m.Term = 0`: `tickHeartbeat` builds it), so the term preamble
is skipped; it is none of the type switch's four cases, so `r.step(m)` runs.
`stepFollower` and `stepCandidate` have no arm for it (`StepC.refl`); `stepLeader` runs
the quorum check (`leader_checkQuorum_step`). -/
theorem wp_Step_MsgCheckQuorum (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (ents : List EntryM) :
    m.Type' = MsgCheckQuorum →
    m.Term' = W64 0 →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id B m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hterm Hwf
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  -- `m.Term = 0` (a local message), so the term preamble is skipped
  rw [decide_eq_true Hterm]
  wp_auto
  -- the type switch: none of its four cases, so `r.step(m)`
  wp_drive _Q
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨
    m.Type' = MsgCheckQuorum :=
    .inr (.inr (.inr Hty))
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  cases Hrole : s.role
  · -- Follower: no `MsgCheckQuorum` arm
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (by notfwd_tac) $$ [$Hphys Hm $Hsrc0] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := followerStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, StepCD.frame (.refl _) (RFrame.refl _), rfl, keep_frame rfl rfl rfl rfl rfl⟩
  · -- Candidate: no `MsgCheckQuorum` arm either
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
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
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, StepCD.frame (.refl _) (RFrame.refl _), rfl, keep_frame rfl rfl rfl rfl rfl⟩
  · -- Leader: the quorum check, perhaps a step-down at its term
    simp only [stepFuncOf]
    imod (preceipt_zero (GF := GF)) with #Hrc00
    wp_apply _P.stepLeader c r id s ml m ents sn ctx rs 0 (by simp [Hty]) Hrole
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys $Hrc00 Hm] as %err %s' %dropped ⟨Hphys, -, %Hres, Herrn⟩
    · isplitl [Hm]
      · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    obtain ⟨rfl, Hwf', Hstep, Hl, Ht, Hpv, Hg⟩ :=
      leader_checkQuorum_step (B := B) c id s m ents dropped s' Hrole Hty Hwf Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s'
    iframe Hphys
    ipureintro
    exact ⟨Hwf', Hstep, rfl, keep_frame_logst Ht Hl Hpv Hg (.mk' fun h => absurd h (LeaderStepResultC.not_precand Hrole Hres))⟩
  · -- PreCandidate, as a candidate: no `MsgCheckQuorum` arm either
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
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
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, StepCD.frame (.refl _) (RFrame.refl _), rfl, keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
