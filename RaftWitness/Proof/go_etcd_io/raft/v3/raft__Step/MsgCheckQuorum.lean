/- `Step`'s `MsgCheckQuorum` branch (2026-10-17, `CheckQuorum` on; Lean-first), in its own file
so that it checks in parallel with the others; only `Proof/raft__Step.lean` may import this
module. `tickHeartbeat` steps it at a leader past its election timeout; it is local (`Term = 0`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas
public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

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

/-- (2026-10-20, witness support) The excluded voter of a configuration with a witness's epoch:
the witness itself (`0`), or an incoming voter that is not the witness (`StepC.newSub`'s). -/
theorem epochRsx_wf {V0 V1 : GSet w64} {w : w64} {em : EpochM} (Hw : w ≠ W64 0)
    (H : EpochWF V0 V1 w (W64 0) em) :
    epochRsx em = W64 0 ∨ (epochRsx em ∈ V0 ∧ epochRsx em ≠ w) := by
  rcases H with ⟨h, -⟩ | ⟨-, ⟨hw, hx, -⟩, -⟩
  · exact absurd h Hw
  · unfold epochRsx
    by_cases he : em.rs0.excl = em.rs0.wit
    · simp [he]
    · rw [if_neg he]; right
      rcases hx with hx | ⟨hin, hne, hnz⟩
      · exact absurd hx he
      · refine ⟨hin, ?_⟩
        by_cases hwV : w ∈ V0
        · rw [if_pos hwV] at hw; rw [← hw]; exact hne
        · rw [if_neg hwV] at hw; exact absurd hw hnz

/-- (2026-10-20, witness support) The check-quorum's new subterm in both models: statically
`StepC.newSub` at any ghost prefix of the subterm (`NState.scp`), dynamically `StepR.newSub` at
the prefix of the configuration index, which `Step` then sets (`ownRaftPhysC_scp`). -/
def CQNewSubOk (c : CfgM) (id : w64) (B : Int) (s s' : NState) : Prop :=
  (∀ P, StepC c id B (toPState s) [] (toPState { s' with scp := P })) ∧
  ∀ (Adm : List EntryM → CCState → Prop) (dec : CCDec) (g : RGh), g.cfg.cfg = c →
    StepR Adm dec id B (rOf s g) []
      (rOf { s' with scp := (rOf s g).full.take (rOf s g).cidx } g)

/-- `stepLeader` on `MsgCheckQuorum` (2026-10-17, `CheckQuorum` on): the leader stays
(`StepC.refl`, its `Match` values unchanged) or steps down at its term (`StepC.stepDown`, and
`StepR.stepDown` in the dynamic model: `reset` clears `pendingConfIndex`); or (2026-10-20,
witness support), the quorum active at a configuration with a witness, starts a new subterm
(`StepC.newSub`, its entry appended up to `B`; the leader's subterm below its last index,
`PSubOk`, so the next one does not wrap; `CQNewSubOk`). The term, the pre-vote setting and the
ghost bounds are kept, and the log but for the new subterm's entry. -/
theorem leader_checkQuorum_step (c : CfgM) {ctx : List w8} (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (dropped : Bool) (s' : NState)
    (Hr : s.role = .leader) (Hty : m.Type' = MsgCheckQuorum) (Hwf : NStateWf s)
    (Hps : PSubOk (toPState s))
    (HB : CQNewSub c id s s' → plogLastIndexZ (toPState s).base (toPState s).log + 1 ≤ B)
    (HB64 : B < 2 ^ 64)
    (H : LeaderStepResultC c id s m ents dropped s' ctx) :
    dropped = false ∧ NStateWf s' ∧ (StepCD c id B m s [] s' ∨ CQNewSubOk c id B s s') ∧
      (∃ es, s'.logst = logAppend s.logst es) ∧ s'.term = s.term ∧ s'.prevote = s.prevote ∧
      s'.gh = s.gh := by
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, Hr]; rfl
  have Hl0 : logAppend s.logst [] = s.logst := by simp [logAppend]
  unfold LeaderStepResultC at H
  rw [ite_eq_right (by rw [Hty]; w32_ne)] at H
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  have Hres0 := Hres
  unfold LeaderNonpropResultC at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ |
    ⟨-, ⟨pvs, ⟨Hpm, rfl⟩ | rfl⟩ | Hcq⟩
  rotate_right 3
  · -- the leader stays
    refine ⟨?_, .inl (StepCD.frame ?_ ⟨rfl, rfl, fun _ => ⟨Hr, rfl⟩⟩), ⟨[], Hl0.symm⟩, rfl, rfl,
      rfl⟩
    · exact Hwf
    · rw [toPState_prvals s pvs (fun _ => Hpm)]
      exact .refl _
  · -- the step-down
    refine ⟨⟨rfl, rfl⟩, .inl ⟨?_, fun Adm dec g _ _ => ⟨g.cidx, .inl rfl, ?_⟩⟩, ⟨[], Hl0.symm⟩,
      rfl, rfl, rfl⟩
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
  · -- (2026-10-20, witness support) a new subterm
    have HBn := HB Hcq
    obtain ⟨pvs, em', Hcw, -, Hchg, Hpm, rfl⟩ := Hcq
    have Hsub : em'.sub = s.ep.sub + W64 1 := Hchg.1
    have Hsub0 : (toPState s).sub = s.ep.sub := by simp [toPState, Hr]
    have Hnw : uint.Z (toPState s).sub + 1 < 2 ^ 64 := by have := Hps Hpr; word
    have Hne : s.ep.sub + W64 1 ≠ W64 0 := by rw [Hsub0] at Hnw; intro h; word
    refine ⟨⟨Hwf.1.trans (by simp [subtermStart, sendMsgs, Hr]), Hwf.2⟩, .inr ⟨?_, ?_⟩,
      ⟨[stampS s.term em'.sub (logLast s.logst) 0 (zero_val EntryM)],
        by simp [subtermStart, sendMsgs, logAppend]⟩, rfl, rfl, rfl⟩
    · -- `StepC.newSub`, excluding the new epoch's voter, at the subterm's ghost prefix
      intro P
      have HC := StepC.newSub (c := c) (id := id) (B := B) (toPState s) (epochRsx em') P Hpr
        Hcw (epochRsx_wf Hcw Hchg.2.1) Hnw HBn
      refine cast ?_ HC
      congr 1
      simp only [toPState, subtermStart, sendMsgs, selfAck, psendMsgs, pappend, pselfAck,
        plastIndex, plogLastIndexZ, logLast, Hr, reduceCtorEq, ↓reduceIte, Hsub, Hpm, logAppend,
        Hne, ne_eq, not_false_eq_true, and_self,
        List.mapIdx_cons, List.mapIdx_nil, List.length_append, List.append_assoc,
        List.length_cons, List.length_nil, Int.natCast_add]
      simp [Int.add_assoc]
    · -- `StepR.newSub`, at the prefix of the configuration index
      intro Adm dec g hc
      have Hrl : (rOf s g).p.role = .leader := by simp [rOf, toPState, Hr, proleRole]
      have Hrx := epochRsx_wf Hcw Hchg.2.1
      rw [← hc] at Hcw Hrx
      have HR := StepR.newSub (Adm := Adm) (dec := dec) (id := id) (B := B) (rOf s g) (epochRsx em')
        Hrl Hcw Hrx Hnw HBn
      refine cast ?_ HR
      congr 1
      simp only [rOf, pciR, toPState, subtermStart, sendMsgs, selfAck, psendMsgs, pappend,
        pselfAck, plastIndex, plogLastIndexZ, logLast, Hr, reduceCtorEq, ↓reduceIte, Hsub, Hpm,
        logAppend, Hne, ne_eq, not_false_eq_true, and_self,
        List.mapIdx_cons, List.mapIdx_nil, List.length_append, List.append_assoc,
        List.length_cons, List.length_nil, Int.natCast_add]
      simp [Int.add_assoc]
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
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (ents : List EntryM) (k0 : Nat) :
    m.Type' = MsgCheckQuorum →
    m.Term' = W64 0 →
    NStateWf s →
    -- (2026-10-20, witness support) a leader's term is nonzero (`ownRaftGhost_term_nz`), and its
    -- subterm below its last index (`PSubOk`, the ghost state's); the log's last index fits a
    -- word (the ghost state's)
    (s.role = .leader → s.term ≠ W64 0) →
    PSubOk (toPState s) →
    plogLastIndexZ (toPState s).base (toPState s).log < 2 ^ 64 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (2026-10-20, witness support) a time receipt, raised by one by a new subterm's entry
        "#Hrc" ∷ ⧖ k0 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (B : Int), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        -- (2026-10-20) the bound `B` of the indices the step creates: the log's last index, or
        -- the next one for a new subterm's entry, which the raised receipt covers
        "%HBb" ∷ ⌜plogLastIndexZ (toPState s).base (toPState s).log ≤ B ∧
          B ≤ plogLastIndexZ (toPState s).base (toPState s).log + 1 ∧ B < 2 ^ 64⌝ ∗
        "Hrcb" ∷ (⌜plogLastIndexZ (toPState s).base (toPState s).log < B⌝ -∗ ⧖ (k0 + 1)) ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- (2026-10-20) or a new subterm, whose ghost prefix `Step` sets (`CQNewSubOk`)
        "%Hrefines" ∷ ⌜StepCD c id B m s [] s' ∨ CQNewSubOk c id B s s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hterm Hwf Hlnz Hps HL
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
    wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := followerStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s %(plogLastIndexZ (toPState s).base (toPState s).log)
    iframe Hphys
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
    isplitr
    · iintro %h; exact absurd h (Int.lt_irrefl _)
    ipureintro
    exact ⟨Hwf, .inl (StepCD.frame (.refl _) (RFrame.refl _)), rfl, keep_frame rfl rfl rfl rfl rfl⟩
  · -- Candidate: no `MsgCheckQuorum` arm either
    simp only [stepFuncOf]
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
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s %(plogLastIndexZ (toPState s).base (toPState s).log)
    iframe Hphys
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
    isplitr
    · iintro %h; exact absurd h (Int.lt_irrefl _)
    ipureintro
    exact ⟨Hwf, .inl (StepCD.frame (.refl _) (RFrame.refl _)), rfl, keep_frame rfl rfl rfl rfl rfl⟩
  · -- Leader: the quorum check, perhaps a step-down at its term
    simp only [stepFuncOf]
    wp_apply _P.stepLeader c r id s ml m ents sn ctx rs k0 (by simp [Hty]) Hrole
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
        (fun _ => Hlnz Hrole)
      $$ [$Hphys $Hrc Hm] as %err %s' %dropped ⟨Hphys, Hrcl, %Hres, Herrn⟩
    · isplitl [Hm]
      · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    have Hnp : m.Type' ≠ MsgProp := by rw [Hty]; w32_ne
    -- the bound: one past the last index for a new subterm's entry, the last index otherwise;
    -- the new log does not wrap (`ownRaftLog`'s `Hnowrap`)
    icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
    icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnw, Hlog⟩
    ihave Hphys := Hback $$ Hlog
    have HL1 : CQNewSub c id s s' → plogLastIndexZ (toPState s).base (toPState s).log + 1 < 2 ^ 64 := by
      intro Hcq
      have Hu := CQNewSub.uents Hcq
      obtain ⟨pvs, em', -, -, -, -, rfl⟩ := Hcq
      simp only [subtermStart, sendMsgs, logAppend] at Hnw Hu
      simp only [plogLastIndexZ, toPState, List.length_append] at Hu ⊢
      simp only [List.length_append] at Hnw
      push_cast at Hnw Hu ⊢
      omega
    have : Decidable (CQNewSub c id s s') := Classical.propDecidable _
    let B : Int := if CQNewSub c id s s' then plogLastIndexZ (toPState s).base (toPState s).log + 1
      else plogLastIndexZ (toPState s).base (toPState s).log
    have HBn : CQNewSub c id s s' → plogLastIndexZ (toPState s).base (toPState s).log + 1 ≤ B :=
      fun h => by simp only [B, h, ↓reduceIte]; exact Int.le_refl _
    have HBb : plogLastIndexZ (toPState s).base (toPState s).log ≤ B ∧
        B ≤ plogLastIndexZ (toPState s).base (toPState s).log + 1 ∧ B < 2 ^ 64 := by
      by_cases h : CQNewSub c id s s'
      · simp only [B, h, ↓reduceIte]; have := HL1 h; omega
      · simp only [B, h, ↓reduceIte]; omega
    obtain ⟨rfl, Hwf', Hstep, ⟨es, Hl⟩, Ht, Hpv, Hg⟩ :=
      leader_checkQuorum_step (B := B) c id s m ents dropped s' Hrole Hty Hwf Hps HBn HBb.2.2 Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s' %B
    iframe Hphys
    isplitr
    · ipureintro; exact HBb
    isplitl [Hrcl]
    · iintro %h
      by_cases Hcq : CQNewSub c id s s'
      · have e : (k0 + if m.Type' = MsgProp then ents.length else 1) = k0 + 1 := by
          rw [if_neg Hnp]
        rw [← e]
        iapply Hrcl $$ %(Or.inr ⟨Hty, Hcq⟩)
      · exfalso; simp only [B, Hcq, ↓reduceIte] at h; exact Int.lt_irrefl _ h
    ipureintro
    exact ⟨Hwf', Hstep, rfl, keep_frame Ht (by rw [Hl]; rfl) (by rw [Hl]; rfl) (by rw [Hl]; rfl)
      (by rw [Hl]; rfl) (by rw [Hl]; rfl) (by rw [Hl]; rfl) (by rw [Hl]; rfl) Hpv Hg
      (fun h => absurd h (LeaderStepResultC.not_precand Hrole Hres)) (by rw [Hl]; rfl)
      (by rw [Hl]; rfl)⟩
  · -- PreCandidate, as a candidate: no `MsgCheckQuorum` arm either
    simp only [stepFuncOf]
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
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ $$ %interface.nil %s %(plogLastIndexZ (toPState s).base (toPState s).log)
    iframe Hphys
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
    isplitr
    · iintro %h; exact absurd h (Int.lt_irrefl _)
    ipureintro
    exact ⟨Hwf, .inl (StepCD.frame (.refl _) (RFrame.refl _)), rfl, keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
