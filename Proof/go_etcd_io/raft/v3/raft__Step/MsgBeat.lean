/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgBeat.v.

`Step`'s `MsgBeat` branch, in its own file so that it checks in parallel with the
others. Proof structure, not specification: no `Module Type`, no `Parameter`; only
`Proof/raft__Step.lean` may import this module.

Lean notes: the branch lemma takes the callee specs (Rocq's functor argument
`P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
section variable `c` as its second.
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

set_option maxHeartbeats 1000000 in
/-- `MsgBeat` is local (`m.Term = 0`: `tickHeartbeat` builds it), so the term preamble
is skipped; it is none of the type switch's four cases, so `r.step(m)` runs.
`stepFollower` and `stepCandidate` have no arm for it (`StepC.refl`); `stepLeader` runs
`bcastHeartbeat`, whose heartbeats are `StepC.beat`'s (`leader_beat_step`). -/
theorem wp_Step_MsgBeat (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (ents : List EntryM) (R : StepG GF) :
    m.Type' = MsgBeat →
    m.Term' = W64 0 →
    NStateWf s →
    -- (2026-10-29, stage U7) a leader's term past `0` (`bcastHeartbeat`'s stamp)
    (s.role = .leader → s.term ≠ W64 0) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (2026-11-10, Q8 stage 1 slice 11) the caller's resource and `Step`'s gates
        "HG" ∷ R.G ∗ "Hgates" ∷ stepGates c r id s m ents sn ctx rs R }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        -- (Q8 stage 1 slice 13) the end state on the path (`StepEnd`, `LemmasStepGates.lean`)
        "%Hend" ∷ ⌜StepEnd c id m ents ctx s s'⌝ ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id B m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ ∗
        "HG" ∷ stepOut R s'.outbox }} := by
  intro Hty Hterm Hwf HLT
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_recv_gate_ns
  try wp_auto
  wp_get _Q
  -- `m.Term = 0` (a local message), so the term preamble is skipped
  rw [decide_eq_true Hterm]
  wp_auto
  -- the type switch: none of its four cases, so `r.step(m)`
  wp_drive _Q
  -- a local message: the preamble skipped
  have hnbf : ¬ PreBF m s := PreBF.of_zero Hterm
  imod preGate_nobf c r id s m _ _ (.inl Hterm) hnbf $$ Hgpre HG with HG
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  have Hty3 : m.Type' = MsgBeat ∨ m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨
    m.Type' = MsgCheckQuorum :=
    .inl Hty
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  have Hsnap0 : ∀ (P : IProp GF), ⊢ (⌜m.Type' = MsgSnap⌝ -∗ P : IProp GF) := fun P => by
    iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
  cases Hrole : s.role
  · -- Follower: no `MsgBeat` arm
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    gates_fol
    wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx R.G1 R.GE
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne)) (by intro Hc; first | (exfalso; rcases Hc with Hc | Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne)) | (exfalso; rcases Hc with Hc | Hc | Hc <;> simp_all [MsgApp, MsgHeartbeat, MsgSnap]) | simp_all [becomeFollower, resetTo, resetTo0])
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (by notfwd_tac) Hgok.1 Hgok.2.1 $$ [$Hphys Hm $Hsrc0 $HG $Hfg] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn, HGo⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    ihave HG := stepOut_or R _ _ $$ HGo
    obtain ⟨rfl, rfl, Hs1⟩ := followerStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    try phys_out
    iapply HΦ $$ %interface.nil %s
    iframe Hphys HG
    ipureintro
    exact ⟨by end_nobf, Hwf, StepCD.frame (.refl _) (RFrame.refl _), rfl, keep_frame rfl rfl rfl rfl rfl⟩
  · -- Candidate: no `MsgBeat` arm either
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    gates_cand
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx R.G1 R.GE R.Gf R.Gb1 R.Gb2 0
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inl Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      Hgok.1 Hgok.2.2.1 Hgok.2.1 $$ [$Hphys $Hrc00 Hm $Hsrc0 $HG $Hcg] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn, HGo⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    ihave HG := stepOut_or R _ _ $$ HGo
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    try phys_out
    iapply HΦ $$ %interface.nil %s
    iframe Hphys HG
    ipureintro
    exact ⟨by end_nobf, Hwf, StepCD.frame (.refl _) (RFrame.refl _), rfl, keep_frame rfl rfl rfl rfl rfl⟩
  · -- Leader: `bcastHeartbeat`
    simp only [stepFuncOf]
    imod (preceipt_zero (GF := GF)) with #Hrc00
    gates_lead
    wp_apply _P.stepLeader c r id s ml m ents sn ctx rs 0 R.G1 R.GE R.Gp1 R.Gp2 R.Gc (.inr (.inl Hty)) Hrole (fun _ => HLT Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (by p3_tac) Hgok.2.1 Hgok.2.2.2.1 Hgok.2.2.2.2 $$ [$Hphys $Hrc00 Hm $HG $Hlg] as %err %s' %dropped ⟨Hphys, -, %Hres, Herrn, HGo⟩
    · isplitl [Hm]
      · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    ihave HG := stepOut_leader R _ _ _ _ $$ HGo
    obtain ⟨rfl, Hwf', Hstep, Hl, Ht, Hpv, Hg⟩ :=
      leader_beat_step (B := B) c id s m ents dropped s' Hrole Hty Hwf Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    try phys_out
    iapply HΦ $$ %interface.nil %s'
    iframe Hphys HG
    ipureintro
    exact ⟨by end_nobf, Hwf', Hstep, rfl, keep_frame_logst Ht Hl Hpv Hg (.mk' fun h => absurd h (LeaderStepResultC.not_precand Hrole Hres))⟩
  · -- PreCandidate (2026-10-04), as a candidate: no `MsgBeat` arm either
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    gates_cand
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx R.G1 R.GE R.Gf R.Gb1 R.Gb2 0
        (.inr (.inr (.inr (.inr (.inl Hty3)))))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inr Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      Hgok.1 Hgok.2.2.1 Hgok.2.1 $$ [$Hphys $Hrc00 Hm $Hsrc0 $HG $Hcg] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn, HGo⟩
    · iapply msgIn_nonprop (by rw [Hty]; w32_ne) $$ Hm
    ihave HG := stepOut_or R _ _ $$ HGo
    obtain ⟨rfl, rfl, Hs1⟩ := candidateStepResult_noop _ _ _ _ _ _ _ _ Hty3 Hres
    rw [Hs1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    try phys_out
    iapply HΦ $$ %interface.nil %s
    iframe Hphys HG
    ipureintro
    exact ⟨by end_nobf, Hwf, StepCD.frame (.refl _) (RFrame.refl _), rfl, keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
