/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVoteResp.v.

One branch of `Step`'s proof, in its own file so that the branches check in parallel
-- each is a few minutes of `wp_auto` over the same 100k-node body, and in one file they
ran back to back.

This is **proof structure, not specification**: `Step` has exactly one spec, in
`Spec/raft__Step.lean`, and this module has no `Module Type` and no `Parameter`.
Only `Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import
this module; see `notes/decisions.md` (2026-09-17, and 2026-09-18 for why the helpers
moved out of the top-level directory).

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
* Rocq's `Local Ltac wp_load_step` (the load of `r.step` in `r.step(r, m)`, bound by
  hand with `wp_bind` because `wp_apply` did not find it in the function position of an
  application, 2026-09-24) is not ported; `MsgBeat.lean` uses
  `wp_apply raft.wp_load_stepC $$ Hphys as Hphys` there, and so does this proof.
* Rocq's hoisted `bool_decide` facts (`Hn17`, `Hn5`, …) are not needed: as in
  `MsgApp_gt.lean`, `repeat (wp_gets; rw [Hty]; try wp_auto)` evaluates each type test.
* `ite_pos`/`ite_neg` are local helpers for the `if`s of `FollowerStepResult` etc.

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by its getters (`wp_gets`, `ElectionLemmas.lean`), and handed whole to the
`stepX` callee (their phase-2 specs take it as `msgIn`, with its real `ents`/`ctx`; until now
`[]`, since they did not read them for this type).
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.ElectionLemmas
public import Proof.ReceiptTactics

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

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- `if` on a decided condition (Mathlib's `if_pos`/`if_neg`, deprecated here). -/
private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- A candidate's tally keeps the term and `NetFrame`'s fields: a win's `becomeLeader`
appends to the unstable entries only. -/
private theorem voteRespResult_frame (id : w64) (s : NState) (src : w64)
    (reject won lost : Bool) (ms : List Msg) (pvs : GMap w64 Progress) (m : MessageM)
    (em : EpochM) :
    NetFrame s { voteRespResult id s src reject won lost ms with prvals := pvs, ep := em } ∧
    TermStep m s { voteRespResult id s src reject won lost ms with prvals := pvs, ep := em } := by
  unfold voteRespResult
  split
  · exact keep_frame rfl rfl rfl rfl rfl
  · split
    · exact keep_frame rfl rfl rfl rfl rfl
    · exact keep_frame rfl rfl rfl rfl rfl

set_option maxHeartbeats 2000000 in
/-- `MsgVoteResp`: the term preamble, then `r.step(m)`.

The one branch where all three `stepX` can run, so it is also the one that needs the
`r.step` field pinned to the role: `raft.wp_load_stepC` loads `s.stepfn`, and `NStateWf`
says it is `stepFuncOf s.role` -- without that there is nothing to apply at
`r.step(m)`. Three term cases, and the third splits three ways:

- `m.Term > r.Term`: a `VoteResp` is not `fromLeader`, so the preamble runs
  `becomeFollower(m.Term, None)` rather than adopting a leader. The role is `follower`
  afterwards, so `r.step` is `stepFollower`, which has no `MsgVoteResp` arm. One
  `StepC.higherTerm`.
- `m.Term < r.Term`: with `checkQuorum` and `preVote` both off, and a `MsgVoteResp`
  being neither `MsgPreVote` nor `MsgStorageAppendResp`, every arm of the chain is
  skipped but the last, which only logs. Then `return nil`. `StepC.refl`, with
  `recv = []` -- the message is dropped, which the model always permits.
- `m.Term = r.Term`: straight to the type switch's default arm. `stepFollower` and
  `stepLeader` only read, so again `StepC.refl`; `stepCandidate` records the vote and
  may win or lose in the same call, which is `StepC.recordVote` followed by `StepC.win` /
  `StepC.lose`, on its `won`/`lost` flags. -/
theorem wp_Step_MsgVoteResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (k0 : Nat) :
    m.Type' = MsgVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `stepCandidate` needs it; `Step` is the outermost caller
    NStateWf s →
    -- (2026-10-18, D19b stage 5) the log's last index fits a word (the ghost state's)
    plogLastIndexZ (toPState s).base (toPState s).log < 2 ^ 64 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the message, as `Step` received it
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (2026-10-18, D19b stage 5) a time receipt, raised by one (the step's first resolution)
        "#Hrc" ∷ ⧖ k0 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (B : Int), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        -- (2026-10-18, D19b stage 5) the bound `B` of the indices the step creates: the log's last
        -- index, or the next one for a win's entry, which the raised receipt covers
        "%HBb" ∷ ⌜plogLastIndexZ (toPState s).base (toPState s).log ≤ B ∧
          B ≤ plogLastIndexZ (toPState s).base (toPState s).log + 1 ∧ B < 2 ^ 64⌝ ∗
        "#Hrcb" ∷ ⧖ (k0 + 1) ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .voteResp m ents) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hwf HL
  have Hnpv : m.Type' ≠ MsgPreVoteResp := by rw [Hty]; w32_ne
  have Hnprop : m.Type' ≠ MsgProp := by rw [Hty]; w32_ne
  wp_start as ⟨Hphys, Hm, #Hrc⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  wp_gets
  rw [decide_eq_false Hnn]
  wp_auto
  wp_gets
  wp_apply +noauto _P.traceReceiveMessage
  -- (2026-10-18, D19b stage 5) the step's receipt: the next resolution (a getter's)
  wp_raise_receipt Hrc
  try wp_auto
  wp_gets
  rw [decide_eq_false Hterm]
  wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · rw [decide_eq_true Hgt]
    wp_auto
    repeat (wp_gets; rw [Hty]; try wp_auto)
    -- "received a message with higher term"
    wp_gets
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_gets
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    wp_gets
    wp_raft_logC
    repeat (wp_gets; rw [Hty]; try wp_auto)
    -- a `MsgVoteResp` is not from a leader: `becomeFollower(m.Term, None)`
    wp_gets
    wp_apply _P.becomeFollower _ _ _ _ _ _ (by exact Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
    repeat (wp_gets; rw [Hty]; try wp_auto)
    -- the default arm, `r.step(m)`: the role is now follower
    wp_gets
    wp_apply raft.wp_load_stepC $$ Hphys as Hphys
    have Hsf : ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).stepfn =
        functions stepFollower [] := rfl
    wp_gets
    rw [Hsf]
    wp_gets
    wp_apply _P.stepFollower c ∅ r id { becomeFollower s m.Term' (W64 0) with prvals := pvs }
        ml m ents sn rs (zero_val _) ctx (.inl Hty)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · rw [ite_neg Hnprop]; iexact Hm
    have Hc1 := (FollowerStepResultC.cfg (by nonsnap Hty) Hres).symm
    unfold FollowerStepResultC at Hres
    replace Hres := Hres.2
    subst Hc1
    wp_gets
    rw [ite_pos Hty] at Hres
    obtain ⟨rfl, rfl⟩ := Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ
    iframe Hphys
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
    isplitr
    · iexact Hrc
    ipureintro
    refine ⟨⟨rfl, rfl⟩, ⟨[absMsg .voteResp m ents], by simp, StepCD.frame ?_ (by rframe)⟩, rfl,
      RespStep.of_fresh Hnpv (Int.le_of_lt Hgt), stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
    wp_gets
    rw [toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs (by simp [becomeFollower]),
      toPState_becomeFollower]
    exact StepCF.higherTerm (c := c) (id := id) (absMsg .voteResp m ents) (toPState s)
      Hgt Hto (by simp [absMsg, absMsgFrom, fromLeader])
  · rw [decide_eq_false Hgt]
    wp_auto
    wp_gets
    wp_apply raft.wp_load_TermC $$ Hphys as Hphys
    by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · -- m.Term < r.Term: with `checkQuorum` and `preVote` both off and a `MsgVoteResp`
      -- neither `MsgPreVote` nor `MsgStorageAppendResp`, every arm is skipped but the
      -- last, which only logs; then `return nil`. Nothing changed: `StepC.refl`.
      wp_gets
      rw [decide_eq_true Hlt]
      wp_auto
      wp_gets
      wp_cq_pv
      all_goals
        try wp_auto
        repeat (wp_gets; rw [Hty]; try wp_auto)
        wp_gets
        wp_apply raft.wp_load_idC $$ Hphys as Hphys
        wp_gets
        wp_apply raft.wp_load_TermC $$ Hphys as Hphys
        wp_gets
        wp_raft_logC
        iapply HΦ $$ %interface.nil %s %_
        iframe Hphys
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iexact Hrc
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil,
          StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- m.Term = r.Term: the preamble does nothing and control reaches the type
      -- switch, whose default arm is `r.step(m)`.
      wp_gets
      rw [decide_eq_false Hlt]
      wp_auto
      have Hteq : m.Term' = s.term := by word
      repeat (wp_gets; rw [Hty]; try wp_auto)
      wp_gets
      wp_apply raft.wp_load_stepC $$ Hphys as Hphys
      wp_gets
      rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
      cases Hrole : s.role
      · -- Follower: `stepFollower` has no `MsgVoteResp` arm.
        simp only [stepFuncOf]
        wp_gets
        wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx (.inl Hty)
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
        · rw [ite_neg Hnprop]; iexact Hm
        have Hc1 := (FollowerStepResultC.cfg (by nonsnap Hty) Hres).symm
        unfold FollowerStepResultC at Hres
        replace Hres := Hres.2
        subst Hc1
        wp_gets
        rw [ite_pos Hty] at Hres
        obtain ⟨rfl, Heq⟩ := Hres
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s %_
        iframe Hphys
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iexact Hrc
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil,
          StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
      · -- Candidate: `stepCandidate` records the vote and may win or lose in the same
        -- call.
        simp only [stepFuncOf]
        -- the node is in its own progress map: what makes `reset`'s `Match` values a
        -- `LeaderMatchOk` if it wins
        icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
        icases ownTrackerC_prvals_dom c tv _ $$ Htrk with ⟨%Hpd, Htrk⟩
        icases ownTrackerC_progress_map c tv _ $$ Htrk with ⟨-, %Hprd, Htrk⟩
        ihave Hphys := Hback $$ %tv Htrkf Htrk
        icases ownRaftPhysC_voter c r id s $$ Hphys with ⟨%Hvoter, Hphys⟩
        have Hcfg : id ∈ c.voters := Hvoter (by rw [Hrole]; decide)
        have Hid : id ∈ domSet s.prvals := by
          have h1 : domSet s.prvals = domSet s.progress := Hpd
          wp_gets
          rw [h1, Hprd]; exact GMap.elem_of_union_l _ Hcfg
        -- the log's `Hnowrap`: `StepC.win`'s no-wrap premise
        icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
        icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hlnw, Hlog⟩
        ihave Hphys := Hback $$ Hlog
        wp_gets
        wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx (.inl Hty)
            (fun _ => ⟨Hteq, Hterm⟩) (.inl Hrole)
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hrole] at Hc; exact absurd Hc (by decide))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
        · rw [ite_neg Hnprop]; iexact Hm
        have Hc1 := (CandidateStepResultC.cfg (by nonsnap Hty) Hres).symm
        unfold CandidateStepResultC at Hres
        replace Hres := Hres.2
        subst Hc1
        wp_gets
        rw [ite_pos Hty, ite_neg (by rw [Hrole]; decide)] at Hres
        obtain ⟨rfl, won, lost, ms, pvs, Hwon, Hlost, rfl⟩ := Hres
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        -- (2026-10-18, D19b stage 5) a win's entry is the next index: the bound is past the log
        have Hnw1 : plogLastIndexZ (toPState s).base (toPState s).log + 1 < 2 ^ 64 := by
          simp only [plogLastIndexZ, toPState, List.length_append]
          push_cast
          omega
        iapply HΦ $$ %_ %_ %(plogLastIndexZ (toPState s).base (toPState s).log + 1)
        iframe Hphys
        isplitr
        · ipureintro; exact ⟨by omega, Int.le_refl _, Hnw1⟩
        isplitr
        · iexact Hrc
        ipureintro
        refine ⟨nstateWf_prvals_ep _ _ _ (nstateWf_voteRespResult _ _ _ _ _ _ _ Hwf), ?_, rfl,
          RespStep.of_fresh Hnpv (Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hteq.symm)),
          voteRespResult_frame _ _ _ _ _ _ _ _ _ _⟩
        refine ⟨[absMsg .voteResp m ents], by simp, ?_⟩
        have Hnp : s.role ≠ .preCandidate := by rw [Hrole]; decide
        have Hvotes : (toPState s).votes = s.votes := toPState_votes_nonpre _ Hnp
        have Hpr : (toPState s).role = .candidate := by rw [toPState_role, Hrole]; rfl
        cases won
        · -- pending or lost: a frame step
          refine StepCD.frame ?_ ?_
          · rw [toPState_voteRespResult _ _ _ _ _ _ _ pvs Hrole _ (fun h => by cases h)]
            unfold pvoteRespResult
            cases lost
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact StepCF.recordVote (c := c) (id := id) (absMsg .voteResp m ents) (toPState s)
                rfl Hto Hteq Hpr
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have Hq := Hlost rfl
              wp_gets
              rw [← Hvotes] at Hq
              exact stepCF_record_then_lose c id (toPState s) (absMsg .voteResp m ents)
                rfl Hto Hteq Hpr Hq
          · cases lost <;>
              exact ⟨rfl, rfl, fun h => by simp [voteRespResult, becomeFollower, Hrole] at h⟩
        · -- won: `StepC.win`; in the dynamic model `StepR.win`, which sets `pendingConfIndex`
          obtain ⟨Hq, Hms, Hmt⟩ := Hwon rfl
          wp_gets
          rw [← Hvotes] at Hq
          have Hmt' : LeaderMatchOk id { toPState s with
              votes := recordVote (toPState s).votes m.From' (!m.Reject') } (prvalsMatch pvs) := by
            wp_gets
            rw [Hmt]
            exact resetMatched_leader_ok id s Hid _ rfl rfl
          have Hbl := toPState_becomeLeader id
            { s with votes := recordVote s.votes m.From' (!m.Reject') }
            (becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }).prvals
            (resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0)) (resetEpoch_sub _ _ _ _ _)
            (epochRsx_reset _ _ _ _ _)
          have Hms' : ∀ m' ∈ ms, ReplOk id (pwinState id { toPState s with
              votes := recordVote (toPState s).votes m.From' (!m.Reject') } (prvalsMatch pvs)) m' := by
            -- the broadcast was judged at `becomeLeader`'s state, which is
            -- `pwinState`'s up to the outbox and `Match`
            intro m' Hm'
            have H := (Hms m' Hm').1
            refine replOk_proper _ _ _ _ ?_ ?_ ?_ ?_ H
            · rfl
            · rfl
            · exact (congrArg PState.log Hbl).symm
            · rfl
          have Hac : ∀ m' ∈ ms, AppCommitEq (pwinState id { toPState s with
              votes := recordVote (toPState s).votes m.From' (!m.Reject') } (prvalsMatch pvs)) m' :=
            fun m' Hm' h => (Hms m' Hm').2.1 h
          -- (D19p) a snapshot to a tracked id: `becomeLeader` keeps the progress map
          have Hsn : ∀ m' ∈ ms, m'.ty = .snap → m'.dst ∈ c.voters ∪ c.learners :=
            Hms.snapTo (by
              show domSet s.progress ⊆ _
              rw [Hprd]; exact GMap.subseteq_refl _)
          have Hnw' : plogLastIndexZ (toPState s).base (toPState s).log + 1 < 2 ^ 64 := by
            simp only [plogLastIndexZ, toPState, List.length_append]
            push_cast
            omega
          refine ⟨?_, fun Adm dec g hc hd => ⟨g.cidx, .inl rfl, ?_⟩⟩
          · rw [if_pos (rfl : true = true), toPState_voteRespResult _ _ _ _ _ _ _ pvs Hrole _
              (fun _ => ⟨resetEpoch_sub _ _ _ _ _, epochRsx_reset _ _ _ _ _⟩)]
            unfold pvoteRespResult
            simp only [↓reduceIte]
            exact stepC_record_then_win c id (toPState s) (absMsg .voteResp m ents)
              (prvalsMatch pvs) ms rfl Hto Hteq Hpr Hmt' Hms' Hq (Int.le_refl _) Hsn
          · rw [if_pos (rfl : true = true)]
            change StepR Adm dec id _ (rOf s g) ([absMsg .voteResp m ents] ++ [])
              (rOf { voteRespResult id s m.From' m.Reject' true lost ms with
                       prvals := pvs, ep := resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0) } g)
            have Hr : rOf { voteRespResult id s m.From' m.Reject' true lost ms with
                              prvals := pvs, ep := resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0) } g =
                { rOf s g with
                  p := toPState { voteRespResult id s m.From' m.Reject' true lost ms with
                                    prvals := pvs, ep := resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0) },
                  pci := plastIndex (toPState s) } := by
              unfold rOf pciR
              simp [voteRespResult, becomeLeader, becomeLeaderLog, becomeLeaderPre, sendMsgs,
                resetTo, resetTo0, plastIndex_toPState]
            wp_gets
            rw [Hr, toPState_voteRespResult _ _ _ _ _ _ _ pvs Hrole _
              (fun _ => ⟨resetEpoch_sub _ _ _ _ _, epochRsx_reset _ _ _ _ _⟩)]
            unfold pvoteRespResult
            simp only [↓reduceIte]
            have Hrp : (rOf s g).p = toPState s := rfl
            have Hrc : (rOf s g).cfg.cfg = c := hc
            refine .trans _ _ _ _ _ (StepR.recordVote (absMsg .voteResp m ents) (rOf s g) rfl Hto
              Hteq Hpr) ?_
            exact StepR.win _ (prvalsMatch pvs) ms Hpr (by rw [Hrc]; exact Hq) (Int.le_refl _) Hmt' Hms'
              Hac
      · -- Leader: `stepLeader`'s `MsgVoteResp` arm only reads.
        simp only [stepFuncOf]
        wp_gets
        imod (preceipt_zero (GF := GF)) with #Hrc00
        wp_apply _P.stepLeader c r id s ml m ents sn ctx rs 0 (.inl Hty) Hrole
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
          $$ [$Hphys $Hrc00 Hm] as %err %s1 %dropped ⟨Hphys, -, %Hres, Herrn⟩
        · rw [ite_neg Hnprop]; iframe Hm; iintro %Hc; exact absurd Hc Hnprop
        unfold LeaderStepResultC at Hres
        wp_gets
        rw [ite_neg (by rw [Hty]; w32_ne)] at Hres
        obtain ⟨rfl, Hres⟩ := Hres
        unfold LeaderNonpropResultC at Hres
        have Heq : s1 = s := by
          rcases Hres with ⟨-, h⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc6, -⟩ | ⟨Hc7, -⟩ <;>
            first | exact h | (exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)) | (exfalso; rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> rw [Hty] at h6 <;> exact absurd h6 (by w32_ne)) | (exfalso; rw [Hty] at Hc7; exact absurd Hc7 (by w32_ne))
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s %_
        iframe Hphys
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iexact Hrc
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil,
          StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
      · -- PreCandidate (2026-10-04): `stepCandidate`'s `myVoteRespType` is
        -- `MsgPreVoteResp`, so a vote response is ignored.
        simp only [stepFuncOf]
        wp_gets
        wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx (.inl Hty)
            (fun _ => ⟨Hteq, Hterm⟩) (.inr Hrole)
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
        · rw [ite_neg Hnprop]; iexact Hm
        have Hc1 := (CandidateStepResultC.cfg (by nonsnap Hty) Hres).symm
        unfold CandidateStepResultC at Hres
        replace Hres := Hres.2
        subst Hc1
        wp_gets
        rw [ite_pos Hty, ite_pos Hrole] at Hres
        obtain ⟨rfl, Heq⟩ := Hres
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s %_
        iframe Hphys
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iexact Hrc
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil,
          StepCD.frame (.refl _) (RFrame.refl _)⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
