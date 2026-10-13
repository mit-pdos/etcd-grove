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
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
* Rocq's `Local Ltac wp_load_step` (the load of `r.step` in `r.step(r, m)`, bound by
  hand with `wp_bind` because `wp_apply` did not find it in the function position of an
  application, 2026-09-24) is not ported; `MsgBeat.lean` uses
  `wp_apply raft.wp_load_step $$ Hphys as Hphys` there, and so does this proof.
* Rocq's hoisted `bool_decide` facts (`Hn17`, `Hn5`, …) are not needed: as in
  `MsgApp_gt.lean`, `repeat (rw [Hty]; wp_auto)` evaluates each type test.
* `ite_pos`/`ite_neg` are local helpers for the `if`s of `FollowerStepResult` etc.
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
    (reject won lost : Bool) (ms : List Msg) (pvs : GMap w64 Progress) (m : raftpb.Message) :
    NetFrame s { voteRespResult id s src reject won lost ms with prvals := pvs } ∧
    TermStep m s { voteRespResult id s src reject won lost ms with prvals := pvs } := by
  unfold voteRespResult
  split
  · exact keep_frame rfl rfl rfl rfl rfl
  · split
    · exact keep_frame rfl rfl rfl rfl rfl
    · exact keep_frame rfl rfl rfl rfl rfl

/-- `MsgVoteResp`: the term preamble, then `r.step(m)`.

The one branch where all three `stepX` can run, so it is also the one that needs the
`r.step` field pinned to the role: `raft.wp_load_step` loads `s.stepfn`, and `NStateWf`
says it is `stepFuncOf s.role` -- without that there is nothing to apply at
`r.step(m)`. Three term cases, and the third splits three ways:

- `m.Term > r.Term`: a `VoteResp` is not `fromLeader`, so the preamble runs
  `becomeFollower(m.Term, None)` rather than adopting a leader. The role is `follower`
  afterwards, so `r.step` is `stepFollower`, which has no `MsgVoteResp` arm. One
  `Step.higherTerm`.
- `m.Term < r.Term`: with `checkQuorum` and `preVote` both off, and a `MsgVoteResp`
  being neither `MsgPreVote` nor `MsgStorageAppendResp`, every arm of the chain is
  skipped but the last, which only logs. Then `return nil`. `Step.refl`, with
  `recv = []` -- the message is dropped, which the model always permits.
- `m.Term = r.Term`: straight to the type switch's default arm. `stepFollower` and
  `stepLeader` only read, so again `Step.refl`; `stepCandidate` records the vote and
  may win or lose in the same call, which is `Step.recordVote` followed by `Step.win` /
  `Step.lose`, on its `won`/`lost` flags. -/
theorem wp_Step_MsgVoteResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `stepCandidate` needs it; `Step` is the outermost caller
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .voteResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hcfg Hwf
  have Hnpv : m.Type' ≠ MsgPreVoteResp := by rw [Hty]; w32_ne
  wp_start as Hphys
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_false Hterm]
  wp_auto
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  by_cases Hgt : uint.Z s.term < uint.Z m.Term'
  · rw [decide_eq_true Hgt]
    wp_auto
    repeat (rw [Hty]; wp_auto)
    -- "received a message with higher term"
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    wp_raft_log
    repeat (rw [Hty]; wp_auto)
    -- a `MsgVoteResp` is not from a leader: `becomeFollower(m.Term, None)`
    wp_apply _P.becomeFollower _ _ _ _ _ _ (by exact Int.le_of_lt Hgt) $$ [$Hphys] as %pvs Hphys
    repeat (rw [Hty]; wp_auto)
    -- the default arm, `r.step(m)`: the role is now follower
    wp_apply raft.wp_load_step $$ Hphys as Hphys
    have Hsf : ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).stepfn =
        functions stepFollower [] := rfl
    rw [Hsf]
    wp_apply _P.stepFollower cfg r id { becomeFollower s m.Term' (W64 0) with prvals := pvs }
        m [] (zero_val _) [] [] (.inl Hty)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        first | (rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
      isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro %Hc; exfalso; rw [Hty] at Hc
        rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
    unfold FollowerStepResult at Hres
    rw [ite_pos Hty] at Hres
    obtain ⟨rfl, rfl⟩ := Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Herrn with %Herrn
    subst Herrn
    wp_auto
    iapply HΦ
    iframe Hphys
    ipureintro
    refine ⟨⟨rfl, rfl⟩, ⟨[absMsg .voteResp m ents], by simp, ?_⟩, rfl,
      RespStep.of_fresh Hnpv (Int.le_of_lt Hgt), stepdown_frame (by rw [Hty]; w32_ne) (Int.le_of_lt Hgt) rfl rfl rfl rfl rfl⟩
    rw [toPState_prvals_nl (becomeFollower s m.Term' (W64 0)) pvs (by simp [becomeFollower]),
      toPState_becomeFollower]
    exact Step.higherTerm (cfg := cfg) (id := id) (absMsg .voteResp m ents) (toPState s)
      Hgt Hto (by simp [absMsg, absMsgFrom, fromLeader])
  · rw [decide_eq_false Hgt]
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    by_cases Hlt : uint.Z m.Term' < uint.Z s.term
    · -- m.Term < r.Term: with `checkQuorum` and `preVote` both off and a `MsgVoteResp`
      -- neither `MsgPreVote` nor `MsgStorageAppendResp`, every arm is skipped but the
      -- last, which only logs; then `return nil`. Nothing changed: `Step.refl`.
      rw [decide_eq_true Hlt]
      wp_auto
      wp_apply raft.wp_load_checkQuorum $$ Hphys as Hphys
      wp_apply raft.wp_load_preVote $$ Hphys as Hphys
      cases s.prevote
      all_goals
        wp_auto
        repeat (rw [Hty]; wp_auto)
        wp_apply raft.wp_load_id $$ Hphys as Hphys
        wp_apply raft.wp_load_Term $$ Hphys as Hphys
        wp_raft_log
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
    · -- m.Term = r.Term: the preamble does nothing and control reaches the type
      -- switch, whose default arm is `r.step(m)`.
      rw [decide_eq_false Hlt]
      wp_auto
      have Hteq : m.Term' = s.term := by word
      repeat (rw [Hty]; wp_auto)
      wp_apply raft.wp_load_step $$ Hphys as Hphys
      rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
      cases Hrole : s.role
      · -- Follower: `stepFollower` has no `MsgVoteResp` arm.
        simp only [stepFuncOf]
        wp_apply _P.stepFollower cfg r id s m [] (zero_val _) [] [] (.inl Hty)
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
        · isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc
            first | (rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
          isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
          isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          · iintro %Hc; exfalso; rw [Hty] at Hc
            rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)
        unfold FollowerStepResult at Hres
        rw [ite_pos Hty] at Hres
        obtain ⟨rfl, Heq⟩ := Hres
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
      · -- Candidate: `stepCandidate` records the vote and may win or lose in the same
        -- call.
        simp only [stepFuncOf]
        -- the node is in its own progress map: what makes `reset`'s `Match` values a
        -- `LeaderMatchOk` if it wins
        icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
        icases ownTracker_prvals_dom cfg tv _ $$ Htrk with ⟨%Hpd, Htrk⟩
        icases ownTracker_progress_map cfg tv _ $$ Htrk with ⟨-, %Hprd, Htrk⟩
        ihave Hphys := Hback $$ %tv Htrkf Htrk
        have Hid : id ∈ domSet s.prvals := by
          have h1 : domSet s.prvals = domSet s.progress := Hpd
          have h2 : domSet s.progress = cfg := Hprd
          rw [h1, h2]; exact Hcfg
        -- the log's `Hnowrap`: `Step.win`'s no-wrap premise
        icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
        icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hlnw, Hlog⟩
        ihave Hphys := Hback $$ Hlog
        wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) [] [] (.inl Hty)
            (fun _ => ⟨Hteq, Hterm⟩) (.inl Hrole) Hcfg
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hrole] at Hc; exact absurd Hc (by decide))
          $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
        · isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc
            first | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
          isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        unfold CandidateStepResult at Hres
        rw [ite_pos Hty, ite_neg (by rw [Hrole]; decide)] at Hres
        obtain ⟨rfl, won, lost, ms, pvs, Hwon, Hlost, rfl⟩ := Hres
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ
        iframe Hphys
        ipureintro
        refine ⟨nstateWf_prvals _ _ (nstateWf_voteRespResult _ _ _ _ _ _ _ Hwf), ?_, rfl,
          RespStep.of_fresh Hnpv (Int.le_of_eq (congrArg (fun x : w64 => uint.Z x) Hteq.symm)),
          voteRespResult_frame _ _ _ _ _ _ _ _ _⟩
        refine ⟨[absMsg .voteResp m ents], by simp, ?_⟩
        rw [toPState_voteRespResult _ _ _ _ _ _ _ _ Hrole]
        have Hnp : s.role ≠ .preCandidate := by rw [Hrole]; decide
        have Hvotes : (toPState s).votes = s.votes := toPState_votes_nonpre _ Hnp
        have Hpr : (toPState s).role = .candidate := by rw [toPState_role, Hrole]; rfl
        unfold pvoteRespResult
        cases won
        · cases lost
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact Step.recordVote (cfg := cfg) (id := id) (absMsg .voteResp m ents) (toPState s)
              rfl Hto Hteq Hpr
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have Hq := Hlost rfl
            rw [← Hvotes] at Hq
            exact step_record_then_lose cfg id (toPState s) (absMsg .voteResp m ents)
              rfl Hto Hteq Hpr Hq
        · simp only [↓reduceIte]
          obtain ⟨Hq, Hms, Hmt⟩ := Hwon rfl
          rw [← Hvotes] at Hq
          refine step_record_then_win cfg id (toPState s) (absMsg .voteResp m ents)
            (prvalsMatch pvs) ms rfl Hto Hteq Hpr ?_ ?_ Hq ?_
          · rw [Hmt]
            exact resetMatched_leader_ok id s Hid _ rfl rfl
          · -- the broadcast was judged at `becomeLeader`'s state, which is
            -- `pwinState`'s up to the outbox and `Match`
            intro m' Hm'
            have H := Hms m' Hm'
            have Hbl := toPState_becomeLeader id
              { s with votes := recordVote s.votes m.From' (!m.Reject') }
              (becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }).prvals
            refine replOk_proper _ _ _ _ ?_ ?_ ?_ ?_ H
            · rfl
            · rfl
            · exact (congrArg PState.log Hbl).symm
            · rfl
          · simp only [plogLastIndexZ, toPState, List.length_append]
            push_cast
            omega
      · -- Leader: `stepLeader`'s `MsgVoteResp` arm only reads.
        simp only [stepFuncOf]
        wp_apply _P.stepLeader cfg r id s m [] [] (.inl Hty) Hrole Hcfg
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by
              exfalso; rw [Hty] at Hc
              rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn, -⟩
        · isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        unfold LeaderStepResult at Hres
        rw [ite_neg (by rw [Hty]; w32_ne)] at Hres
        obtain ⟨rfl, Hres⟩ := Hres
        unfold LeaderNonpropResult at Hres
        have Heq : s1 = s := by
          rcases Hres with ⟨-, h⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ <;>
            first | exact h | (exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩
      · -- PreCandidate (2026-10-04): `stepCandidate`'s `myVoteRespType` is
        -- `MsgPreVoteResp`, so a vote response is ignored.
        simp only [stepFuncOf]
        wp_apply _P.stepCandidate cfg r id s m [] (zero_val _) [] [] (.inl Hty)
            (fun _ => ⟨Hteq, Hterm⟩) (.inr Hrole) Hcfg
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
            (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
          $$ [$Hphys] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
        · isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc
            first | (rcases Hc with Hc | Hc <;> exact absurd Hc (by w32_ne)) | exact absurd Hc (by w32_ne)
          isplitl []
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
          · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
        unfold CandidateStepResult at Hres
        rw [ite_pos Hty, ite_pos Hrole] at Hres
        obtain ⟨rfl, Heq⟩ := Hres
        subst s1
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herrn with %Herrn
        subst Herrn
        wp_auto
        iapply HΦ $$ %interface.nil %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, ⟨[], fun _ h => absurd h List.not_mem_nil, .refl _⟩, rfl,
      RespStep.refl _ _, keep_frame rfl rfl rfl rfl rfl⟩

end StepProof

end branches

end EtcdGrove
end Perennial
