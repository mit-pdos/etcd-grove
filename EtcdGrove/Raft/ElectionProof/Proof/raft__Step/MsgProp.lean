/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgProp.v.

One branch of `Step`'s proof: `MsgProp`, a local proposal.

This is **proof structure, not specification**: `Step` has exactly one spec, in
`Spec/raft__Step.lean`, and this module has no `Module Type` and no `Parameter`.
Only `Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import
it; see `notes/decisions.md` (2026-09-17, and 2026-09-18 for why the helpers
moved out of the top-level directory).

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as their second.
* Rocq's `Local Lemma to_pstate_proposed` is `private theorem toPState_proposed`.
* Rocq's `Local Ltac`s are not ported: `wp_load_step` (binds the load of `r.step` in
  function position, as in `MsgVoteResp`), `finish_err err` (`Step`'s tail after
  `r.step(r, m)`: `if err != nil { return err }`, then `return nil`; destructs `err` and
  runs `wp_auto`), `recv_elem` (`∀ m' ∈ recv, m' = a` for `recv` `[]` or `[a]`), and
  `finish_drop` (a dropped proposal: the state is unchanged, `Step.refl`, and `err` is
  `ErrProposalDropped`'s value); their bodies are inlined at each use.
* `ite_pos`/`ite_neg` are local helpers for the `if`s of `FollowerStepResult` etc.
-/
import EtcdGrove.Raft.ElectionProof.Proof.raft__Step.Base

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

namespace StepProof

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- `proposed` (`Spec/stepLeader.lean`) is `Step.propose`'s state: the log grows by the
batch stamped at the leader's term and the indices after the last one, and the
self-acknowledgement at the new last index is queued. (Checked 2026-10-02: the physical
definition and the rule agree; nothing needed changing.) -/
private theorem toPState_proposed (id : w64) (s : NState) (ents : List raftpb.Entry) :
    toPState (proposed id s ents) =
    psendMsgs
      (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))
      [pselfAck id
         (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))] := by
  have Hli : ∀ s : NState, plastIndex (toPState s) = logLast s.logst := by
    intro s
    simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
    congr 1; push_cast; omega
  simp only [proposed, sendMsgs, toPState, psendMsgs, pappend, pselfAck, selfAck, logAppend,
    List.append_assoc]
  rw [← Hli s]
  simp only [toPState]
  congr 3
  simp only [plastIndex, plogLastIndexZ, logLast, List.length_append]
  congr 2; push_cast; simp only [List.length_mapIdx]; omega

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- `if` on a decided condition (Mathlib's `if_pos`/`if_neg`, deprecated here). -/
private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- `MsgProp`: a local message (`Term = 0`), so the term preamble is skipped and the
type switch's default arm runs `r.step(r, m)`:

- `stepFollower` forwards it to the leader (`Step.propForward`), or, with no leader
  known, drops it (`Step.refl`, `ErrProposalDropped`). `send` holds the entries
  read-only, so the batch is made persistent first;
- `stepCandidate` drops it;
- `stepLeader` appends it (`Step.propose`) and broadcasts (`Step.sendApps`), or drops it
  when `appendEntry` refuses the batch.

`recv` is the proposal itself when it is forwarded, and nothing otherwise. `LeadOk`
(`Protocol/Model.lean`, from `ownRaftGhost`) is what makes the follower's forwarding
`send` not self-addressed. -/
theorem wp_Step_MsgProp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgProp →
    m.Term' = W64 0 →
    (m.From' = W64 0 ∨ m.From' = id) →
    ents ≠ [] →
    (∀ e ∈ ents, e.Type' = EntryNormal) →
    (ents.length : Int) < 2^61 →
    (s.role = .follower → s.lead ≠ id) →
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        "Hents" ∷ m.Entries' ↦* ents ∗
        "Hcap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- Either one step from `s` consuming at most the proposal (forwarded or
        -- dropped), or -- appended at the leader -- the `Step.propose` state's premises
        -- and one step from that state on (the broadcast), so that `Step` can take
        -- `Step.propose`'s ghost update with the registry
        -- (`ownRaftGhost_step_propose_reg`) and the uniform one for the rest
        -- (2026-10-06).
        "%Hrefines" ∷ ⌜(∃ recv, (∀ m' ∈ recv, m' = absMsg .propose m ents) ∧
              Step cfg id (toPState s) recv (toPState s')) ∨
            (err = interface.nil ∧ (toPState s).role = .leader ∧
             (∀ e ∈ ents, e.Type' = W32 0) ∧
             plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int) < 2 ^ 64 ∧
             Step cfg id
               (psendMsgs (pappend (toPState s)
                   (ents.mapIdx (stamp (toPState s).term (plastIndex (toPState s)))))
                 [pselfAck id (pappend (toPState s)
                   (ents.mapIdx (stamp (toPState s).term (plastIndex (toPState s)))))])
               [] (toPState s'))⌝ ∗
        "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) }} := by
  intro Hty Hterm Hfrom Hne Hnorm Hlen Hlok Hcfg Hwf
  wp_start as ⟨Hphys, Hents, Hcap⟩
  wp_auto
  wp_apply _P.traceReceiveMessage
  rw [decide_eq_true Hterm]
  wp_auto
  rw [Hty]
  wp_auto
  wp_apply raft.wp_load_step $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf]
  have HnVR : m.Type' ≠ MsgVoteResp := by rw [Hty]; w32_ne
  cases Hrole : s.role
  · -- Follower: forward to the leader, or drop. `send` wants the entries read-only.
    simp only [stepFuncOf]
    ipersist Hents
    wp_apply _P.stepFollower cfg r id s m ents (zero_val _) []
        (.inr (.inl Hty))
        (fun _ => ⟨Hfrom, Hterm, Hlok Hrole⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hcap] as %err %s1 %dropped ⟨Hphys, %Hres, Herrn⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro _
        iframe Hents Hcap
    unfold FollowerStepResult at Hres
    rw [ite_neg HnVR, ite_pos Hty] at Hres
    by_cases Hl0 : s.lead = W64 0
    · -- no leader known: dropped
      rw [ite_pos Hl0] at Hres
      obtain ⟨rfl, rfl⟩ := Hres
      simp only [↓reduceIte]
      cases err
      all_goals
        wp_auto
        iapply HΦ
        iframe Hphys
        isplitr
        · ipureintro; exact Hwf
        isplitr
        · ipureintro; left; exact ⟨[], by simp, .refl _⟩
        iright; iexact Herrn
    · -- forwarded: `Step.propForward`
      rw [ite_neg Hl0] at Hres
      obtain ⟨rfl, rfl⟩ := Hres
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      iapply HΦ
      iframe Hphys
      isplitr
      · ipureintro; exact nstateWf_sendMsgs _ _ Hwf
      isplitr
      · ipureintro; left
        refine ⟨[absMsg .propose m ents], by simp, ?_⟩
        have Hld : (toPState s).lead = s.lead :=
          toPState_lead_nonpre s (by rw [Hrole]; exact PRole.noConfusion)
        rw [toPState_sendMsgs]
        have := Step.propForward (cfg := cfg) (id := id) (absMsg .propose m ents) (toPState s)
          rfl (by rw [toPState_role, Hrole]; rfl) (by rw [Hld]; exact Hl0)
        rw [Hld] at this
        exact this
      ileft; ipureintro; rfl
  · -- Candidate: drop
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m ents (zero_val _) []
        (.inr (.inl Hty))
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
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    unfold CandidateStepResult at Hres
    rw [ite_neg HnVR, ite_pos Hty] at Hres
    obtain ⟨rfl, rfl⟩ := Hres
    simp only [↓reduceIte]
    cases err
    all_goals
      wp_auto
      iapply HΦ
      iframe Hphys
      isplitr
      · ipureintro; exact Hwf
      isplitr
      · ipureintro; left; exact ⟨[], by simp, .refl _⟩
      iright; iexact Herrn
  · -- Leader: append and broadcast, or drop
    simp only [stepFuncOf]
    wp_apply _P.stepLeader cfg r id s m ents (.inr (.inr (.inr (.inr (.inl Hty))))) Hrole Hcfg
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hne, Hnorm, Hlen⟩)
      $$ [$Hphys Hents] as %err %s' %dropped ⟨Hphys, %Hres, Herrn, -⟩
    · isplitl []
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
      · iintro _; iexact Hents
    unfold LeaderStepResult at Hres
    rw [ite_pos Hty] at Hres
    unfold LeaderProposeResult at Hres
    cases dropped
    · -- appended and broadcast
      simp only [Bool.false_eq_true, ↓reduceIte] at Hres ⊢
      obtain ⟨ms, pvs, rfl, Hms, Hpvs⟩ := Hres
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      -- the appended log does not wrap: `ownRaftLog`'s `Hnowrap` at the new state
      icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
      icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnw, Hlog⟩
      ihave Hphys := Hback $$ Hlog
      iapply HΦ
      iframe Hphys
      isplitr
      · ipureintro; exact nstateWf_prvals _ _ (nstateWf_sendMsgs _ _ Hwf)
      isplitr
      · ipureintro; right
        refine ⟨rfl, by rw [toPState_role, Hrole]; rfl, Hnorm, ?_, ?_⟩
        · simp only [proposed, sendMsgs, logAppend, List.length_append, List.length_mapIdx] at Hnw
          simp only [plogLastIndexZ, toPState, List.length_append]
          push_cast at Hnw ⊢
          omega
        · rw [toPState_prvals (sendMsgs (proposed id s ents) ms) pvs (fun _ => Hpvs), toPState_sendMsgs, toPState_proposed]
          unfold ReplSends at Hms
          rw [toPState_proposed] at Hms
          exact Step.sendApps _ _ (by simp [psendMsgs, pappend, toPState, Hrole, proleRole]) Hms
      ileft; ipureintro; rfl
    · -- `appendEntry` refused the batch
      simp only [↓reduceIte] at Hres ⊢
      subst Hres
      cases err
      all_goals
        wp_auto
        iapply HΦ
        iframe Hphys
        isplitr
        · ipureintro; exact Hwf
        isplitr
        · ipureintro; left; exact ⟨[], by simp, .refl _⟩
        iright; iexact Herrn
  · -- PreCandidate (2026-10-04), as a candidate: drop
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate cfg r id s m ents (zero_val _) []
        (.inr (.inl Hty))
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
      · iintro %Hc; exfalso; rw [Hty] at Hc; exact absurd Hc (by w32_ne)
    unfold CandidateStepResult at Hres
    rw [ite_neg HnVR, ite_pos Hty] at Hres
    obtain ⟨rfl, rfl⟩ := Hres
    simp only [↓reduceIte]
    cases err
    all_goals
      wp_auto
      iapply HΦ
      iframe Hphys
      isplitr
      · ipureintro; exact Hwf
      isplitr
      · ipureintro; left; exact ⟨[], by simp, .refl _⟩
      iright; iexact Herrn

end StepProof

end branches

end EtcdGrove
end Perennial
