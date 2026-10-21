/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgProp.v.

One branch of `Step`'s proof: `MsgProp`, a local proposal.

This is **proof structure, not specification**: `Step` has exactly one spec, in
`Spec/raft__Step.lean`, and this module has no `Module Type` and no `Parameter`.
Only `Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import
it; see `notes/decisions.md` (2026-09-17, and 2026-09-18 for why the helpers
moved out of the top-level directory).

Lean notes:
* The branch lemmas take the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as their first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as their second.
* Rocq's `Local Lemma to_pstate_proposed` is `private theorem toPState_proposed`.
* Rocq's `Local Ltac`s are not ported: `wp_load_step` (binds the load of `r.step` in
  function position, as in `MsgVoteResp`), `finish_err err` (`Step`'s tail after
  `r.step(r, m)`: `if err != nil { return err }`, then `return nil`; destructs `err` and
  runs `wp_auto`), `recv_elem` (`∀ m' ∈ recv, m' = a` for `recv` `[]` or `[a]`), and
  `finish_drop` (a dropped proposal: the state is unchanged, `StepC.refl`, and `err` is
  `ErrProposalDropped`'s value); their bodies are inlined at each use.
* `ite_pos`/`ite_neg` are local helpers for the `if`s of `FollowerStepResult` etc.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.Base
public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas

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

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- `proposed` (`Spec/stepLeader.lean`) is `StepC.propose`'s state: the log grows by the
batch stamped at the leader's term and the indices after the last one, and the
self-acknowledgement at the new last index is queued. (Checked 2026-10-02: the physical
definition and the rule agree; nothing needed changing.) -/
private theorem toPState_proposed (id : w64) (s : NState) (ents : List EntryM)
    (Hr : s.role = .leader) :
    toPState (proposed id s ents) =
    psendMsgs
      (pappend (toPState s)
        (ents.mapIdx (stampS s.term (toPState s).sub (plastIndex (toPState s)))))
      [pselfAck id
         (pappend (toPState s)
           (ents.mapIdx (stampS s.term (toPState s).sub (plastIndex (toPState s)))))] := by
  have Hli : ∀ s : NState, plastIndex (toPState s) = logLast s.logst := by
    intro s
    simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
    congr 1; push_cast; omega
  -- (2026-10-20, witness support) the entries are stamped with the leader's subterm
  have Hsub : (toPState s).sub = s.ep.sub := by simp [toPState, Hr]
  rw [Hsub]
  simp only [proposed, sendMsgs, toPState, psendMsgs, pappend, pselfAck,
    selfAck, logAppend, List.append_assoc]
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

/-- A proposal the leader drops after the conf-change loop moved `pendingConfIndex`
(2026-10-14, stage B7): nothing the protocol sees, `StepR.propDrop` in the dynamic model. -/
private theorem stepCD_propDrop (c : CfgM) (id : w64) (m : MessageM) (s : NState)
    (ents : List EntryM) (cs : List (Option CCMsg)) (ctx : List w8)
    (Hty : m.Type' = MsgProp) (Hr : s.role = .leader) (Hct : CCTypesOk ents cs)
    (Hlen : (ents.length : Int) < 2 ^ 61) :
    StepCD c id B m s [] { s with pci := (leaderPropConf s ents cs c.joint).2 } := by
  refine ⟨.refl _, fun Adm dec g hc hd => ⟨g.cidx, .inl rfl, ?_⟩⟩
  change StepR Adm dec id B (rOf s g) []
    (rOf { s with pci := (leaderPropConf s ents cs c.joint).2 } g)
  have Hnw := hd.2.2.2.2 Hty
  have Hrl : (rOf s g).p.role = .leader := by simp [rOf, toPState, Hr, proleRole]
  have Hpb : propBatch (rOf s g) ents cs = leaderPropConf s ents cs c.joint := by
    show propConf s.logst.applied (plastIndex (toPState s)) (pciR s) ents cs
        (CfgM.joint g.cfg.cfg) = propConf s.logst.applied (logLast s.logst) s.pci ents cs c.joint
    have Hli : plastIndex (toPState s) = logLast s.logst := by
      simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
      congr 1; push_cast; omega
    rw [Hli, hc]; simp [pciR, Hr]
  have Hrr : rOf { s with pci := (leaderPropConf s ents cs c.joint).2 } g =
      { rOf s g with pci := (leaderPropConf s ents cs c.joint).2 } := by
    unfold rOf pciR
    rw [show ({ s with pci := (leaderPropConf s ents cs c.joint).2 } : NState).role = s.role
      from rfl, ite_eq_left Hr]
    rfl
  rw [Hrr, ← Hpb]
  exact StepR.propDrop (absMsg .propose m ents ctx) (rOf s g) cs rfl Hrl Hct
    (by show plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int) < 2 ^ 64
        omega)

set_option maxHeartbeats 1000000 in
/-- `MsgProp`: a local message (`Term = 0`), so the term preamble is skipped and the
type switch's default arm runs `r.step(r, m)`:

- `stepFollower` forwards it to the leader (`StepC.propForward`), or, with no leader
  known, drops it (`StepC.refl`, `ErrProposalDropped`). `send` holds the entries
  read-only, so the batch is made persistent first;
- `stepCandidate` drops it;
- `stepLeader` appends it (`StepC.propose`) and broadcasts (`StepC.sendApps`), or drops it
  when `appendEntry` refuses the batch.

`recv` is the proposal itself when it is forwarded, and nothing otherwise. `LeadOk`
(`Protocol/Model.lean`, from `ownRaftGhost`) is what makes the follower's forwarding
`send` not self-addressed. -/
theorem wp_Step_MsgProp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (cs : List (Option CCMsg)) (k0 : Nat) :
    m.Type' = MsgProp →
    m.Term' = W64 0 →
    (m.From' = W64 0 ∨ m.From' = id) →
    ents ≠ [] →
    (ents.length : Int) < 2^61 →
    (s.role = .follower → s.lead ≠ id) →
    -- a leader's term is nonzero (2026-10-10, `ownRaftGhost_term_nz`)
    (s.role = .leader → s.term ≠ W64 0) →
    NStateWf s →
    -- (2026-10-18, D19b stage 5) the log's last index fits a word (the ghost state's)
    plogLastIndexZ (toPState s).base (toPState s).log < 2 ^ 64 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the proposal, its entry pointers owned
        "Hm" ∷ msgIn ml (DFrac.own 1) ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (2026-10-13) the conf-change entries' bytes
        "#Hcc" ∷ ccEntsOk ents cs ∗
        -- (2026-10-18, D19b stage 5) a time receipt, for `appendEntry`
        "#Hrc" ∷ ⧖ k0 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (B : Int), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        -- (2026-10-18, D19b stage 5) the bound `B` of the indices the step creates: the log's last
        -- index, or past it by the batch when appended, which the receipt then covers
        "%HBb" ∷ ⌜plogLastIndexZ (toPState s).base (toPState s).log ≤ B ∧
          B ≤ plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int) ∧
          B < 2 ^ 64⌝ ∗
        "Hrcb" ∷ (⌜plogLastIndexZ (toPState s).base (toPState s).log < B⌝ -∗
          ⧖ (k0 + ents.length)) ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- what `RawNode` keeps track of is untouched (2026-10-09)
        "%Hframe" ∷ ⌜LocalFrame s s' ∧ s'.logst.applying = s.logst.applying⌝ ∗
        -- Either one step from `s` consuming at most the proposal (forwarded or
        -- dropped), or -- appended at the leader -- the `StepC.propose` state's premises
        -- and one step from that state on (the broadcast), so that `Step` can take
        -- `StepC.propose`'s ghost update with the registry
        -- (`ownRaftGhost_step_propose_reg`) and the uniform one for the rest
        -- (2026-10-06).
        -- (2026-10-14, stage B7: the whole step, the proposal received when it is forwarded
        -- or appended; until then the appended case handed `Step` `StepC.propose`'s premises)
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .propose m ents ctx) ∧
              recv.length ≤ 1 ∧ StepCD c id B m s recv s'⌝ ∗
        "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) }} := by
  intro Hty Hterm Hfrom Hne Hlen Hlok Hlnz Hwf HL
  wp_start as ⟨Hphys, Hm, #Hcc, #Hrc⟩
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
  have HnVR : m.Type' ≠ MsgVoteResp := by rw [Hty]; w32_ne
  cases Hrole : s.role
  · -- Follower: forward to the leader, or drop. `send` wants the entries read-only.
    simp only [stepFuncOf]
    wp_apply _P.stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inl Hty))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hfrom, Hterm, Hlok Hrole⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_prop Hty $$ Hm
    have Hc1 := (FollowerStepResultC.cfg (by nonsnap Hty) Hres).symm
    unfold FollowerStepResultC at Hres
    replace Hres := Hres.2
    subst Hc1
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
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
        isplitr
        · ipureintro; exact Hwf
        isplitr
        · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
        isplitr
        · ipureintro; exact ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩
        iright; iexact Herrn
    · -- forwarded: `StepC.propForward`
      rw [ite_neg Hl0] at Hres
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
      · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
      isplitr
      · ipureintro; exact nstateWf_sendMsgs _ _ Hwf
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro
        refine ⟨[absMsg .propose m ents ctx], by simp, by simp, StepCD.frame ?_ (by rframe)⟩
        have Hld : (toPState s).lead = s.lead :=
          toPState_lead_nonpre s (by rw [Hrole]; exact PRole.noConfusion)
        rw [toPState_sendMsgs]
        have := StepCF.propForward (c := c) (id := id) (absMsg .propose m ents ctx) (toPState s)
          rfl (by rw [toPState_role, Hrole]; rfl) (by rw [Hld]; exact Hl0)
        rw [Hld] at this
        exact this
      ileft; ipureintro; rfl
  · -- Candidate: drop
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inl Hty))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inl Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_prop Hty $$ Hm
    have Hc1 := (CandidateStepResultC.cfg (by nonsnap Hty) Hres).symm
    unfold CandidateStepResultC at Hres
    replace Hres := Hres.2
    subst Hc1
    rw [ite_neg HnVR, ite_pos Hty] at Hres
    obtain ⟨rfl, rfl⟩ := Hres
    simp only [↓reduceIte]
    cases err
    all_goals
      wp_auto
      iapply HΦ
      iframe Hphys
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
      isplitr
      · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
      isplitr
      · ipureintro; exact Hwf
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro; exact ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩
      iright; iexact Herrn
  · -- Leader: append and broadcast, or drop
    simp only [stepFuncOf]
    icases ownRaftPhysC_dom c r id s $$ Hphys with ⟨%Hpc, Hphys⟩
    wp_apply _P.stepLeader c r id s ml m ents sn ctx rs k0 (.inr (.inr (.inr (.inr (.inl Hty))))) Hrole
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hne, Hlen, Hlnz Hrole⟩)
        (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys $Hrc Hm] as %err %s' %dropped ⟨Hphys, Hrcl, %Hres, Herrn⟩
    · isplitl [Hm]
      · iapply msgIn_prop Hty $$ Hm
      · iintro _; iexists cs; iexact Hcc
    unfold LeaderStepResultC at Hres
    rw [ite_pos Hty] at Hres
    unfold LeaderProposeResult at Hres
    obtain ⟨cs', Hct, Hres⟩ := Hres
    have Hrepl : PropRepl ents (leaderPropConf s ents cs' c.joint).1 :=
      propConf_repl (joint := c.joint) s.logst.applied (logLast s.logst) s.pci ents cs' Hct
    have Hps : ∀ p, toPState { s with pci := p } = toPState s := fun _ => rfl
    cases dropped
    · -- appended and broadcast
      simp only [Bool.false_eq_true, ↓reduceIte] at Hres ⊢
      obtain ⟨ms, pvs, rfl, Hms, Hpvs⟩ := Hres
      icases Herrn with %Herrn
      subst Herrn
      wp_auto
      -- the appended log does not wrap: `ownRaftLog`'s `Hnowrap` at the new state
      icases ownRaftPhysC_log_same c r id _ $$ Hphys with ⟨Hlog, Hback⟩
      icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hnw, Hlog⟩
      ihave Hphys := Hback $$ Hlog
      have Hnwe0 : plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int)
          < 2 ^ 64 := by
        have := Hrepl.length
        simp only [proposed, sendMsgs, logAppend, List.length_append, List.length_mapIdx] at Hnw
        simp only [plogLastIndexZ, toPState, List.length_append]
        push_cast at Hnw this ⊢
        omega
      have e : (k0 + if m.Type' = MsgProp then ents.length else 1) = k0 + ents.length := by
        rw [if_pos Hty]
      ihave #Hrc2 : ⧖ (k0 + ents.length) $$ [Hrcl]
      · rw [← e]; iapply Hrcl $$ %(Or.inl (And.intro Hty (by simp)))
      iapply HΦ $$ %_ %_ %(plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int))
      iframe Hphys
      isplitr
      · ipureintro; exact ⟨by omega, Int.le_refl _, Hnwe0⟩
      isplitr
      · iintro -; iexact Hrc2
      isplitr
      · ipureintro; exact nstateWf_prvals _ _ (nstateWf_sendMsgs _ _ Hwf)
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro
        have Hrl : (toPState s).role = .leader := by rw [toPState_role, Hrole]; rfl
        have Hnwb : plogLastIndexZ (toPState s).base (toPState s).log
            + ((leaderPropConf s ents cs' c.joint).1.length : Int) < 2 ^ 64 := by
          simp only [proposed, sendMsgs, logAppend, List.length_append, List.length_mapIdx] at Hnw
          simp only [plogLastIndexZ, toPState, List.length_append]
          push_cast at Hnw ⊢
          omega
        have Hnwe : plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int)
            < 2 ^ 64 := by rw [← Hrepl.length]; exact Hnwb
        generalize Hsp : ({ s with pci := (leaderPropConf s ents cs' c.joint).2 } : NState) = sp
          at Hms ⊢
        have Hspv : sp.prvals = s.prvals := by rw [← Hsp]
        rw [← Hspv] at Hpvs
        have Hsps : toPState sp = toPState s := by rw [← Hsp]; rfl
        have Hspt : sp.term = s.term := by rw [← Hsp]
        have Hspr : sp.role = .leader := by rw [← Hsp]; exact Hrole
        have Hspp : sp.progress = s.progress := by rw [← Hsp]
        have HP : toPState { sendMsgs (proposed id sp (leaderPropConf s ents cs' c.joint).1) ms with
              prvals := pvs } =
            psendMsgs (psendMsgs
              (pappend (toPState s)
                ((leaderPropConf s ents cs' c.joint).1.mapIdx
                  (stampS (toPState s).term (toPState s).sub (plastIndex (toPState s)))))
              [pselfAck id (pappend (toPState s)
                ((leaderPropConf s ents cs' c.joint).1.mapIdx
                  (stampS (toPState s).term (toPState s).sub (plastIndex (toPState s)))))]) ms := by
          rw [toPState_prvals (sendMsgs (proposed id sp (leaderPropConf s ents cs' c.joint).1) ms) pvs
            (fun _ => Hpvs), toPState_sendMsgs, toPState_proposed _ _ _ Hspr, Hsps, Hspt]
          rfl
        unfold ReplSends at Hms
        rw [toPState_proposed _ _ _ Hspr, Hsps, Hspt] at Hms
        have Hrl2 : (psendMsgs (pappend (toPState s)
              ((leaderPropConf s ents cs' c.joint).1.mapIdx
                (stampS (toPState s).term (toPState s).sub (plastIndex (toPState s)))))
            [pselfAck id (pappend (toPState s)
              ((leaderPropConf s ents cs' c.joint).1.mapIdx
                (stampS (toPState s).term (toPState s).sub (plastIndex (toPState s)))))]).role = .leader := by
          simp [psendMsgs, pappend, toPState, Hrole, proleRole]
        refine ⟨[absMsg .propose m ents ctx] ++ [], by simp, by simp, ?_, fun Adm dec g hc hd => ⟨g.cidx, .inl rfl, ?_⟩⟩
        · -- `StepC.propose` of the loop's batch, then the broadcast
          rw [HP]
          have Hpr := StepC.propose (c := c) (id := id)
            (B := plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int)) (absMsg .propose m ents ctx) (toPState s)
            (leaderPropConf s ents cs' c.joint).1 rfl Hrepl Hrl (by have := Hrepl.length; omega)
          exact .trans _ _ _ _ _ Hpr
            (StepC.sendApps _ _ Hrl2 (fun m hm => (Hms m hm).1)
              (fun m hm h => (GMap.elem_of_subseteq _ _).1 Hpc _ (by
                have := (Hms m hm).2.2.1 h
                simp only [proposed, sendMsgs] at this
                rw [Hspp] at this; exact this)))
        · -- `StepR.propose`: the loop exactly, `pendingConfIndex` moved; then the broadcast
          change StepR Adm dec id _ (rOf s g) ([absMsg .propose m ents ctx] ++ [])
            (rOf { sendMsgs (proposed id sp (leaderPropConf s ents cs' c.joint).1) ms with
              prvals := pvs } g)
          have Hpb : propBatch (rOf s g) ents cs' = leaderPropConf s ents cs' c.joint := by
            show propConf s.logst.applied (plastIndex (toPState s)) (pciR s) ents cs'
                (CfgM.joint g.cfg.cfg) =
              propConf s.logst.applied (logLast s.logst) s.pci ents cs' c.joint
            have Hli : plastIndex (toPState s) = logLast s.logst := by
              simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
              congr 1; push_cast; omega
            rw [Hli, hc]; simp [pciR, Hrole]
          have Hr : rOf { sendMsgs (proposed id sp (leaderPropConf s ents cs' c.joint).1) ms with
                prvals := pvs } g =
              { rOf s g with
                p := toPState { sendMsgs (proposed id sp (leaderPropConf s ents cs' c.joint).1) ms
                  with prvals := pvs },
                pci := (leaderPropConf s ents cs' c.joint).2 } := by
            rw [← Hsp]
            unfold rOf pciR
            simp [proposed, sendMsgs, logAppend, Hrole]
          rw [Hr, HP]
          have HprR : StepR Adm dec id _ (rOf s g) [absMsg .propose m ents ctx] _ :=
            StepR.propose (absMsg .propose m ents ctx) (rOf s g) cs' rfl Hrl Hct (Int.le_refl _)
          refine .trans _ _ _ _ _ HprR ?_
          rw [show (absMsg .propose m ents ctx).entries = ents from rfl, Hpb]
          exact StepR.sendApps _ ms Hrl2 (fun m hm => (Hms m hm).1) (fun m hm => (Hms m hm).2.1)
      ileft; ipureintro; rfl
    · -- dropped: a leader transfer in progress, or `appendEntry` refused the batch (only
      -- `pendingConfIndex` moved, 2026-10-13)
      simp only [↓reduceIte] at Hres ⊢
      rcases Hres with rfl | rfl
      all_goals cases err
      all_goals
        wp_auto
        iapply HΦ
        iframe Hphys
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
        isplitr
        · ipureintro; exact Hwf
        isplitr
        · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
        isplitr
        · ipureintro
          exact ⟨[], by simp, by simp, by
            first
            | exact StepCD.frame (.refl _) (RFrame.refl _)
            | exact stepCD_propDrop c id m s ents cs' ctx Hty Hrole Hct Hlen⟩
        iright; iexact Herrn
  · -- PreCandidate (2026-10-04), as a candidate: drop
    simp only [stepFuncOf]
    wp_apply _P.stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx
        (.inr (.inl Hty))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inr Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      $$ [$Hphys Hm] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn⟩
    · iapply msgIn_prop Hty $$ Hm
    have Hc1 := (CandidateStepResultC.cfg (by nonsnap Hty) Hres).symm
    unfold CandidateStepResultC at Hres
    replace Hres := Hres.2
    subst Hc1
    rw [ite_neg HnVR, ite_pos Hty] at Hres
    obtain ⟨rfl, rfl⟩ := Hres
    simp only [↓reduceIte]
    cases err
    all_goals
      wp_auto
      iapply HΦ
      iframe Hphys
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
      isplitr
      · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
      isplitr
      · ipureintro; exact Hwf
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro; exact ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩
      iright; iexact Herrn

end StepProof

end branches

end EtcdGrove
end Perennial
