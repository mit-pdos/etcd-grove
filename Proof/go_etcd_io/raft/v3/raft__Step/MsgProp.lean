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

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
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

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- `proposed` (`Spec/stepLeader.lean`) is `StepC.propose`'s state: the log grows by the
batch stamped at the leader's term and the indices after the last one, and the
self-acknowledgement at the new last index is queued. (Checked 2026-10-02: the physical
definition and the rule agree; nothing needed changing.) -/
private theorem toPState_proposed (id : w64) (s : NState) (ents : List EntryM) :
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

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- `if` on a decided condition (Mathlib's `if_pos`/`if_neg`, deprecated here). -/
private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

omit [GooseInterp] [GooseSemantics] go_gctx in
private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- A proposal the leader drops after the conf-change loop moved `pendingConfIndex`
(2026-10-14, stage B7): nothing the protocol sees, `StepR.propDrop` in the dynamic model. -/
private theorem stepCD_propDrop (c : CfgM) (id : w64) (m : MessageM) (s : NState)
    (ents : List EntryM) (cs : List (Option ConfChangeIM)) (ctx : List w8)
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

/-- (2026-11-11, slice 23a) `stepLeader`'s conf-change loop keeps a batch of no conf-change entry
whole, `pendingConfIndex` unchanged. -/
theorem propConf_noConf_fold (joint : Bool) (applied li : w64) (ents : List EntryM)
    (cs : List (Option ConfChangeIM)) (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    ∀ acc : List EntryM × w64,
      (ents.zip cs).foldl (propConfStep joint applied li) acc = (acc.1 ++ ents, acc.2) := by
  revert hnc
  induction hct with
  | nil => intro _ acc; simp
  | @cons e o es os ho _ ih =>
    intro hnc acc
    have hn : o = none := by
      have h1 : o.isSome = false := by
        rw [ho]; simp only [decide_eq_false_iff_not]; exact hnc e (List.mem_cons_self ..)
      cases o with
      | none => rfl
      | some _ => simp at h1
    subst hn
    simp only [List.zip_cons_cons, List.foldl_cons, propConfStep]
    rw [ih (fun e' he' => hnc e' (List.mem_cons_of_mem _ he'))]
    simp

theorem leaderPropConf_noConf (s : NState) (ents : List EntryM) (cs : List (Option ConfChangeIM))
    (joint : Bool) (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    leaderPropConf s ents cs joint = (ents, s.pci) := by
  unfold leaderPropConf propConf
  rw [propConf_noConf_fold joint _ _ ents cs hct hnc]
  simp

/-- (slice 23a) The proposed state's log is past `s`'s (a non-empty batch appended). -/
theorem proposed_logst_ne (id : w64) (s : NState) (ents : List EntryM) (hne : ents ≠ []) :
    (proposed id s ents).logst ≠ s.logst := by
  intro h
  have h1 := congrArg (fun l => l.uents.length) h
  simp only [proposed, sendMsgs, logAppend, List.length_append, List.length_mapIdx] at h1
  exact hne (List.eq_nil_of_length_eq_zero (by omega))

/-- (slice 23a) **The broadcast after a proposal, alone** (`StepC.sendApps`/`StepR.sendApps`), from a
leader's state `s1`: the step `Step` takes from the proposed state the closing wand gave raft's ghost
state back at. -/
theorem stepCD_sendApps [GoSemanticsFunctions] (c : CfgM) (id : w64) (B : Int) (m : MessageM) (s1 : NState) (ms : List Msg)
    (pvs : GMap w64 Progress) (hrole : s1.role = .leader) (Hms : ReplSends id s1 ms)
    (Hpvs : prvalsMatch pvs = prvalsMatch s1.prvals) (Hpc : domSet s1.progress ⊆ c.voters ∪ c.learners) :
    StepCD c id B m s1 [] { sendMsgs s1 ms with prvals := pvs } := by
  have HP : toPState { sendMsgs s1 ms with prvals := pvs } = psendMsgs (toPState s1) ms := by
    rw [toPState_prvals (sendMsgs s1 ms) pvs (fun _ => Hpvs), toPState_sendMsgs]
  have Hrl : (toPState s1).role = .leader := by rw [toPState_role, hrole]; rfl
  refine ⟨?_, fun Adm dec g hc hd => ⟨g.cidx, .inl rfl, ?_⟩⟩
  · rw [HP]
    exact StepC.sendApps _ _ Hrl (fun m hm => (Hms m hm).1)
      (fun m hm h => (GMap.elem_of_subseteq _ _).1 Hpc _ ((Hms m hm).2.2.1 h))
  · have Hr : rOf { sendMsgs s1 ms with prvals := pvs } { g with cidx := g.cidx } =
        { rOf s1 g with p := psendMsgs (rOf s1 g).p ms } := by
      unfold rOf pciR
      rw [HP]
      simp [sendMsgs] <;> rfl
    rw [Hr]
    exact StepR.sendApps _ ms Hrl (fun m hm => (Hms m hm).1) (fun m hm => (Hms m hm).2.1)

theorem proposed_role (id : w64) (s : NState) (ents : List EntryM) (h : s.role = .leader) :
    (proposed id s ents).role = .leader := by
  simp [proposed, sendMsgs, h]

theorem proposed_gh (id : w64) (s : NState) (ents : List EntryM) : (proposed id s ents).gh = s.gh := rfl

theorem proposed_storage (id : w64) (s : NState) (ents : List EntryM) :
    (proposed id s ents).logst.storage = s.logst.storage := rfl

/-- (slice 23a) The new messages' numbers from the proposed state (whose outbox is `s`'s and the
self-acknowledgement). -/
theorem outTrStep_proposed (id : w64) (s : NState) (ents : List EntryM) (s' : NState)
    (h : OutTrStep s s') : OutTrStep (proposed id s ents) s' := by
  intro htr x hx
  rcases h htr x hx with h1 | h1
  · left; simp only [proposed, sendMsgs]; exact List.mem_append_left _ h1
  · right; exact h1

/-- (slice 23a) The dynamic premises of a leader's proposal, at a state with room for a batch. -/
theorem gmodePre_prop_leader {md : GMode} {m : MessageM} {ents : List EntryM} {s1 : NState}
    (hty : m.Type' = MsgProp) (hrole : s1.role = .leader)
    (hb : plogLastIndexZ (toPState s1).base (toPState s1).log + 2 ^ 61 < 2 ^ 64) : md.Pre m ents s1 := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    exact ⟨fun _ hp => absurd (hrole.symm.trans hp) (by decide),
      fun h => absurd (hty.symm.trans h) (by w32_ne), fun _ => hb⟩

/-- (slice 23a) A proposal's step keeps the mode (`GMove`: no ghost part moves). -/
theorem stepOut_prop_md {md md' : GMode} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState}
    (hty : m.Type' = MsgProp) (h : md.StepOut c id m s s' md') : md' = md := by
  cases md with
  | static => exact h.1
  | dyn dec c0 h0 g =>
    obtain ⟨g', hmv, rfl, -⟩ := h
    rcases hmv with ⟨h1, -⟩ | rfl | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (hty.symm.trans h1) (by w32_ne)
    · rfl
    · exact absurd (hty.symm.trans h1) (by w32_ne)
    · exact absurd (hty.symm.trans h1) (by w32_ne)

/-- (slice 23a) **A proposal's whole step, the model's witness at the mode unchanged** (`StepCD`, the
dynamic premises at `s`). -/
theorem stepOut_of_stepCD_prop {md : GMode} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState}
    {B : Int} {recv : List Msg} (Hstep : StepCD c id B m s recv s') (hty : m.Type' = MsgProp)
    (Hdyn : ∀ dec c0 h0 g, md = .dyn dec c0 h0 g → g.cfg.cfg = c ∧ DynHyp (effDec dec g.decs) m s s' g) :
    md.StepOut c id m s s' md := by
  cases md with
  | static => exact ⟨rfl, B, recv, Hstep.1⟩
  | dyn dec c0 h0 g =>
    obtain ⟨hc, hd⟩ := Hdyn dec c0 h0 g rfl
    obtain ⟨cidx', Hcm, HR⟩ := Hstep.2 (AdmFold (effDec dec g.decs) c0) (effDec dec g.decs) g hc hd
    have hci : cidx' = g.cidx := by
      rcases Hcm with h | ⟨h, -⟩
      · exact h
      · exact absurd (hty.symm.trans h) (by w32_ne)
    subst hci
    exact ⟨g, .inr (.inl rfl), rfl, B, recv, HR⟩

/-- (slice 23a) The dynamic mode's facts at `s`, read off (its configuration and invariant). -/
theorem ghostRest_dynFacts (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) :
    ghostRest (GF := GF) γ md c id s ⊢
      ⌜∀ dec c0 h0 g, md = .dyn dec c0 h0 g → g.cfg.cfg = c ∧ RInv (effDec dec g.decs) c0 (rOf s g)⌝ ∗
        ghostRest γ md c id s := by
  cases md with
  | static =>
    iintro H
    iframe H
    ipureintro; intro _ _ _ _ h; cases h
  | dyn dec c0 h0 g =>
    unfold ghostRest
    simp only [ghostRestM]
    iintro ⟨%Hn, ⟨%Hd, H0, H1⟩, H2⟩
    isplitr
    · ipureintro; intro dec' c0' h0' g' h; cases h; exact ⟨Hd.2.1, Hd.2.2⟩
    iframe H0 H1 H2
    isplitr
    · ipureintro; exact Hn
    ipureintro; exact Hd

/-- (slice 23a) A proposal's entries' data, from its `isMessage`. -/
theorem isMessage_propose_data (γ : RaftNames) (m : MessageM) (ents : List EntryM) (ctx : List w8) :
    isMessage (GF := GF) γ (absMsg .propose m ents ctx) ⊢ [∗list] e ∈ ents, propData γ e := by
  unfold isMessage absMsg absMsgFrom
  iintro ⟨-, H⟩
  iexact H

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
theorem wp_Step_MsgProp
    -- (2026-10-29, stage U5) the four callee specs this branch uses, not `raft.Step.Postulates`:
    -- `raft.appliedTo` steps its automatic leave through this branch, so its proof cannot take
    -- the specs of `Step`'s other callees (`appliedTo` among them)
    -- (2026-11-10, Q8 stage 1 slice 11; until then their untraced instances) the gated specs
    (wp_traceReceiveMessage : traceReceiveMessage.gatedTriple (GF := GF) (hG := hG))
    (wp_stepFollower : stepFollower.spec (GF := GF) (hG := hG))
    (wp_stepCandidate : stepCandidate.spec (GF := GF) (hG := hG))
    (wp_stepLeader : stepLeader.spec (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (cs : List (Option ConfChangeIM)) (k0 : Nat) (R : StepG GF) :
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
    -- (2026-10-22, D38a) a forwarded message has no responses (`stepFollower`'s premise)
    rs = [] →
    -- (2026-11-10, Q8 stage 1 slice 11; until then `s.gh.tr = none`) a traced node proposes no
    -- configuration change (`stepLeader`'s premise, P3)
    (s.gh.tr ≠ none → ∀ e ∈ ents, ¬ IsConfEnt e) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the proposal, its entry pointers owned
        "Hm" ∷ msgIn ml (DFrac.own 1) ⟨m, ents, sn, ctx, rs⟩ ∗
        -- (2026-10-13) the conf-change entries' bytes
        "#Hcc" ∷ ccEntsOk ents cs ∗
        -- (2026-10-18, D19b stage 5) a time receipt, for `appendEntry`
        "#Hrc" ∷ ⧖ k0 ∗
        -- (2026-11-10, Q8 stage 1 slice 11) the caller's resource and `Step`'s gates
        "HG" ∷ R.G ∗ "Hgates" ∷ stepGates c r id s m ents sn ctx rs R ∗
        -- (2026-11-11, slice 23a) at a leader, the loan to the `Replicate` gate (`StepG.Tp`) from
        -- `appendEntry`'s receipt
        "HTp" ∷ (⌜s.role = .leader⌝ -∗ ⧖ (k0 + ents.length) -∗ R.Tp ents) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (B : Int), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        -- (Q8 stage 1 slice 11) the caller's resource
        "HG" ∷ stepOut R s'.outbox ∗
        -- (2026-10-18, D19b stage 5) the bound `B` of the indices the step creates: the log's last
        -- index, or past it by the batch when appended, which the receipt then covers
        "%HBb" ∷ ⌜plogLastIndexZ (toPState s).base (toPState s).log ≤ B ∧
          B ≤ plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int) ∧
          B < 2 ^ 64⌝ ∗
        "Hrcb" ∷ (⌜plogLastIndexZ (toPState s).base (toPState s).log < B⌝ -∗
          ⧖ (k0 + ents.length)) ∗
        -- (Q8 stage 1 slice 13) the end state on the path (`StepEnd`, `LemmasStepGates.lean`)
        "%Hend" ∷ ⌜StepEnd c id m ents ctx s s'⌝ ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- what `RawNode` keeps track of is untouched (2026-10-09)
        "%Hframe" ∷ ⌜LocalFrame s s' ∧ s'.logst.applying = s.logst.applying⌝ ∗
        -- (2026-10-29, stage U5) and `applied` (what `appliedTo`'s leave keeps)
        "%Happl" ∷ ⌜s'.logst.applied = s.logst.applied⌝ ∗
        -- (2026-10-25, T-M M2b) a pre-candidate keeps its log and commit index (`PreKeep`)
        "%Hpk" ∷ ⌜s.role = .preCandidate → PreKeep s s'⌝ ∗
        -- Either one step from `s` consuming at most the proposal (forwarded or
        -- dropped), or -- appended at the leader -- the `StepC.propose` state's premises
        -- and one step from that state on (the broadcast), so that `Step` can take
        -- `StepC.propose`'s ghost update with the registry
        -- (`ownRaftGhost_step_propose_reg`) and the uniform one for the rest
        -- (2026-10-06).
        -- (2026-10-14, stage B7: the whole step, the proposal received when it is forwarded
        -- or appended; until then the appended case handed `Step` `StepC.propose`'s premises)
        -- (2026-11-11, slice 23a) at a leader, for a batch of no conf change: from the proposed state
        -- by the broadcast alone when the batch was appended (with the room `StepR`'s premise asks of
        -- the end state's log), else from `s` receiving nothing (dropped)
        "%Hlead" ∷ ⌜s.role = .leader → (∀ e ∈ ents, ¬ IsConfEnt e) →
          ((proposed id s ents).logst = s'.logst →
            StepCD c id (plogLastIndexZ (toPState (proposed id s ents)).base
              (toPState (proposed id s ents)).log) m (proposed id s ents) [] s' ∧
            plogLastIndexZ (toPState s').base (toPState s').log + 2 ^ 61 < 2 ^ 64) ∧
          ((proposed id s ents).logst ≠ s'.logst →
            StepCD c id (plogLastIndexZ (toPState s).base (toPState s).log) m s [] s')⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .propose m ents ctx) ∧
              recv.length ≤ 1 ∧ StepCD c id B m s recv s'⌝ ∗
        "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) }} := by
  intro Hty Hterm Hfrom Hne Hlen Hlok Hlnz Hwf HL Hnors Htr
  wp_start as ⟨Hphys, Hm, #Hcc, #Hrc, HG, Hgates, HTp⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  iunfold stepGates at Hgates
  icases Hgates with ⟨Hgrecv, Hgpre, Hglow, Hgvresp, Hghup, Hgstep, %Hgok⟩
  wp_apply wp_traceReceiveMessage c r id s ml _ ⟨m, _, _, _, _⟩ _
      (fun _ h => (by rw [Hty]; w32_ne : m.Type' ≠ MsgSnap) (mtypeOf_Snap _ h))
    $$ [Hphys Hm Hgrecv HG] as ⟨Hphys, Hm, HG⟩
  · iframe Hphys Hm
    iapply Hgrecv; iexact HG
  try wp_auto
  wp_get _Q
  rw [decide_eq_true Hterm]
  wp_auto
  wp_drive _Q
  -- a local message: the preamble skipped
  have hnbf : ¬ PreBF m s := PreBF.of_zero Hterm
  imod preGate_nobf c r id s m _ _ (.inl Hterm) hnbf $$ Hgpre HG with HG
  wp_apply raft.wp_load_stepC $$ Hphys as Hphys
  rw [show s.stepfn = stepFuncOf s.role from Hwf.1]
  have HnVR : m.Type' ≠ MsgVoteResp := by rw [Hty]; w32_ne
  cases Hrole : s.role
  · -- Follower: forward to the leader, or drop. `send` wants the entries read-only.
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    gates_fol
    wp_apply wp_stepFollower c ∅ r id s ml m ents sn rs (zero_val _) ctx R.G1 R.GE
        (.inr (.inl Hty))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne)) (by intro Hc; first | (exfalso; rcases Hc with Hc | Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne)) | (exfalso; rcases Hc with Hc | Hc | Hc <;> simp_all [MsgApp, MsgHeartbeat, MsgSnap]) | simp_all [becomeFollower, resetTo, resetTo0])
        (fun _ => ⟨Hfrom, Hterm, Hlok Hrole⟩)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by exfalso; rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun _ => Hnors) Hgok.1 Hgok.2.1 (by xtr_tac) $$ [$Hphys Hm $Hsrc0 $HG $Hfg] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn, HGo⟩
    · iapply msgIn_prop Hty $$ Hm
    ihave HG := stepOut_or R _ _ $$ HGo
    have Hres0 := Hres
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
        try phys_out
        iapply HΦ
        iframe Hphys HG
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
        isplitr
        · ipureintro; exact StepEnd.fn_nobf hnbf (notStale_of_zero Hterm) (by rw [Hty]; w32_ne)
            (by rw [Hty]; w32_ne) (StepFnEnd.follower Hrole Hres0)
        isplitr
        · ipureintro; exact Hwf
        isplitr
        · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro; first | exact fun _ => ⟨rfl, rfl, rfl, fun h => h, Int.le_refl _⟩ | exact fun h => by cases h | exact fun h => absurd (h.symm.trans Hrole) (by decide)
        isplitr
        · ipureintro; intro h; exfalso; first | cases h | (rw [Hrole] at h; cases h)
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
      try phys_out
      iapply HΦ
      iframe Hphys HG
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
      isplitr
      · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
      isplitr
      · ipureintro; exact StepEnd.fn_nobf hnbf (notStale_of_zero Hterm) (by rw [Hty]; w32_ne)
          (by rw [Hty]; w32_ne) (StepFnEnd.follower Hrole Hres0)
      isplitr
      · ipureintro; exact nstateWf_sendMsgs _ _ Hwf
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; first | exact fun _ => ⟨rfl, rfl, rfl, fun h => h, Int.le_refl _⟩ | exact fun h => by cases h | exact fun h => absurd (h.symm.trans Hrole) (by decide)
      isplitr
      · ipureintro; intro h; exfalso; first | cases h | (rw [Hrole] at h; cases h)
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
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    gates_cand
    wp_apply wp_stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx R.G1 R.GE R.Gf R.Gb1 R.Gb2 0
        (.inr (.inl Hty))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inl Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      Hgok.1 Hgok.2.2.1 Hgok.2.1 $$ [$Hphys $Hrc00 Hm $Hsrc0 $HG $Hcg] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn, HGo⟩
    · iapply msgIn_prop Hty $$ Hm
    ihave HG := stepOut_or R _ _ $$ HGo
    have Hres0 := Hres
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
      try phys_out
      iapply HΦ
      iframe Hphys HG
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
      isplitr
      · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
      isplitr
      · ipureintro; exact StepEnd.fn_nobf hnbf (notStale_of_zero Hterm) (by rw [Hty]; w32_ne)
          (by rw [Hty]; w32_ne) (StepFnEnd.candidate (.inl Hrole) Hres0)
      isplitr
      · ipureintro; exact Hwf
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; first | exact fun _ => ⟨rfl, rfl, rfl, fun h => h, Int.le_refl _⟩ | exact fun h => by cases h | exact fun h => absurd (h.symm.trans Hrole) (by decide)
      isplitr
      · ipureintro; intro h; exfalso; first | cases h | (rw [Hrole] at h; cases h)
      isplitr
      · ipureintro; exact ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩
      iright; iexact Herrn
  · -- Leader: append and broadcast, or drop
    simp only [stepFuncOf]
    icases ownRaftPhysC_dom c r id s $$ Hphys with ⟨%Hpc, Hphys⟩
    -- (slice 23a) the leader's gates at `stepLeader`'s loan (the receipt), from `Step`'s
    ihave Hlg := stepFnGates_leader c r id s m _ _ R ∅ s (preState_nobf hnbf ∅) Hrole $$ Hgstep
    ihave Hlg := leaderGates_tp c r id s m ents (R.Tp ents) iprop(⧖ (k0 + ents.length)) _ _ _ _ _
      $$ [HTp Hlg]
    · iframe Hlg; iintro %_ Hr; iapply HTp $$ %(by first | trivial | exact Hrole) Hr
    iunfold leaderGates at Hlg
    wp_apply wp_stepLeader c r id s ml m ents sn ctx rs k0 R.G1 R.GE R.Gp1 R.Gp2 R.Gc (.inr (.inr (.inr (.inr (.inl Hty))))) Hrole (by intro Hc; exfalso; first | (rcases Hc with Hc | Hc <;> rw [Hty] at Hc <;> exact absurd Hc (by w32_ne)) | (rcases Hc with Hc | Hc <;> simp_all [MsgBeat, MsgTransferLeader]))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | ⟨Hc, -⟩ <;> exact absurd Hc (by w32_ne))
        (fun _ => ⟨Hne, Hlen, Hlnz Hrole⟩)
        (fun Hc => by exfalso; rw [Hty] at Hc; rcases Hc with Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      (fun _ h => Htr h) Hgok.2.1 Hgok.2.2.2.1 Hgok.2.2.2.2 (by xtr_tac) (by ltr_tac) $$ [$Hphys $Hrc Hm $HG $Hlg] as %err %s' %dropped ⟨Hphys, Hrcl, %Hres, Herrn, HGo⟩
    · isplitl [Hm]
      · iapply msgIn_prop Hty $$ Hm
      · iintro _; iexists cs; iexact Hcc
    ihave HG := stepOut_leader R _ _ _ _ $$ HGo
    have Hres0 := Hres
    unfold LeaderStepResultC at Hres
    rw [ite_pos Hty] at Hres
    unfold LeaderProposeResult at Hres
    obtain ⟨cs', Hct, Hlv, Hres⟩ := Hres
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
      icases ownRaftLog_last_bound _ _ $$ Hlog with ⟨%Hlb, Hlog⟩
      ihave Hphys := Hback $$ Hlog
      have Hnwe0 : plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int)
          < 2 ^ 64 := by
        have := Hrepl.length
        simp only [proposed, sendMsgs, logAppend, List.length_append, List.length_mapIdx] at Hnw
        simp only [plogLastIndexZ, toPState, List.length_append]
        push_cast at Hnw this ⊢
        omega
      ihave #Hrc2 := Hrcl $$ %(And.intro Hty (by simp))
      try phys_out
      iapply HΦ $$ %_ %_ %(plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int))
      iframe Hphys HG
      isplitr
      · ipureintro; exact ⟨by omega, Int.le_refl _, Hnwe0⟩
      isplitr
      · iintro -; iexact Hrc2
      isplitr
      · ipureintro; exact StepEnd.fn_nobf hnbf (notStale_of_zero Hterm) (by rw [Hty]; w32_ne)
          (by rw [Hty]; w32_ne) (StepFnEnd.leader Hrole Hres0)
      isplitr
      · ipureintro; exact nstateWf_prvals _ _ (nstateWf_sendMsgs _ _ Hwf)
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; first | exact fun _ => ⟨rfl, rfl, rfl, fun h => h, Int.le_refl _⟩ | exact fun h => by cases h | exact fun h => absurd (h.symm.trans Hrole) (by decide)
      isplitr
      · -- (slice 23a) from the proposed state, the broadcast alone
        ipureintro
        intro _ hnc
        have Hpc0 := leaderPropConf_noConf s ents cs' c.joint Hct hnc
        have hss : ({ s with pci := (leaderPropConf s ents cs' c.joint).2 } : NState) = s := by
          rw [Hpc0]
        rw [hss, Hpc0] at Hms ⊢
        refine ⟨fun _ => ⟨stepCD_sendApps c id _ m _ ms pvs (by simp [proposed, sendMsgs, Hrole]) Hms
            (by simpa [proposed, sendMsgs] using Hpvs) (by simpa [proposed, sendMsgs] using Hpc), ?_⟩,
          fun h => absurd (by simp [sendMsgs]) h⟩
        simp only [plogLastIndexZ, toPState, sendMsgs, proposed, logAppend, Hpc0, List.length_append,
          List.length_mapIdx] at Hlb ⊢
        omega
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
        have Hspp : sp.progress = s.progress := by rw [← Hsp]
        have HP : toPState { sendMsgs (proposed id sp (leaderPropConf s ents cs' c.joint).1) ms with
              prvals := pvs } =
            psendMsgs (psendMsgs
              (pappend (toPState s)
                ((leaderPropConf s ents cs' c.joint).1.mapIdx
                  (stamp (toPState s).term (plastIndex (toPState s)))))
              [pselfAck id (pappend (toPState s)
                ((leaderPropConf s ents cs' c.joint).1.mapIdx
                  (stamp (toPState s).term (plastIndex (toPState s)))))]) ms := by
          rw [toPState_prvals (sendMsgs (proposed id sp (leaderPropConf s ents cs' c.joint).1) ms) pvs
            (fun _ => Hpvs), toPState_sendMsgs, toPState_proposed, Hsps, Hspt]
          rfl
        unfold ReplSends at Hms
        rw [toPState_proposed, Hsps, Hspt] at Hms
        have Hrl2 : (psendMsgs (pappend (toPState s)
              ((leaderPropConf s ents cs' c.joint).1.mapIdx
                (stamp (toPState s).term (plastIndex (toPState s)))))
            [pselfAck id (pappend (toPState s)
              ((leaderPropConf s ents cs' c.joint).1.mapIdx
                (stamp (toPState s).term (plastIndex (toPState s)))))]).role = .leader := by
          simp [psendMsgs, pappend, toPState, Hrole, proleRole]
        refine ⟨[absMsg .propose m ents ctx] ++ [], by simp, by simp, ?_, fun Adm dec g hc hd => ⟨g.cidx, .inl rfl, ?_⟩⟩
        · -- `StepC.propose` of the loop's batch, then the broadcast
          rw [HP]
          exact .trans _ _ _ _ _
            (.propose (absMsg .propose m ents ctx) _ (leaderPropConf s ents cs' c.joint).1 rfl Hrepl
              Hrl (by have := Hrepl.length; omega))
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
          refine .trans _ _ _ _ _
            (StepR.propose (absMsg .propose m ents ctx) (rOf s g) cs' rfl Hrl Hct
              (Int.le_refl _) Hlv) ?_
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
        try phys_out
        iapply HΦ
        iframe Hphys HG
        isplitr
        · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
        isplitr
        · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
        isplitr
        · ipureintro; exact StepEnd.fn_nobf hnbf (notStale_of_zero Hterm) (by rw [Hty]; w32_ne)
            (by rw [Hty]; w32_ne) (StepFnEnd.leader Hrole Hres0)
        isplitr
        · ipureintro; exact Hwf
        isplitr
        · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro; first | exact fun _ => ⟨rfl, rfl, rfl, fun h => h, Int.le_refl _⟩ | exact fun h => by cases h | exact fun h => absurd (h.symm.trans Hrole) (by decide)
        isplitr
        · -- (slice 23a) not appended: from `s`, nothing received
          ipureintro
          intro _ _
          refine ⟨fun h => absurd h (proposed_logst_ne id _ ents Hne), fun _ => ?_⟩
          first
          | exact StepCD.frame (.refl _) (RFrame.refl _)
          | exact stepCD_propDrop c id m _ ents cs' ctx Hty Hrole Hct Hlen
        isplitr
        · ipureintro
          exact ⟨[], by simp, by simp, by
            first
            | exact StepCD.frame (.refl _) (RFrame.refl _)
            | exact stepCD_propDrop c id m s ents cs' ctx Hty Hrole Hct Hlen⟩
        iright; iexact Herrn
  · -- PreCandidate (2026-10-04), as a candidate: drop
    simp only [stepFuncOf]
    ihave #Hsrc0 : rcvSrc (GF := GF) s.gh.sn m.Type' sn $$ []
    · iapply rcvSrc_ne; notsnap_tac
    gates_cand
    wp_apply wp_stepCandidate c ∅ r id s ml m ents sn rs (zero_val _) ctx R.G1 R.GE R.Gf R.Gb1 R.Gb2 0
        (.inr (.inl Hty))
        (fun Hc => by
          exfalso; rw [Hty] at Hc
          rcases Hc with Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne))
        (.inr Hrole)
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun _ Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
        (fun Hc => by rw [Hty] at Hc; exact absurd Hc (by w32_ne))
      Hgok.1 Hgok.2.2.1 Hgok.2.1 $$ [$Hphys $Hrc00 Hm $Hsrc0 $HG $Hcg] as %err %s1 %dropped %c1 ⟨Hphys, %Hres, Herrn, HGo⟩
    · iapply msgIn_prop Hty $$ Hm
    ihave HG := stepOut_or R _ _ $$ HGo
    have Hres0 := Hres
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
      try phys_out
      iapply HΦ
      iframe Hphys HG
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
      isplitr
      · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
      isplitr
      · ipureintro; exact StepEnd.fn_nobf hnbf (notStale_of_zero Hterm) (by rw [Hty]; w32_ne)
          (by rw [Hty]; w32_ne) (StepFnEnd.candidate (.inr Hrole) Hres0)
      isplitr
      · ipureintro; exact Hwf
      isplitr
      · ipureintro; exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; first | exact fun _ => ⟨rfl, rfl, rfl, fun h => h, Int.le_refl _⟩ | exact fun h => by cases h | exact fun h => absurd (h.symm.trans Hrole) (by decide)
      isplitr
      · ipureintro; intro h; exfalso; first | cases h | (rw [Hrole] at h; cases h)
      isplitr
      · ipureintro; exact ⟨[], by simp, by simp, StepCD.frame (.refl _) (RFrame.refl _)⟩
      iright; iexact Herrn

end StepProof

end branches

end EtcdGrove
end Perennial
