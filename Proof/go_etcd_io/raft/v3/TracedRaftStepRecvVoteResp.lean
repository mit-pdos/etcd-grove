/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's `MsgVoteResp` of its
term, the election left pending** (2026-11-11, trace-check Q8 stage 1 slice 22b, `notes/decisions.md`,
"Q8 stage 1 (slice 22b)").

Raft records the vote (`poll`'s `RecordVote`) and, the tally neither won nor lost, does nothing more;
the specification's receive line records it in `HandleRequestVoteResponse` (amendment A3's relaxed tally:
`phaseStepR_voteRespCand`, `fxPresR_voteRespCand`, `TracedRecvVoteResp.lean`). Which outcome `poll`
reaches depends on the step's configuration `c` as well as on the state and the message, so the path is
stated over `c` (`stepBundle_traced.onC`, `stepBundle_traced.on` with the path reading `c`; `.on` is its
case of a path not reading it, `stepBundle_traced.on_of_onC`).

**Not here** (`notes/decisions.md`, "Q8 stage 1 (slice 22b)"): the won election (its `BecomeLeader` line's
facts need the new leader's term log, which raft's ghost step creates, the close's `ownStepGhost` at `s`
then being stale, as for a leader's `MsgProp`) and the lost one (`stepClose` is handed `stepOut`, which
does not say whether the step-down's gate ran: the resource left before it, `G1`, at the lost state cannot
be closed).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRecvVoteResp
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvCand
public import Proof.go_etcd_io.raft.v3.TracedRaftStepHup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section traced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`stepBundle_traced.on` with a path that reads the step's configuration** (`c`): a candidate's
vote response's path is `poll`'s outcome, which reads it. The premises and the conclusion are
`stepBundle_traced.on`'s verbatim. -/
abbrev stepBundle_traced.onC (Path : CfgM → NState → MessageM → Prop) : Prop :=
  ∀ (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool),
  Path c s m →
  s.gh.tr = some γd →
  s.prevote = false → s.cq = false → StepEndTy m.Type' → NStateWf s →
  (m.Type' = MsgHup ∨ m.Type' = MsgBeat ∨ m.Type' = MsgProp → m.Term' = W64 0) →
  (m.Type' = MsgHup → s.role ≠ .leader) →
  (∀ ty, mtypeOf m.Type' = some ty → ty.traced = true → m.To' = id) →
  uint.Z s.term + 1 < traceNumBound → uint.Z m.Term' < traceNumBound →
  (∀ ty, mtypeOf m.Type' = some ty → MsgTrOk γ (absMsg ty m ents ctx)) →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  c.learners = ∅ → domSet s.progress ⊆ c.voters ∪ c.learners →
  s.role ≠ .preCandidate → TrRecvShape m ents →
  (m.Type' = MsgHeartbeat ∨ m.Type' = MsgApp → γ.reBoot ≠ []) →
  (trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗
      (recvTokOf γd m ents ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) ⊢
    |={⊤}=> ∃ R : StepG GF, R.G ∗ stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s R) ∗
      stepClose γ md c id m ents ctx s R
        (fun s' => iprop(∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)))

/-- A path that does not read the configuration. -/
theorem stepBundle_traced.on_of_onC {Path : NState → MessageM → Prop}
    (h : stepBundle_traced.onC (GF := GF) (hG := hG) (fun _ => Path)) :
    stepBundle_traced.on (GF := GF) (hG := hG) Path := h

/-- **A candidate's vote response of its term, the election left pending**: the recorded tally
(`recordVote`) neither a quorum of grants (`JQuorum`) nor lost (`JLost`) at the step's configuration. -/
def CandVoteRespPending (c : CfgM) (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgVoteResp ∧ m.Term' = s.term ∧ s.role = .candidate ∧
  ¬ JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∧
  ¬ JLost c (recordVote s.votes m.From' (!m.Reject'))

/-- **The resources of a pending vote response**: after the receive line (`G0`) and the preamble (`G1`)
raft's ghost state and the capability at the pinned idle phase of the state after `recordVote` (`s1`);
`False` at the others (no further gate runs). -/
def vrPendR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s s1 : NState) (γd : GName)
    (tn : TraceNames) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (Λ : Option TraceEv → Prop) (k : Nat)
    (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (IdlePin s1 tn.voters cs1 P0) (fun o => o.isSome = true))
  G1 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (IdlePin s1 tn.voters cs1 P0) (fun o => o.isSome = true))
  GE := fun _ => iprop(⌜False⌝)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **`raft.Step`'s traced bundle on a candidate's vote response of its term, the election left
pending**: the receive line (the specification's `HandleRequestVoteResponse`, amendment A3), and nothing
more; the end state is raft's after `recordVote`. -/
theorem stepBundle_traced_candVoteRespPending :
    stepBundle_traced.onC (GF := GF) (hG := hG) CandVoteRespPending := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hnq, hnl⟩ := hp
  have hmty : mtypeOf m.Type' = some .voteResp := by rw [hTy]; rfl
  have htrd : MsgType.traced .voteResp = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .voteResp m ents hmty htrd hsh
  have hto' : m.To' = id := hto .voteResp hmty htrd
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup⟩ := resp_ne (.inr (.inr hTy))
  have hmt2 : mtypeOf m.Type' = some .voteResp ∧ MsgType.traced .voteResp = true := ⟨hmty, htrd⟩
  have hnl' : s.role ≠ .leader := by rw [hrole]; decide
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.voteResp %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hidC⟩ := hI0
  obtain ⟨hmT, hmd, -, -, -, -, hvr⟩ := msgAbs_recvTy hev hma
  have hmty' : ma.type = .requestVoteResponse := hvr rfl
  have hmd' : ma.dest = idAbs id := by rw [hmd]; exact congrArg idAbs hto'
  imodintro
  iexists vrPendR bfl γ md c r id s { s with votes := recordVote s.votes m.From' (!m.Reject') } γd tn cs0
    (toC (confAbs tn.voters) (respSrv a0 ma)) P0 Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [vrPendR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, vrPendR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .voteResp m ents).NumsBelow traceNumBound := (hok .voteResp hmty hreT htrd).1
      have hps := phaseStepR_voteRespCand id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole
        hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .voteResp m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .voteResp evt bfl k ma (fun _ => False)
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · iapply fxPresR_voteRespCand γ id ma _ _ _ hmty' hmd'
        · rintro C cs P ⟨rfl, rfl, rfl, -⟩
          refine ⟨hidC, ?_⟩
          rw [hmT, ← ha0]
          show uint.Z m.Term' = a0.currentTerm
          rw [hR0.1]
          show uint.Z m.Term' = uint.Z (toPState s).term
          rw [hterm]; rfl
        · rintro C cs P cs' P' ⟨rfl, rfl, rfl, -⟩ ⟨-, rfl, hP, -⟩
          refine ⟨by simpa using hP.symm, fun a ha => ?_⟩
          exact toC_respSrv _ _ _ ma (ha0.trans ha.symm)
      · iexists tn; iframe Hdir Htok
    isplitr
    · -- the preamble: no step-down at the node's term
      unfold preGate
      iintro %_ HG0
      simp only [hnbf, ↓reduceIte]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (hns h).elim
    isplitr
    · iintro %h; exfalso; rcases h with h | h
      · exact hnV h
      · exact hnPV h
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %h; exfalso; rw [hrole] at h; cases h
      isplit
      · iintro %_
        iunfold candidateGates
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) |
          iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnq, hnl])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnq, hnl]
      · iintro %h; exfalso; rw [hrole] at h; cases h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's tally recorded, nothing more
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨pvs, hse⟩ : ∃ pvs : GMap w64 Progress,
        s' = { ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState) with prvals := pvs } := by
      obtain ⟨pvs0, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs0] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.2.1 (.inl hrole)
      unfold CandidateStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [if_pos hTy] at hf
      obtain ⟨-, hf⟩ := hf
      rw [if_neg (by rw [hrole]; decide)] at hf
      obtain ⟨won, lost, ms, pvs, hw, hl, hs'⟩ := hf
      cases won with
      | true => exact absurd (hw rfl).1 hnq
      | false =>
        cases lost with
        | true => exact absurd (hl rfl) hnl
        | false => exact ⟨pvs, hs'⟩
    subst hse
    have hmono : ∀ C cs P, IdlePin { s with votes := recordVote s.votes m.From' (!m.Reject') } tn.voters
        (toC (confAbs tn.voters) (respSrv a0 ma)) P0 C cs P →
        SimIdle C { ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState) with prvals := pvs } cs P := by
      rintro C cs P ⟨rfl, rfl, rfl, hI⟩
      rw [simIdle_iff] at hI ⊢
      refine ⟨?_, hI.2⟩
      have h := simIdleS_prvals_nl tn.voters ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState)
        pvs hnl'
      exact (congrFun h _).mpr hI.1
    have hout : OutTrStep s
        { ({ s with votes := recordVote s.votes m.From' (!m.Reject') } : NState) with prvals := pvs } := by
      intro _ x hx; exact .inl hx
    unfold stepOut
    dsimp only [vrPendR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | %h | %h | ⟨%b, %N, %h⟩)
    · iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
      · ipureintro; exact hout
    · iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
      · ipureintro; exact hout
    · exact h.elim
    · exact h.elim
    · exact h.elim

end traced

end EtcdGrove
end Perennial
