/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's `MsgVoteResp` of its
term that loses the election** (2026-11-11, trace-check Q8 stage 1 slice 24b, `notes/decisions.md`,
"Q8 stage 1 (slice 24b)").

Raft records the vote (`poll`'s `RecordVote`), finds the election lost (`JLost` at the step's
configuration, not won) and steps down at its term (`stepCandidate`'s `becomeFollower(r.Term, None)`),
logging a `BecomeFollower` line. The specification's receive line records the vote
(`HandleRequestVoteResponse`, amendment A3's relaxed tally, as for the pending election:
`phaseStepR_voteRespCand`, `fxPresR_voteRespCand`); the `BecomeFollower` line is not skipped (`bfCond`
reads the receive line: neither a higher-term receipt nor a candidate's append request,
`bfCond_voteResp`), so it is the specification's `StepDownToFollower` (`PhaseStepBF`'s second case),
from the candidate to `bfSrv` (`phaseStepBF_lost`), keeping the facts (`fxPresBF_cand`, from
`simFx_rtf` with no leader). The close knows the step-down ran: its result is guarded (`stepOutG`), and
`CandHooked` holds, so neither `G0` nor `G1` can be the step's end.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteResp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- `bfSrv` is `ReturnToFollowerState`'s server with no leader. -/
theorem bfSrv_rtfSrv (a : Etcdraft.Server) : bfSrv a = rtfSrv a Etcdraft.nil := rfl

/-- `toC` of the step-down, from `toC` of the server. -/
theorem toC_bfSrv (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (h : toC S x = toC S y) :
    toC S (bfSrv x) = toC S (bfSrv y) := by
  rw [bfSrv_rtfSrv, bfSrv_rtfSrv]; exact toC_rtfSrv S x y _ h

/-- **A `BecomeFollower` line after a candidate's receive line of a vote response of its term is not
skipped** (`bfCond`: the receipt is neither of a higher term nor an append request). -/
theorem bfCond_voteResp (id : w64) (s : NState) (c : CfgM) (m : Msg) (e0 e : TraceEv)
    (h0 : SendEvOf (W64 16) id s c m e0) (hterm : m.term = s.term) :
    bfCond (evConv e0) (evConv e) = false := by
  obtain ⟨hname0, -, ht0, -, -, -, -, -, ⟨tm, hmsg, hm⟩, -⟩ := h0
  have hn0 : e0.name = go!"ReceiveRequestVoteResponse" := by
    simp only [evtNames] at hname0; have := hname0; simp at this; exact this.symm
  unfold bfCond evConv
  simp only [hmsg, Option.map_some]
  rw [hn0, ht0, hm.2.1, hterm]
  simp [Etcdraft.isReceiveName, gsStr]
  intro h; exact absurd h (by decide)

/-- The state after a candidate's lost election (`becomeFollower(r.Term, None)` after the tally). -/
abbrev lostState (s : NState) (m : MessageM) : NState :=
  becomeFollower { s with votes := recordVote s.votes m.From' (!m.Reject') } s.term (W64 0)

/-- The tracker's step-down after a lost election, related to the specification's (`bfSrv`). -/
theorem simServerR_lost (C : List w64) (bl : Nat) (s : NState) (m : MessageM) (a : Etcdraft.Server)
    (hR : SimServerR C bl (toPState { s with votes := recordVote s.votes m.From' (!m.Reject') }) a) :
    SimServerR C bl (toPState (lostState s m)) (bfSrv a) := by
  rw [toPState_becomeFollower]
  obtain ⟨hT, -, hV, -, hB, hLog, hCm, hCfg, hPc, -, -⟩ := hR
  refine ⟨hT, ?_, ?_, ?_, hB, hLog, hCm, hCfg, hPc, ?_, ?_⟩
  · simp [bfSrv, pbecomeFollower, roleAbs]
  · simp only [bfSrv]; rw [hV]
    simp only [pbecomeFollower]
    split
    · rfl
    · rename_i h; exact absurd rfl h
  · simp [bfSrv, pbecomeFollower, idAbs, Etcdraft.nil]
  · intro h; simp [pbecomeFollower] at h
  · intro h; simp [pbecomeFollower] at h

/-- **The step-down's idle relation**: from the candidate's server at the tally (`a`) to `bfSrv a` at
the lost state. -/
theorem simIdle_lost (C : List w64) (s : NState) (m : MessageM) (a : Etcdraft.Server) (P : List Etcdraft.Msg)
    (hR : SimServerR C C.length (toPState { s with votes := recordVote s.votes m.From' (!m.Reject') }) a)
    (hs : LogShapeOk C.length (toPState { s with votes := recordVote s.votes m.From' (!m.Reject') }))
    (hP : P = pendAbs C (toPState { s with votes := recordVote s.votes m.From' (!m.Reject') }).outbox)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState { s with votes := recordVote s.votes m.From' (!m.Reject') })) < 2 ^ 63) :
    SimIdle C (lostState s m) (toC (confAbs C) (bfSrv a)) P := by
  have hps : toPState (lostState s m) = pbecomeFollower
      (toPState { s with votes := recordVote s.votes m.From' (!m.Reject') }) s.term (W64 0) :=
    toPState_becomeFollower _ _ _
  have hR' := simServerR_lost C C.length s m a hR
  refine ⟨bfSrv a, rfl, hR', ?_, ?_, bt, bc, ?_⟩
  · unfold LogShapeOk at hs ⊢; rw [hps]; exact hs
  · rw [hP, hps]; rfl
  · rw [hps]; exact bl

/-- **A candidate's lost election: the `BecomeFollower` line's phase step** (not skipped: the
specification's `StepDownToFollower`, `bfSrv`), from the tally's pinned idle phase. -/
theorem phaseStepBF_lost (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM)
    (C0 : List w64) (a1 : Etcdraft.Server) (P0 : List Etcdraft.Msg)
    (hrole : s.role = .candidate) (hterm : m.Term' = s.term) :
    PhaseStepBF id c (lostState s m)
      (IdlePin { s with votes := recordVote s.votes m.From' (!m.Reject') } C0 (toC (confAbs C0) a1) P0)
      (IdlePin (lostState s m) C0 (toC (confAbs C0) (bfSrv a1)) P0)
      (RecvLast (W64 16) id s c (absMsg .voteResp m ents)) := by
  rintro C cs P o ⟨rfl, rfl, rfl, hI⟩ hΛ _ e e0 he ho
  obtain ⟨e0', rfl, he0⟩ := hΛ
  obtain rfl : e0' = e0 := Option.some.inj ho
  have hbf := bfCond_voteResp id s c _ e0' e he0 hterm
  refine ⟨fun h => absurd (hbf.symm.trans h) (by decide), fun _ a ha => ?_⟩
  obtain ⟨a', ha', hR', hs, hP, bt, bc, bl⟩ := hI
  have hR : SimServerR C C.length (toPState { s with votes := recordVote s.votes m.From' (!m.Reject') }) a :=
    simServerR_toC (ha'.trans ha.symm) hR'
  have hst : a.state = Etcdraft.candidate := by
    rw [hR.2.1]; simp [toPState, hrole, proleRole, roleAbs]
  have hI' := simIdle_lost C s m a P hR hs hP bt bc bl
  obtain ⟨b, hb, hRb, hsb, -, bt', bc', bl'⟩ := hI'
  refine ⟨.inr hst, simServerR_toC hb hRb, hsb, by simp [becomeFollower], bt', bc', bl', rfl,
    toC_bfSrv _ _ _ ha, rfl, simIdle_lost C s m a P hR hs hP bt bc bl⟩

end pure

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A step-down's facts at the tally's candidate share** (`FxPresBF`): `ReturnToFollowerState`'s with no
leader (`simFx_rtf`, `bfSrv_rtfSrv`). -/
theorem fxPresBF_cand (γ : RaftNames) (id : w64) (s1 : NState) (C0 : List w64) (cs1 : ServerC)
    (P0 : List Etcdraft.Msg) (hid : id ∈ C0) (hrole : s1.role = .candidate) :
    ⊢ FxPresBF (GF := GF) γ id (IdlePin s1 C0 cs1 P0) := by
  iunfold FxPresBF
  imodintro
  iintro %C %P %σ %h Htbl #Hfx
  obtain ⟨⟨rfl, hcs, rfl, hI⟩, hsrv, -, -, -, -⟩ := h
  obtain ⟨a, ha, hR, -⟩ := hI
  have hc : (σ.s (idAbs id)).state = Etcdraft.candidate := by
    have h1 : a.state = (σ.s (idAbs id)).state := congrArg ServerC.state ha
    rw [← h1, hR.2.1]; simp [toPState, hrole, proleRole, roleAbs]
  have hi : idAbs id ∈ σ.server := by rw [hsrv, mem_confAbs]; exact hid
  iframe Htbl
  rw [bfSrv_rtfSrv]
  iapply simFx_rtf γ C σ (idAbs id) Etcdraft.nil hi hc
  iexact Hfx

/-- **A candidate's vote response of its term that loses the election**: the recorded tally lost
(`JLost`) and not won (`JQuorum`) at the step's configuration. -/
def CandVoteRespLost (c : CfgM) (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgVoteResp ∧ m.Term' = s.term ∧ s.role = .candidate ∧
  ¬ JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∧
  JLost c (recordVote s.votes m.From' (!m.Reject'))

/-- **The resources of a lost election**: after the receive line (`G0`) and the preamble (`G1`) raft's
ghost state and the capability at the pinned idle phase of the tally's state, the receive event last;
after the `BecomeFollower` line (`GE`) at the lost state's (`bfSrv`); `False` at the others. -/
def vrLostR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (γd : GName) (tn : TraceNames) (cs0 : ServerC) (a1 : Etcdraft.Server)
    (P0 : List Etcdraft.Msg) (Λ Λr : Option TraceEv → Prop) (k : Nat) (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true
      (IdlePin { s with votes := recordVote s.votes m.From' (!m.Reject') } tn.voters
        (toC (confAbs tn.voters) a1) P0) Λr)
  G1 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true
      (IdlePin { s with votes := recordVote s.votes m.From' (!m.Reject') } tn.voters
        (toC (confAbs tn.voters) a1) P0) Λr)
  GE := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (IdlePin (lostState s m) tn.voters (toC (confAbs tn.voters) (bfSrv a1)) P0)
      (fun o => o.isSome = true))
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **`raft.Step`'s traced bundle on a candidate's vote response of its term that loses the election**:
the receive line (the specification's `HandleRequestVoteResponse`, amendment A3), then raft's
`BecomeFollower` line, the specification's `StepDownToFollower` (not skipped: `bfCond_voteResp`); the end
state is raft's after `becomeFollower(r.Term, None)` (`lostState`, with any `Progress`). -/
theorem stepBundle_traced_candVoteRespLost :
    stepBundle_traced.onC (GF := GF) (hG := hG) CandVoteRespLost := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hnq, hlost⟩ := hp
  have hmty : mtypeOf m.Type' = some .voteResp := by rw [hTy]; rfl
  have htrd : MsgType.traced .voteResp = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .voteResp m ents hmty htrd hsh
  have hev16 : evt = W64 16 := by
    rcases hev with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  subst hev16
  have hto' : m.To' = id := hto .voteResp hmty htrd
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hhook : CandHooked c m s := ⟨hTy, hterm, hrole, .inr hlost⟩
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup⟩ := resp_ne (.inr (.inr hTy))
  have hmt2 : mtypeOf m.Type' = some .voteResp ∧ MsgType.traced .voteResp = true := ⟨hmty, htrd⟩
  have hnl' : (lostState s m).role ≠ .leader := by simp [becomeFollower]
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
  iexists vrLostR bfl γ md c r id s m γd tn cs0 (respSrv a0 ma) P0 Λ
    (RecvLast (W64 16) id s c (absMsg .voteResp m ents)) k ma
  isplitl [Hcap Htok]
  · dsimp only [vrLostR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, vrLostR]
    isplitr
    · -- the receive line, its event kept last
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .voteResp m ents).NumsBelow traceNumBound := (hok .voteResp hmty hreT htrd).1
      have hps := phaseStepR_voteRespCand id c s m ents (W64 16) tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole
        hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf (W64 16) id s c (absMsg .voteResp m ents) e →
          TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok (W64 16) id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs .voteResp (W64 16) bfl k ma (fun _ => False)
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
        dsimp only [vrLostR]
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) |
          iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnq])
        -- the step-down's `BecomeFollower` line, not skipped
        iintro %_ ⟨Hgh, Hc⟩
        iapply hookGate_fupd
        icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
        imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
        imodintro
        rw [htr]
        have ht1 : uint.nat (lostState s m).term < traceNumBound := by
          show uint.nat s.term < traceNumBound; word
        have hc1' : uint.nat (lostState s m).logst.committed < traceNumBound := Hb.2
        have hl1 : uint.nat (plastIndex (toPState (lostState s m))) < traceNumBound := Hb.1
        iapply hookGate_mono
        isplitl [Hgh]
        · iintro Hc; iframe Hgh Hc
        icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
        iapply trCapB_hookGate_bf (some γd) γ r id c c tl (lostState s m) true _ _
          (RecvLast (W64 16) id s c (absMsg .voteResp m ents)) (fun o => o.isSome = true)
          (fun _ => rfl) (fun h => by cases h)
          (fun _ => phaseStepBF_lost id c s m ents tn.voters (respSrv a0 ma) P0 hrole hterm)
          (fun h => by cases h) (fun _ _ => rfl)
          (fun _ => ⟨fun _ e he => nodeEvOf_ok _ id _ c e _ he (by decide) ht1 hc1' hl1 (Nat.le_refl _),
            fun h => by cases h⟩)
          (fun h => by cases h)
        iframe Htl Hc
        simp only [trOwn, ↓reduceIte]
        iapply fxPresBF_cand γ id { s with votes := recordVote s.votes m.From' (!m.Reject') } tn.voters _ P0
          hidC hrole
      · iintro %h; exfalso; rw [hrole] at h; cases h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's tally and step-down, the specification's; the close is guarded
    -- (`stepOutG`): the election decided, the step ends past `"Hglost"`
    iapply stepClose_anyB
    iunfold stepClose
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨pvs, hse⟩ : ∃ pvs : GMap w64 Progress, s' = { lostState s m with prvals := pvs } := by
      obtain ⟨pvs0, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs0] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.2.1 (.inl hrole)
      unfold CandidateStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [ite_eq_left hTy] at hf
      obtain ⟨-, hf⟩ := hf
      rw [ite_eq_right (by rw [hrole]; decide)] at hf
      obtain ⟨won, lost, ms, pvs, hw, -, hx, hs'⟩ := hf
      cases won with
      | true => exact absurd (hw rfl).1 hnq
      | false =>
        obtain rfl := hx rfl hlost
        exact ⟨pvs, hs'⟩
    subst hse
    have hmono : ∀ C cs P, IdlePin (lostState s m) tn.voters
        (toC (confAbs tn.voters) (bfSrv (respSrv a0 ma))) P0 C cs P →
        SimIdle C { lostState s m with prvals := pvs } cs P := by
      rintro C cs P ⟨rfl, rfl, rfl, hI⟩
      rw [simIdle_iff] at hI ⊢
      refine ⟨?_, hI.2⟩
      have h := simIdleS_prvals_nl tn.voters (lostState s m) pvs hnl'
      exact (congrFun h _).mpr hI.1
    have hout : OutTrStep s { lostState s m with prvals := pvs } := by
      intro _ x hx; exact .inl hx
    unfold stepOutG
    dsimp only [vrLostR]
    icases Hout with (⟨%hn, -⟩ | ⟨%hn, -⟩ | ⟨Hgh, Hc⟩ | %h | ⟨%b, %N, %h⟩)
    · exact (hn hhook).elim
    · exact (hn hhook).elim
    · imodintro
      isplitl [Hgh]
      · ileft; iframe Hgh; ipureintro; exact CloseAt.of_traced hmty rfl
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
      · ipureintro; exact hout
    · exact h.elim
    · exact h.elim

end paths

end EtcdGrove
end Perennial
