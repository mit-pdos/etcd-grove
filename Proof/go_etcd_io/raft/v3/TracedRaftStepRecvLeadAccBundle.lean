/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a leader's accepted `MsgAppResp` of its
term** (2026-11-11, trace-check Q8 stage 1 slice 29c, `notes/decisions.md`, "Q8 stage 1 (slice 29c)";
slice 30c, "Q8 stage 1 (slice 30c)": the path `LeadAcc` whole, after plan Q30 (a)).

The family (`leadAccR`): the receive line (slice 27c's `phaseStepR_leadAcc`, `fxPresR_leadAcc`) into
`G0`/`G1` (raft's ghost state at `s`, the capability at the receive line's result `AccPin`, the outbox
`s`'s); `"Hgcommit"` (`leadAccGate_commit`: raft's ghost state past the commit, the `Commit` line) into
`leadAccGc b N`; the sends after it (`leadAccGate_app`, `_hb`, `_resp`, `_tnow`); the close: past
`maybeCommit` raft's ghost state at the outcome's state (`CloseMid`'s third case: `maybeCommitOut`'s
outcome unique, `maybeCommitOut_unique`, so the end state's commit index is the family's), at `s`
otherwise (`CloseAt.of_traced`).

**The path** (`LeadAcc s m`): a leader of the message's term, accepted, the sender tracked, `PrvalsOk`.
(Slice 29c's path was `LeadAccNC`, `LeadAcc` and no outcome of `maybeCommit` that commits: `Step`'s result
at `G0`/`G1` did not say that `maybeCommit` had not run. Since slice 30c, plan Q30 (a), it does: `stepOutG`
guards `G0`/`G1` by `¬ LeadRan`, from `stepLeader.spec`'s guard on its `G` arm; so the close given `G0`/`G1`
is at `¬ AppRespRan`, where the end state's commit index is the node's, `AppRespAcceptedC`.)
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadAccGates
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteResp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [GoSemanticsFunctions]

/-- (slice 30c) Off `LeadRan` (`stepOutG`'s guard on `G0`/`G1`) an accepted response of the leader's term
did not reach `maybeCommit`. -/
theorem leadAcc_notRan {s : NState} {m : MessageM} (hp : LeadAcc s m) (h : ¬ LeadRan m s) :
    ¬ AppRespRan s m.From' m.Index' :=
  fun hr => h ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hr⟩

end pure

section bundle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An accepted response's resources** (see the header). -/
def leadAccR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (γd : GName) (tn : TraceNames) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg)
    (Λ : Option TraceEv → Prop) (k : Nat) (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun o => iprop(⌜o = s.outbox⌝ ∗ ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (AccPin s tn.voters cs1 P0 m.From' m.Index') (fun o => o.isSome = true))
  G1 := fun o => iprop(⌜o = s.outbox⌝ ∗ ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (AccPin s tn.voters cs1 P0 m.From' m.Index') (fun o => o.isSome = true))
  GE := fun _ => iprop(⌜False⌝)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := leadAccGc γ md c r id s m Λ

/-- **The close at `s`** (`maybeCommit` not past its gate): the capability at the receive line's result
is the idle one at the end state, whose idle server is `s`'s at `appRespMatch`'s `Match` values. -/
theorem leadAcc_closeAt (γd : GName) (γ : RaftNames) (c : CfgM) (r : Loc) (id : w64)
    (s s' : NState) (m : MessageM) (Λ : Option TraceEv → Prop) (C0 : List w64) (cs1 : ServerC)
    (P0 : List Etcdraft.Msg) (pvs : GMap w64 Progress)
    (hpvs : prvalsMatch pvs = appRespMatch s m.From' m.Index')
    (hS : ∀ C, SimIdleS C s' = SimIdleS C { s with prvals := pvs }) (ho : s'.outbox = s.outbox) {bt : Bool} :
    trCapB (GF := GF) (some γd) γ r id c true (AccPin s C0 cs1 P0 m.From' m.Index') (fun o => o.isSome = true) ⊢
      |={⊤}=> ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
        trCapB (some γd) γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ) := by
  iintro Hc
  ihave Hc : trFam (some γd) γ r id c true (fun C => SimIdleS C { s with prvals := pvs })
      (fun o => o.isSome = true) s'.outbox $$ [Hc]
  · unfold trFam
    iapply trCapB_mono (some γd) γ r id c true _ _ _
      (fun C cs P h => by
        obtain ⟨-, -, -, ⟨pvsA, hA, hI⟩, -⟩ := h
        rw [simIdle_iff] at hI
        refine ⟨?_, ?_⟩
        · have h1 := hI.1
          rw [simIdleS_prvalsEq C s pvsA pvs (hA.trans hpvs.symm)] at h1
          exact h1
        · rw [ho, hI.2]) $$ Hc
  have hS' : ∀ C, SimIdleS C { s with prvals := pvs } = SimIdleS C s' := fun C => (hS C).symm
  imod trFam_idle (some γd) γ r id c true { s with prvals := pvs } s' _ hS' $$ Hc with Hc
  imodintro
  iexists true
  isplitr; · ipureintro; exact fun _ => rfl
  iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h) $$ Hc

/-- **`raft.Step`'s traced bundle on a leader's accepted `MsgAppResp` of its term** (see the header). -/
theorem stepBundle_traced_leadAcc : stepBundle_traced.on (GF := GF) (hG := hG) LeadAcc := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  have hp0 := hp
  obtain ⟨hTy, hrej, hterm, hrole, hfp, hfv, hpok⟩ := hp0
  have hmty : mtypeOf m.Type' = some .appResp := by rw [hTy]; rfl
  have htrd : MsgType.traced .appResp = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .appResp m ents hmty htrd hsh
  have hto' : m.To' = id := hto .appResp hmty htrd
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup⟩ := resp_ne (.inl hTy)
  have hnVR : m.Type' ≠ MsgVoteResp := by rw [hTy]; simp [MsgAppResp, MsgVoteResp]
  have hnHR : m.Type' ≠ MsgHeartbeatResp := by rw [hTy]; simp [MsgAppResp, MsgHeartbeatResp]
  have hmt2 : mtypeOf m.Type' = some .appResp ∧ MsgType.traced .appResp = true := ⟨hmty, htrd⟩
  have hx : ∃ x, prvalsMatch s.prvals !! m.From' = some x := prvalsMatch_some_of_dom hfv
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.appResp %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  ihave #Hm : isMessage γ (absMsg .appResp m ents) $$ []
  · ihave #H := Hmsg $$ %MsgType.appResp %hmt2
    rw [← isMessage_absMsg_ctx γ .appResp m ents ctx ⟨by decide, by decide⟩]
    iapply isMessageC_isMessage
    iexact H
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hidC⟩ := hI0
  obtain ⟨hmT, hmd, -, -, -, hrt, -⟩ := msgAbs_recvTy hev hma
  have hmaty : ma.type = .appendEntriesResponse := hrt (.inl rfl)
  have hmd' : ma.dest = idAbs id := by rw [hmd]; exact congrArg idAbs hto'
  imodintro
  iexists leadAccR bfl γ md c r id s m γd tn cs0 (toC (confAbs tn.voters) (respSrv a0 ma)) P0 Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [leadAccR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, leadAccR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .appResp m ents).NumsBelow traceNumBound := (hok .appResp hmty hreT htrd).1
      have hps := phaseStepR_leadAcc id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hrej hterm hrole hx
        hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .appResp m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply hookGateOpt_mono s.gh.tr r _
        iprop(ownStepGhost γ md c id s ∗ trCapB (some γd) γ r id c true
          (AccPin s tn.voters (toC (confAbs tn.voters) (respSrv a0 ma)) P0 m.From' m.Index')
          (fun o => o.isSome = true))
      isplitr
      · iintro ⟨Hgh, Hc⟩
        iframe Hgh Hc
        ipureintro; rfl
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .appResp evt bfl k ma (fun _ => False) (recvPhantoms ma)
        (IdlePin s tn.voters cs0 P0) _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · iapply fxPresR_leadAcc γ id ma _ _ _ hmaty hmd'
        · rintro C cs P ⟨rfl, rfl, rfl, -⟩
          refine ⟨hidC, ?_⟩
          rw [hmT, ← ha0]
          show uint.Z m.Term' = a0.currentTerm
          rw [hR0.1]
          show uint.Z m.Term' = uint.Z (toPState s).term
          rw [hterm]; rfl
        · rintro C cs P cs' P' ⟨rfl, rfl, rfl, -⟩ ⟨-, hcs', hP, -⟩
          subst hcs'
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
    · iintro %h; exact (h.elim hnV hnPV).elim
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %h; rw [hrole] at h; cases h
      isplit
      · iintro %h; rw [hrole] at h; rcases h with h | h <;> cases h
      · iintro %_
        iunfold leaderGates
        isplitr
        · iguard_false [hnB]
        isplitr
        · iguard_false [hnRI]
        isplitr
        · iguard_false [hnRI]
        isplitr
        · iguard_false [hnTL]
        isplitr
        · iguard_false [hnTL]
        isplitr
        · rw [← htr]; iexact Hnosnap
        isplitr
        · iguard_false [hnCQ]
        isplitr
        · iguard_false [hnP]
        isplitr
        · iguard_false [hnP]
        isplitr
        · iguard_false [hnP]
        isplitr
        · iintro %h
          exfalso
          rcases h with h | ⟨-, h⟩
          · exact hnHR h
          · rw [hrej] at h; cases h
        isplitr
        · imodintro; iintro %h; exact (hnHR h).elim
        isplitr
        · -- `"Hgcommit"`: raft's ghost state past the commit, the `Commit` line
          iintro %_ %Hran %pvs' %b %N %Hpvs %Hout Hlc ⟨-, Hgh, Hc⟩
          rw [htr]
          iapply leadAccGate_commit γd γ md c r id s m ents Λ tn.voters _ P0 pvs' b N htr hp hto' Hran Hpvs
            Hout hT hfit
          iframe Hlc Hm Hgh Hc
        isplitr
        · imodintro
          iintro %_ %N %mm %o %_ %hmm HG
          rw [← htr]
          iapply leadAccGate_resp γd γ md c r id s m Λ true N mm o htr hmm $$ HG
        isplitr
        · imodintro
          iintro %_ %_ %N %k' %to %cm %o %_ %Hto %hcm HG
          rw [← htr]
          iapply leadAccGate_hb γd γ md c r id s m Λ N to cm _ o htr hrole hlrn hdom hT hfit Hto hcm $$ HG
        isplitr
        · imodintro
          iintro %_ %b %N %to %mm %o %Hto %Happ HG
          rw [← htr]
          iapply leadAccGate_app γd γ md c r id s m Λ b N to mm o htr hrole hlrn hdom hT hfit Hto Happ $$ HG
        · imodintro
          iintro %_ %b %N %o HG
          rw [← htr]
          iapply leadAccGate_tnow γd γ md c r id s m Λ b N o htr $$ HG
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand
    iunfold stepClose
    iintro %s' %B %recv %_ %hend %_ Hout
    obtain ⟨pvsF, hfe⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
    rw [hpre pvsF] at hfe
    have hsc := leadAcc_scope hp hfe
    obtain ⟨pvsE, n, hpvsE, hranE, hnranE, hlogE, hSE⟩ : ∃ (pvs : GMap w64 Progress) (n : w64),
        prvalsMatch pvs = appRespMatch s m.From' m.Index' ∧
        (AppRespRan s m.From' m.Index' → ∃ (b : Bool) (N : w64),
          maybeCommitOut c { s with prvals := pvs } b N ∧ n = (commitAt s b N).logst.committed) ∧
        (¬ AppRespRan s m.From' m.Index' → n = s.logst.committed) ∧
        s'.logst = { s.logst with committed := n } ∧
        ∀ C, SimIdleS C s' = SimIdleS C { s with logst := { s.logst with committed := n }, prvals := pvs } := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      exact leadAcc_end hp h
    unfold stepOutG
    dsimp only [leadAccR]
    icases Hout with (⟨%hg, ⟨%ho, Hgh, Hc⟩⟩ | ⟨%hg, ⟨%ho, Hgh, Hc⟩⟩ | %h | %h | ⟨%b, %N, H⟩)
    rotate_right 3
    · exact h.elim
    · exact h.elim
    · -- past `maybeCommit`: raft's ghost state at the outcome's state
      unfold leadAccGc
      icases H with ⟨%pvs, %Hp, HF⟩
      obtain ⟨hpvs, hout, hran, -⟩ := Hp
      obtain ⟨b', N', hoE, hn⟩ := hranE hran
      obtain ⟨rfl, rfl⟩ := maybeCommitOut_unique hout hoE (hpvsE.trans hpvs.symm)
      have hlogX : (commitAt { s with prvals := pvs } b N).logst = s'.logst := by
        rw [hlogE, hn]; cases b <;> rfl
      have hS : ∀ C, SimIdleS C (commitAt { s with prvals := pvs } b N) = SimIdleS C s' := by
        intro C
        rw [hSE C, hn]
        have h1 : commitAt { s with prvals := pvs } b N =
            { s with logst := { s.logst with committed := (commitAt s b N).logst.committed }, prvals := pvs } := by
          cases b <;> rfl
        rw [h1]
        exact simIdleS_prvalsEq C { s with logst := { s.logst with committed := (commitAt s b N).logst.committed } }
          pvs pvsE (hpvs.trans hpvsE.symm)
      have hX : ∀ x, x ∈ (commitAt { s with prvals := pvs } b N).outbox ↔ x ∈ s.outbox := by
        cases b <;> exact fun _ => Iff.rfl
      have hXs : TrScope (commitAt { s with prvals := pvs } b N) → TrScope s := by
        cases b <;> exact fun h => h
      ihave HF := lineF_unfilter γ md c r id (commitAt { s with prvals := pvs } b N) _ _ true s'.outbox
        (fun h x hx hxt => (hX x).2 ((hsc (hXs h)).2 x hx hxt)) $$ HF
      imod lineF_close γ md c r id (commitAt { s with prvals := pvs } b N) s' (stepLastEv Λ) true hS
          (fun h => (hsc (hXs h)).1) $$ HF
        with ⟨Hgh, ⟨%HtyX, %bb, %hbb, Hc⟩, %Hot⟩
      imodintro
      isplitl [Hgh]
      · iright
        iexists commitAt { s with prvals := pvs } b N
        iframe Hgh
        ipureintro
        exact .inr (.inr ⟨hTy, hrole, hterm, hrej, hfp, pvs, b, N, hpvs, rfl, hlogX⟩)
      have hXtr : (commitAt { s with prvals := pvs } b N).gh.tr = some γd := by rw [commitAt_gh]; exact htr
      rw [hXtr]
      isplitl [Hc]
      · isplitr
        · ipureintro
          intro hts hs0
          have hs' := hsc hs0
          refine ⟨hs'.1, fun x hx => ?_⟩
          rcases (HtyX (by rw [hXtr]; rfl) (by cases b <;> exact hs0)).2 x hx with h | h
          · exact .inl ((hX x).1 h)
          · exact .inr h
        iexists bb
        isplitr; · ipureintro; exact fun _ => hbb rfl
        iexact Hc
      ipureintro
      cases b <;> exact Hot
    all_goals
      -- `maybeCommit` not run (`stepOutG`'s guard, slice 30c): the close at `s`
      have hn := hnranE (leadAcc_notRan hp hg.2)
      have hS : ∀ C, SimIdleS C s' = SimIdleS C { s with prvals := pvsE } := by
        intro C; rw [hSE C, hn]
      imod leadAcc_closeAt γd γ c r id s s' m Λ tn.voters _ P0 pvsE hpvsE hS ho (bt := bfl) $$ Hc with Hc
      imodintro
      isplitl [Hgh]
      · ileft; iframe Hgh; ipureintro; exact CloseAt.of_traced hmty htrd
      isplitl [Hc]
      · isplitr
        · ipureintro
          exact fun _ h => ⟨(hsc h).1, fun x hx => .inl (ho ▸ hx)⟩
        iexact Hc
      ipureintro
      exact outTrStep_of_outOk (by rw [ho]; exact outOk_self s)

end bundle

end EtcdGrove
end Perennial
