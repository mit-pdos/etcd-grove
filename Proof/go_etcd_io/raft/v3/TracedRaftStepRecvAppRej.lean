/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a follower's rejected `MsgApp` of its
term** (2026-11-10, trace-check Q8 stage 1 slice 20b, `notes/decisions.md`, "Q8 stage 1 (slice 20b)").

At or above the commit index, a request whose previous entry the log does not have is rejected
(`HandleAppResult`'s third exit): the specification's `RejectAppendEntriesRequest`
(`lineEffect_rejectRecv`), which needs `index = 0 → logterm = 0` (raft compares with the base's term
`0` and rejects such a request; the specification's `LogOK` accepts it): a request's previous entry is
in its leader's full log, from the base (`isMessage_app_index0`). The reply's hint is not read
(`msgAbs` of a rejection has `matchIndex 0`); its `LogTerm` (the hint's term) is within the trace's
number bound since `HandleAppResult` bounds it by the request's (this slice's strengthening of
`findConflictByTerm`'s spec).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvApp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **An append request at index `0` has previous term `0`**: its previous entry is in its leader's
full log, from the base `(0, 0)`. -/
theorem isMessage_app_index0 (γ : RaftNames) (m : Msg) (Hty : m.ty = .app) :
    ⊢ isMessage (GF := GF) γ m -∗ ⌜uint.Z m.index = 0 → m.logterm = W64 0⌝ := by
  iintro #Hm
  icases isMessage_app_inv γ m Hty $$ Hm with ⟨-, -, ⟨%bL, %l, %fpL, -, %HlL, #HlfL, -, -, -⟩, -⟩
  iunfold lpfull at HlfL
  icases HlfL with ⟨%F0, -, -, %HfL⟩
  ipureintro
  intro h0
  have hr := plogTermAt_some_range _ _ _ _ HlL.1
  have hfull : plogTermAt base0 (fpL ++ l) m.index = some m.logterm := by
    rw [full_term_at _ _ _ _ HfL.1 hr.1]; exact HlL.1
  have h0' : m.index = W64 0 := by word
  rw [h0'] at hfull
  unfold plogTermAt at hfull
  simp [base0_index] at hfull
  exact hfull.symm

end ghost

section pure
variable [GooseExts]

/-- `maybeAppend` succeeds only at a matching previous entry. -/
theorem plogMaybeAppend_matches {b : entryID} {es : List EntryM} {prev : entryID} {ents : List EntryM}
    {x : w64 × List EntryM} (h : plogMaybeAppend b es prev ents = some x) : PlogMatches b es prev := by
  unfold plogMaybeAppend at h
  split at h
  · assumption
  · cases h

end pure

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A rejected append request's receive line's phase step, at a follower of its term**: the
leader adopted, the rejection `rjResp` added. -/
theorem phaseStepR_appRej (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .app m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .follower)
    (hmt0 : ¬ PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))))
    (hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0)
    (hb : (absMsg .app m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .app m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .app m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) { a0 with lead := idAbs m.From' })
        (P0 ++ [rjResp a0 (idAbs id) (idAbs m.From')])) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg .app m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .app m ents).dst s c (absMsg .app m ents) e := by
    rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .app m ents).dst ∈ C := by rw [hdst]; exact hC
  have hev10 : evt = W64 10 := by
    rcases hev with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  subst hev10
  obtain ⟨hmt, -⟩ := msgAbs_recvTy hev hma
  have hnl : ¬ ma.term < a.currentTerm := by
    rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z (toPState s).term; rw [hterm]; exact Int.lt_irrefl _
  have hph := recvPhantoms_nolow ma a hnl
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hsrc : (absMsg .app m ents).src = m.From' := rfl
  refine ⟨{ a with lead := idAbs m.From' }, [rjResp a (idAbs id) (idAbs m.From')],
    ⟨rfl, toC_lead _ _ _ _ hcx, by rw [rjResp_toC _ _ _ _ _ hcx]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have := lineEffect_rejectRecv C e s c _ a ma (fun _ => False) rfl he' hin hout hC' hR hs hrole hterm
    hmt0 hlt0 bt bc bl bmc bi blt bk hma
  rw [hsrc] at this
  exact this

/-- A rejection's numbers (the node's term, the request's index, the hint and its term within the
request's). -/
theorem appRespRej_nums (id : w64) (s : NState) (dst idx ht hint lt : w64)
    (hT : uint.Z s.term + 1 < traceNumBound) (hidx : uint.nat idx < traceNumBound)
    (hlt : uint.nat lt < traceNumBound) (hht : uint.Z ht ≤ uint.Z lt) (hh : uint.Z hint ≤ uint.Z idx) :
    (appResp id s dst true idx ht hint).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hT hidx hlt
  unfold appResp Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨by word, by simp, by word, hidx, by simp, by word⟩

/-- **The idle relation after a rejected append request at a follower of its term**: raft's end state
(the leader adopted, the rejection queued, its hint whatever) is related to the specification's. -/
theorem rejEnd_simIdle (C : List w64) (id : w64) (s : NState) (m : MessageM) (a0 : Etcdraft.Server)
    (hR : SimServerR C C.length (toPState s) a0) (hs : LogShapeOk C.length (toPState s))
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (hrole : s.role = .follower) (ht hint : w64) :
    SimIdle C (sendMsgs { s with lead := m.From' }
        [appResp id { s with lead := m.From' } m.From' true m.Index' ht hint])
      (toC (confAbs C) { a0 with lead := idAbs m.From' })
      (pendAbs C s.outbox ++ [rjResp a0 (idAbs id) (idAbs m.From')]) := by
  obtain ⟨hT, hSt, hV, hL, hB, hLog, hCm, hCfg, hPc, -, -⟩ := hR
  refine ⟨_, rfl, ?_, hs, ?_, bt, bc, bl⟩
  · refine ⟨hT, ?_, hV, ?_, hB, hLog, hCm, hCfg, hPc, ?_, ?_⟩
    · rw [hSt]; simp [toPState, sendMsgs, hrole]
    · simp [toPState, sendMsgs, hrole]
    · intro h; simp [toPState, sendMsgs, hrole, proleRole] at h
    · intro h; simp [toPState, sendMsgs, hrole, proleRole] at h
  · show _ = pendAbs C (s.outbox ++ _)
    rw [pendAbs_append]
    simp [pendAbs, TraceSim.msgAbs, appResp, rjResp, hT, toPState]

end fx

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A rejected append request of the node's term at a follower** (at or above the commit index, the
log not matching its previous entry). -/
def FolAppRej (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgApp ∧ m.Term' = s.term ∧ s.role = .follower ∧ uint.Z s.logst.committed ≤ uint.Z m.Index' ∧
  ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index')

/-- **`raft.Step`'s traced bundle on a rejected append request of the node's term at a follower**: the
receive line (the specification's `RejectAppendEntriesRequest`), then the rejection's send line, which
the specification skips. The resources are `voteR`'s. -/
theorem stepBundle_traced_folAppRej : stepBundle_traced.on (GF := GF) (hG := hG) FolAppRej := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hge, hnm⟩ := hp
  have hmty : mtypeOf m.Type' = some .app := by rw [hTy]; rfl
  have htrd : MsgType.traced .app = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .app m ents hmty htrd hsh
  have hto' : m.To' = id := hto .app hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2 (.inr (.inl hTy)) (by rw [hto', h])
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  obtain ⟨hnH, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := app_ne hTy
  have hmt2 : mtypeOf m.Type' = some .app ∧ MsgType.traced .app = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.app %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  ihave #Hmc := Hmsg $$ %MsgType.app %hmt2
  ihave #Hm := isMessageC_isMessage γ _ $$ Hmc
  icases isMessage_app_index0 γ (absMsg .app m ents ctx) rfl $$ Hm with %Hi0
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hidC⟩ := hI0
  have hfa : ma.dest = idAbs id ∧ ma.source = idAbs m.From' ∧ ma.type = .appendEntriesRequest ∧
      ma.term = uint.Z m.Term' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]
    simp [hto']
  obtain ⟨hmd, hms, hmty', hmterm⟩ := hfa
  have hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0 := fun h => Hi0 (by
    show uint.Z m.Index' = 0; have := h; word)
  have hmt0 : ¬ PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))) := by
    have : W64 (uint.nat m.Index') = m.Index' := by word
    rw [this]
    have hb0 : (toPState s).base = entryID.mk (W64 0) (W64 0) := hs0.1
    intro h; apply hnm
    show PlogMatches (toPState s).base (toPState s).log _
    rw [hb0]; exact h
  imodintro
  iexists voteR bfl γ md c r id s γd tn cs0 (toC (confAbs tn.voters) { a0 with lead := idAbs m.From' }) P0
    (P0 ++ [rjResp a0 (idAbs id) (idAbs m.From')]) Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [voteR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, voteR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hreT htrd).1
      have hps := phaseStepR_appRej id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole
        hmt0 hlt0 hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .app m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .app evt bfl k ma (fun _ => False)
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · iapply fxPresR_leadReply γ id ma _ s tn.voters cs0 _ P0 _ (fun a => rjResp a (idAbs id) ma.source)
          hmd (fun _ => by simp [rjResp]) (fun _ => rfl) (fun _ => by simp [rjResp, canonMsg])
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          refine ⟨by rw [hms]; exact toC_lead _ _ _ _ hcx, by rw [hms]; exact rjResp_toC _ _ _ _ _ hcx, ?_⟩
          rw [hmterm, hRa.1, hterm]; exact Int.lt_irrefl _
        · intro σ hsrv hpv' hcq' hmem hcs hsi
          have hσR : SimServerR tn.voters tn.voters.length (toPState s) (σ.s ma.dest) :=
            simServerR_toC (ha0.trans hcs.symm) hR0
          have hf : (σ.s ma.dest).state = Etcdraft.follower := by
            rw [hσR.2.1]; simp [toPState, hrole, proleRole, roleAbs]
          have hT' : ma.term = (σ.s ma.dest).currentTerm := by rw [hmterm, hσR.1, hterm]; rfl
          have h1 := TraceSpecInv.specInv_rejectAppendEntriesRequest hsi hpv' hcq'
            (reject_step σ ma.dest ma.source ma hT' hf hpv' hcq')
          have h1' : TraceSpecInv.SpecInv (σ.reply (rjResp (σ.s ma.dest) ma.dest ma.source) ma) := h1
          have h2' := TraceSpecInv.specInv_upd_frame (i := ma.dest) (f := fun w => { w with lead := ma.source }) h1'
            rfl rfl rfl rfl rfl rfl rfl rfl
          have h2 : TraceSpecInv.SpecInv (withLead (σ.reply (rjResp (σ.s ma.dest) ma.dest ma.source) ma)
              ma.dest ma.source) := h2'
          rw [withLead_reply] at h2
          have e1 : rjResp (σ.s ma.dest) ma.dest ma.source = rjResp (σ.s ma.dest) (idAbs id) ma.source := by
            rw [hmd]
          rw [e1] at h2
          exact h2
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
      · iintro %_
        iunfold followerGates
        isplitr
        · -- the rejection's send line, skipped by the specification
          iintro %_ %s1 %mm %hres ⟨Hgh, Hc⟩
          have hx : ∃ ht hint : w64, s1 = { s with lead := m.From' } ∧
              mm = appResp id { s with lead := m.From' } m.From' true m.Index' ht hint ∧
              uint.Z hint ≤ uint.Z m.Index' ∧ uint.Z ht ≤ uint.Z m.LogTerm' := by
            unfold HandleAppResult at hres
            try simp only at hres
            rcases hres with ⟨h, -⟩ | ⟨-, lastnewi, es', ls', h, -⟩ | ⟨-, -, hint, ht, hrh, hht, h⟩
            · exact absurd h (by show ¬ uint.Z m.Index' < uint.Z s.logst.committed; omega)
            · exact absurd (plogMaybeAppend_matches h) hnm
            · obtain ⟨h1, h2⟩ := sendMsgs_one_inj h
              exact ⟨ht, hint, h1, h2, hrh.1, hht⟩
          obtain ⟨ht, hint, rfl, rfl, hhi, hht⟩ := hx
          rw [htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
          imodintro
          have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
          have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hreT htrd).1
          have hn := appRespRej_nums id { s with lead := m.From' } m.From' m.Index' ht hint m.LogTerm' hT
            hnb.2.2.2.1 hnb.2.2.1 hht hhi
          have ht2 : uint.nat s.term < traceNumBound := by word
          have hOkR : ∀ e, (∃ mm ∈ [appResp id { s with lead := m.From' } m.From' true m.Index' ht hint],
              SendEvOf (W64 11) id { s with lead := m.From' } c mm e) →
              TraceEv.Ok (elements c.incoming).length e := by
            intro e ⟨mm, hmm, he⟩
            simp only [List.mem_singleton] at hmm; subst hmm
            exact sendEvOf_ok _ id _ c _ e _ he (by decide) ht2 Hb.2 Hb.1 hn (Nat.le_refl _)
          iapply skipGate_appresp γd γ r id c _ _ tn.voters _ _ (ownStepGhost γ md c id s) rfl
            (by simp only [appResp]; exact hne) hOkR
          iframe Hgh Hc
        isplitr; · iintro %hg; exact (hnH hg).elim
        isplitr
        · iintro %hg
          rcases hg with h | h | h
          · exact (hnP h).elim
          · exact (hnRI h).elim
          · exact (hnTL h).elim
        isplitr; · iintro %hg; exact (hnTN hg).elim
        imodintro; iintro %hg; exact (hnTN hg).elim
      isplit
      · iintro %h; exfalso; rw [hrole] at h; rcases h with h | h <;> cases h
      · iintro %h; exfalso; rw [hrole] at h; cases h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's rejection, the specification's
    iapply stepClose_anyB
    iunfold stepClose
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨ht, hint, hhi, hht, hse⟩ : ∃ ht hint : w64, uint.Z hint ≤ uint.Z m.Index' ∧
        uint.Z ht ≤ uint.Z m.LogTerm' ∧
        s' = sendMsgs { s with lead := m.From' } [appResp id { s with lead := m.From' } m.From' true m.Index' ht hint] := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.1 hrole
      unfold FollowerStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [hTy] at hf
      simp [MsgVoteResp, MsgProp, MsgApp] at hf
      obtain ⟨-, hf⟩ := hf
      unfold HandleAppResult at hf
      try simp only at hf
      rcases hf with ⟨h, -⟩ | ⟨-, lastnewi, es', ls', h, -⟩ | ⟨-, -, hint, ht, hrh, hht, h⟩
      · exact absurd h (by show ¬ uint.Z m.Index' < uint.Z s.logst.committed; omega)
      · exact absurd (plogMaybeAppend_matches h) hnm
      · exact ⟨ht, hint, hrh.1, hht, h⟩
    subst hse
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) { a0 with lead := idAbs m.From' })
        (P0 ++ [rjResp a0 (idAbs id) (idAbs m.From')]) C cs P →
        SimIdle C (sendMsgs { s with lead := m.From' }
          [appResp id { s with lead := m.From' } m.From' true m.Index' ht hint]) cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0']
      exact rejEnd_simIdle tn.voters id s m a0 hR0 hs0 bt bc bl hrole ht hint
    unfold stepOut
    dsimp only [voteR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | ⟨Hgh, Hc, -⟩ | %h | ⟨%b, %N, %h⟩)
    rotate_right 2
    · exact h.elim
    · exact h.elim
    all_goals
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      have hre : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
      · ipureintro
        intro _ x hx
        simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hre htrd).1
          exact .inr (Msg.trOk_of_nums (by intro h; cases h) (by intro h; cases h) (fun _ => appRespRej_nums id _ m.From' m.Index' ht hint m.LogTerm' hT hnb.2.2.2.1
            hnb.2.2.1 hht hhi))

end paths

end EtcdGrove
end Perennial
