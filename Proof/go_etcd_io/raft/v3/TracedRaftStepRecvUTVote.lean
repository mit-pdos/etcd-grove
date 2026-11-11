/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a vote request of a higher term**
(2026-11-10, trace-check Q8 stage 1 slice 20b, `notes/decisions.md`, "Q8 stage 1 (slice 20b)").

Raft steps down in `Step`'s preamble (`becomeFollower(m.Term, None)`; no lease, check-quorum off), its
`BecomeFollower` line skipped (`phaseStepBF_ut`), then decides the vote at the new term and answers (the
answer's send line skipped). The specification's receive line: `UpdateTerm`, then
`HandleRequestVoteRequest` at the new term (`lineEffect_ut` with `recvAt_voteReq`); raft decides as the
specification does (`voteEnd_simIdle` at the step-down, with `simServerR_ut`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTHb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A higher-term vote request's receive line's phase step**: `UpdateTerm` (the intermediate shape,
`utSrv`, up to `toC`), then the grant decision at the new term (`vrSrv`, `vrResp`). -/
theorem phaseStepR_utVote (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .vote m ents) evt)
    (hto : m.To' = id) (hgt : uint.Z s.term < uint.Z m.Term') (hpre : s.role ≠ .preCandidate)
    (hb : (absMsg .vote m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .vote m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .vote m ents))
      (fun v => toC (confAbs C0) v = toC (confAbs C0) (utSrv a0 (uint.Z m.Term'))) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) (vrSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma))
        (P0 ++ [vrResp (utSrv a0 (uint.Z m.Term')) (idAbs id) (idAbs m.From') ma])) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC, -⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg .vote m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .vote m ents).dst s c (absMsg .vote m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .vote m ents).dst ∈ C := by rw [hdst]; exact hC
  have hC'' : idAbs (absMsg .vote m ents).dst ∈ confAbs C := by rw [mem_confAbs]; exact hC'
  obtain ⟨hmt, hmd, hmsrc, -, hv, -, -⟩ := msgAbs_recvTy hev hma
  have hph : recvPhantoms ma a = [] :=
    recvPhantoms_nolow ma a (by rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z s.term; omega)
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
  refine ⟨vrSrv (utSrv a (uint.Z m.Term')) (idAbs m.From') ma,
    [vrResp (utSrv a (uint.Z m.Term')) (idAbs id) (idAbs m.From') ma],
    ⟨rfl, toC_vrSrv _ _ _ _ _ hux, by rw [vrResp_toC _ _ _ _ _ _ hux]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have h2 := recvAt_voteReq C (idAbs (absMsg .vote m ents).dst) (utSrv a ma.term) ma hmd hC'' (hv rfl) rfl
  have := lineEffect_ut C e s c (absMsg .vote m ents) evt a _ ma _ _ hev he' hin hout hC' hR hs hpre hgt
    bt bc bl bmt bi blt bk bmc hma h2
  rw [hmt, hmsrc] at this
  exact lineEffect_mid_mono this (fun v hv => by rw [hv]; exact hux)

/-- **The facts of a higher-term vote request's receive line**: at the intermediate state `simFx_ut`,
at the result `simFx_voteReq` from it. -/
theorem fxPresR_utVote (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (L : List EntryM)
    (u0 : Etcdraft.Server) (c0 t0 T : Int) (hiC : id ∈ C0) (hdst : ma.dest = idAbs id) (hT63 : T < 2 ^ 63)
    (hbL : BootTerms C0.length 1 L) (hwr : PlogWfR (entryID.mk (W64 0) (W64 0)) L)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      toC (confAbs C0) u0 = toC (confAbs C0) (utSrv a T) ∧
      cs1 = toC (confAbs C0) (vrSrv (utSrv a T) ma.source ma) ∧
      r1 = vrResp (utSrv a T) (idAbs id) ma.source ma ∧ ma.term = T ∧
      a.currentTerm = t0 ∧ a.commitIndex = c0 ∧ a.log = logAbs C0 C0.length 1 L ∧ t0 < T) :
    logRecs (GF := GF) γ base0 L ∗ isCommitted γ (L.take c0.toNat) ∗ commitIn γ L (W64 c0) (W64 t0) ⊢
      FxPresR (GF := GF) γ id ma E (fun v => toC (confAbs C0) v = toC (confAbs C0) u0) (recvPhantoms ma)
        (IdlePin s C0 cs0 P0) (VPin C0 cs1 (P0 ++ [r1])) := by
  iintro ⟨#HL, #Hcm, #Hci⟩
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hu0, hc1, hr1, hmT, ht0, hc0, hlog, hlt⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hmT, ht0]; omega)
  icases simFx_ut γ C σ id T L hsrv hiC (by rw [hσa, ht0]; exact hlt) hT63 (by rw [hσa]; exact hlog) hbL hwr
    c0 t0 (by rw [hσa]; exact hc0) (by rw [hσa]; exact ht0) $$ [$Htbl $Hfx $HL $Hcm $Hci] with ⟨Htbl, #Hu⟩
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = withNode σ (idAbs id) (utSrv (σ.s (idAbs id)) T) _root_.id _root_.id :=
    ⟨_, rfl⟩
  rw [← hσu]
  have hσud : σu.s (idAbs id) = utSrv a T := by rw [hσu]; simp [withNode, hσa]
  ihave #H1 := simFx_voteReq γ C σu (idAbs id) ma.source ma (by rw [hσud, hmT]; exact Int.le_refl _) rfl
    (by rw [hσu]; exact hmem) hdst $$ Hu
  iframe Htbl
  isplitl
  · have hs : ∀ k, toC (withNode σu (idAbs id) (vrSrv (σu.s (idAbs id)) ma.source ma) (fun b => b.without ma)
          (fun b => b.with (vrResp (σu.s (idAbs id)) (idAbs id) ma.source ma))).server
        ((withNode σ (idAbs id) a' (fun b => b.without ma)
          (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s k) =
        toC (withNode σu (idAbs id) (vrSrv (σu.s (idAbs id)) ma.source ma) (fun b => b.without ma)
          (fun b => b.with (vrResp (σu.s (idAbs id)) (idAbs id) ma.source ma))).server
          ((withNode σu (idAbs id) (vrSrv (σu.s (idAbs id)) ma.source ma) (fun b => b.without ma)
            (fun b => b.with (vrResp (σu.s (idAbs id)) (idAbs id) ma.source ma))).s k) := by
      intro k
      show toC σu.server (if k = idAbs id then a' else σ.s k) =
        toC σu.server (if k = idAbs id then vrSrv (σu.s (idAbs id)) ma.source ma else σu.s k)
      split
      · rw [hσud, hσu]; show toC σ.server a' = toC σ.server _; rw [hsrv, hcs', hc1]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    ihave #H3 := simFx_congr γ C
      (withNode σu (idAbs id) (vrSrv (σu.s (idAbs id)) ma.source ma) (fun b => b.without ma)
        (fun b => b.with (vrResp (σu.s (idAbs id)) (idAbs id) ma.source ma)))
      (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
      (by rw [hσu]; rfl) (by rw [hσu]; rfl) (by rw [hph, hr1, hσud, hσu]; rfl) hs $$ H1
    iexact H3
  · iintro %v %hv
    have hs : ∀ k, toC σu.server ((withNode σ (idAbs id) v _root_.id _root_.id).s k) = toC σu.server (σu.s k) := by
      intro k
      show toC σu.server (if k = idAbs id then v else σ.s k) = toC σu.server (σu.s k)
      split
      · rename_i hk; subst hk
        rw [hσud, hσu]; show toC σ.server v = toC σ.server _; rw [hsrv, hv, hu0]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    ihave #H4 := simFx_congr γ C σu (withNode σ (idAbs id) v _root_.id _root_.id) (by rw [hσu]; rfl)
      (by rw [hσu]; rfl) (by rw [hσu]; rfl) hs $$ Hu
    iexact H4

end fx

section nums
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A vote answer's numbers at the step-down's state (its term the request's). -/
theorem vresp_nums_ut (id : w64) (s : NState) (m : MessageM) (pvs : GMap w64 Progress) (rej : Bool)
    (hmT : uint.Z m.Term' < traceNumBound) :
    (vrespMsgOf id { becomeFollower s m.Term' (W64 0) with prvals := pvs } m rej).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hmT
  unfold vrespMsgOf Msg.plain Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨?_, by simp, by simp, by simp, by simp, by simp⟩
  split <;> first | word | (show uint.nat m.Term' < 2 ^ 61; word)

end nums

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A vote request of a higher term than the node's.** -/
def UTVote (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgVote ∧ uint.Z s.term < uint.Z m.Term'

/-- **`raft.Step`'s traced bundle on a vote request of a higher term**: the receive line (`UpdateTerm`,
then the grant decision), the preamble's `BecomeFollower` line (skipped), then the answer's send line
(skipped); raft decides as the specification does (`voteEnd_simIdle` at the step-down). -/
theorem stepBundle_traced_utVote : stepBundle_traced.on (GF := GF) (hG := hG) UTVote := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hgt⟩ := hp
  have hmty : mtypeOf m.Type' = some .vote := by rw [hTy]; rfl
  have htrd : MsgType.traced .vote = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .vote m ents hmty htrd hsh
  have hto' : m.To' = id := hto .vote hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2 (.inl hTy) (by rw [hto', h])
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup⟩ := vote_ne hTy
  have hnS : m.Type' ≠ MsgSnap := by rw [hTy]; simp [MsgVote, MsgSnap]
  have hbf : PreBF m s := ⟨hgt, hnPV, fun h => hnPVR h.1⟩
  have hlead0 : preLead m = W64 0 := by
    unfold preLead; rw [if_neg]; rintro (h | h | h) <;> first | exact hnA h | exact hnH h | exact hnS h
  have hpre : ∀ pvs, preState s m pvs = { becomeFollower s m.Term' (W64 0) with prvals := pvs } := by
    intro pvs; simp only [preState, hbf, ↓reduceIte, hlead0]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hT63 : uint.Z m.Term' < 2 ^ 63 := by have hb : traceNumBound = 2 ^ 61 := rfl; rw [hb] at hmT; omega
  have hmt2 : mtypeOf m.Type' = some .vote ∧ MsgType.traced .vote = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.vote %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hidC⟩ := hI0
  obtain ⟨hmterm, hmd0, hms, -, -, -, -⟩ := msgAbs_recvTy hev hma
  have hmd : ma.dest = idAbs id := by rw [hmd0]; show idAbs m.To' = _; rw [hto']
  have hbL : BootTerms tn.voters.length 1 (toPState s).log := fun k e hk he => hs0.2.2 k e (by omega) he
  have hcs1 : (toC (confAbs tn.voters) (vrSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma)).state =
      Etcdraft.follower := by
    show (vrSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma).state = _
    rw [(vrSrv_fields _ _ _).2.2.2.1]; rfl
  imodintro
  iexists bfR bfl γ md c r id s γd tn cs0
    (toC (confAbs tn.voters) (vrSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma)) P0
    (P0 ++ [vrResp (utSrv a0 (uint.Z m.Term')) (idAbs id) (idAbs m.From') ma]) Λ
    (RecvLast evt id s c (absMsg .vote m ents)) (fun o => o.isSome = true) k ma
  isplitl [Hcap Htok]
  · dsimp only [bfR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, bfR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      iunfold ownStepGhost at Hgh
      icases Hgh with ⟨Hg, Hr⟩
      icases ownRaftGhost_logFacts γ id (toPState s) hs0.1 $$ Hg with ⟨Hg, ⟨#HL, #Hcm, #Hci⟩, %Hwr⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .vote m ents).NumsBelow traceNumBound := (hok .vote hmty hreT htrd).1
      have hps := phaseStepR_utVote id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hgt hnpc hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .vote m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs .vote evt bfl k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · have hW1 : W64 (uint.Z s.logst.committed) = s.logst.committed := by word
        have hW2 : W64 (uint.Z s.term) = s.term := by word
        iapply fxPresR_utVote γ id ma _ s tn.voters cs0 _ P0 _ (toPState s).log (utSrv a0 (uint.Z m.Term'))
          (uint.Z s.logst.committed) (uint.Z s.term) (uint.Z m.Term') hidC hmd hT63 hbL Hwr
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
          refine ⟨hux, by rw [hms]; exact toC_vrSrv _ _ _ _ _ hux, by rw [hms]; exact vrResp_toC _ _ _ _ _ _ hux,
            hmterm, hRa.1, hRa.2.2.2.2.2.2.1, hRa.2.2.2.2.2.1, hgt⟩
        · rw [hW1, hW2, show s.logst.committed = (toPState s).commit from rfl, show s.term = (toPState s).term from rfl]
          isplitr; · iexact HL
          isplitr; · iexact Hcm
          iexact Hci
      · iexists tn; iframe Hdir Htok
    isplitr
    · -- the preamble: the step-down's `BecomeFollower` line, skipped
      unfold preGate
      iintro %_ HG0
      simp only [hbf, ↓reduceIte]
      icases HG0 with ⟨Hgh, Hc⟩
      iapply hookGate_fupd
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      rw [htr, hlead0]
      have ht1 : uint.nat (becomeFollower s m.Term' (W64 0)).term < traceNumBound := by
        show uint.nat m.Term' < traceNumBound; word
      have hc1' : uint.nat (becomeFollower s m.Term' (W64 0)).logst.committed < traceNumBound := Hb.2
      have hl1 : uint.nat (plastIndex (toPState (becomeFollower s m.Term' (W64 0)))) < traceNumBound := Hb.1
      iapply bfGate_skip γd γ r id c (becomeFollower s m.Term' (W64 0)) tn.voters _ _ _
        (ownStepGhost γ md c id s) hcs1
        (phaseStepBF_ut id c s _ evt (absMsg .vote m ents) tn.voters _ _ (recvEv_name evt id s c _ hev) hgt rfl hT63)
        (fun e he => nodeEvOf_ok _ id _ c e _ he (by decide) ht1 hc1' hl1 (Nat.le_refl _))
      iframe Hgh Hc
    isplitr
    · iintro %h; exact (hns h).elim
    isplitr
    · -- the answer's send line, skipped by the specification
      iintro %_ %pvs %rej ⟨Hgh, Hc⟩
      rw [htr]
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      rw [hpre pvs]
      have hn := vresp_nums_ut id s m pvs rej hmT
      have ht2 : uint.nat ({ becomeFollower s m.Term' (W64 0) with prvals := pvs } : NState).term < traceNumBound := by
        show uint.nat m.Term' < traceNumBound; word
      have hvt : vrespTyOf m = MsgVoteResp := by simp [vrespTyOf, hTy]
      rw [hvt]
      iapply skipGate_vresp γd γ r id c _ _ tn.voters _ _ (ownStepGhost γ md c id s)
        (by unfold vrespMsgOf; rw [if_pos hTy]; rfl) (by simp only [vrespMsgOf, Msg.plain]; exact hne)
        (fun e ⟨mm, hmm, he⟩ => by
          simp only [List.mem_singleton] at hmm; subst hmm
          exact sendEvOf_ok _ id _ c _ e _ he (by decide) ht2 Hb.2 Hb.1 hn (Nat.le_refl _))
      iframe Hgh Hc
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %_
        iunfold followerGates
        isplitr; · iintro %hg; exact (hnA hg).elim
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
      · iintro %h; exfalso; simp [becomeFollower] at h
      · iintro %h; exfalso; simp [becomeFollower] at h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's step-down and vote decision, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨pvs, hve⟩ : ∃ pvs : GMap w64 Progress,
        VoteEnd id { becomeFollower s m.Term' (W64 0) with prvals := pvs } m s' := by
      rcases ((hend (by rw [htr]; rfl)) hty).2.2.1 hns hTy with ⟨h, -⟩ | ⟨pvs, h⟩
      · rw [hcq] at h; cases h
      · exact ⟨pvs, by rw [hpre pvs] at h; exact h⟩
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) (vrSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma))
        (P0 ++ [vrResp (utSrv a0 (uint.Z m.Term')) (idAbs id) (idAbs m.From') ma]) C cs P →
        SimIdle C s' cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0']
      exact voteEnd_simIdle tn.voters id { becomeFollower s m.Term' (W64 0) with prvals := pvs } s' m ents
        (utSrv a0 (uint.Z m.Term')) ma (simServerR_ut _ _ s a0 m.Term' pvs hR0 hgt) hs0 hT63 bc bl hTy rfl
        (by simp [becomeFollower]) hma hve
    have hout : OutTrStep s s' := by
      intro _ x hx
      rcases hve with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · exact .inr (Msg.trOk_of_nums (by unfold vrespMsgOf; split <;> (intro h; cases h)) (by unfold vrespMsgOf; split <;> (intro h; cases h)) (fun _ => vresp_nums_ut id s m pvs false hmT))
      · simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · exact .inr (Msg.trOk_of_nums (by unfold vrespMsgOf; split <;> (intro h; cases h)) (by unfold vrespMsgOf; split <;> (intro h; cases h)) (fun _ => vresp_nums_ut id s m pvs true hmT))
    have hlast : ∀ o, RecvLast evt id s c (absMsg .vote m ents) o → stepLastEv Λ o := by
      rintro o ⟨e0, rfl, -⟩; exact .inr rfl
    unfold stepOut
    dsimp only [bfR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | ⟨Hgh, Hc, -⟩ | %h | ⟨%b, %N, %h⟩)
    rotate_right 2
    · exact h.elim
    · exact h.elim
    all_goals
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      have hre : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      iframe Hgh
      isplitl [Hc]
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ hlast
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout

end paths

end EtcdGrove
end Perennial
