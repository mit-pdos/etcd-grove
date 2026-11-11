/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a stale or rejected `MsgApp` of a
higher term** (2026-11-10, trace-check Q8 stage 1 slice 20b, `notes/decisions.md`, "Q8 stage 1 (slice
20b)").

Raft steps down in `Step`'s preamble (`becomeFollower(m.Term, m.From)`, its line skipped:
`phaseStepBF_ut`), then handles the request as a follower of the new term: below the commit index the
stale exit, at or above it with the log not matching the rejection (the accepted exit is not done
here). The specification's receive line: `UpdateTerm`, then `AppendEntriesAlreadyDone`
(`recvAt_stale`, the log matching below the commit index by `ownRaftGhost_appStaleMatch` at a term at
most the request's) or `RejectAppendEntriesRequest` (`recvAt_reject`) at the new term; the facts
`simFx_ut`, then `simFx_leadReply` (`fxPresR_utLeadReply`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTVote

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section nums
variable [GooseExts]

/-- An append response's numbers, at a term within the bound (`appResp_nums`'s, the step-down's term). -/
theorem appRespU_nums (id : w64) (s : NState) (dst idx : w64) (hT : uint.Z s.term < traceNumBound)
    (hidx : uint.nat idx < traceNumBound) :
    (appResp id s dst false idx (W64 0) (W64 0)).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hT hidx
  unfold appResp Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨by word, by simp, by simp, hidx, by simp, by simp⟩

/-- A rejection's numbers, at a term within the bound (`appRespRej_nums`'s). -/
theorem appRespRejU_nums (id : w64) (s : NState) (dst idx ht hint lt : w64)
    (hT : uint.Z s.term < traceNumBound) (hidx : uint.nat idx < traceNumBound)
    (hlt : uint.nat lt < traceNumBound) (hht : uint.Z ht ≤ uint.Z lt) (hh : uint.Z hint ≤ uint.Z idx) :
    (appResp id s dst true idx ht hint).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hT hidx hlt
  unfold appResp Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨by word, by simp, by word, hidx, by simp, by word⟩

end nums

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A higher-term append request's receive line's phase step, the stale or rejected exit**:
`UpdateTerm`, then the handler (`hRA`) adopting the leader and replying `R`. -/
theorem phaseStepR_utApp (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .app m ents) evt)
    (hto : m.To' = id) (hgt : uint.Z s.term < uint.Z m.Term') (hpre : s.role ≠ .preCandidate)
    (hb : (absMsg .app m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .app m ents) = some ma)
    (R : Etcdraft.Server → Etcdraft.Msg) (hRc : ∀ x y, toC (confAbs C0) x = toC (confAbs C0) y → R x = R y)
    (hRsrc : ∀ u, (R u).source = idAbs id)
    (hRA : ∀ a, SimServerR C0 C0.length (toPState s) a →
      RecvAt C0 (idAbs id) (utSrv a (uint.Z m.Term')) { utSrv a (uint.Z m.Term') with lead := idAbs m.From' } ma
        (fun b => b.without ma) (fun b => b.with (R (utSrv a (uint.Z m.Term'))))) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .app m ents))
      (fun v => toC (confAbs C0) v = toC (confAbs C0) (utSrv a0 (uint.Z m.Term'))) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) { utSrv a0 (uint.Z m.Term') with lead := idAbs m.From' })
        (P0 ++ [R (utSrv a0 (uint.Z m.Term'))])) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC, -, -⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg .app m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .app m ents).dst s c (absMsg .app m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .app m ents).dst ∈ C := by rw [hdst]; exact hC
  obtain ⟨hmt, -, -, -, -, -, -⟩ := msgAbs_recvTy hev hma
  have hph : recvPhantoms ma a = [] :=
    recvPhantoms_nolow ma a (by rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z s.term; omega)
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
  refine ⟨{ utSrv a (uint.Z m.Term') with lead := idAbs m.From' }, [R (utSrv a (uint.Z m.Term'))],
    ⟨rfl, toC_lead _ _ _ _ hux, by rw [hRc _ _ hux]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hRsrc _
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have h2 := hRA a hR
  have hmt' : ma.term = uint.Z m.Term' := hmt
  rw [← hmt', ← hdst] at h2
  have := lineEffect_ut C e s c (absMsg .app m ents) evt a _ ma _ _ hev he' hin hout hC' hR hs hpre hgt
    bt bc bl bmt bi blt bk bmc hma h2
  rw [hmt'] at this
  exact lineEffect_mid_mono this (fun v hv => by rw [hv]; exact hux)

/-- **The facts of a higher-term append request's receive line, the stale or rejected exit**: at the
intermediate state `simFx_ut`, at the result `simFx_leadReply` (its `SpecInv` the handler's, `hspec`). -/
theorem fxPresR_utLeadReply (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (L : List EntryM)
    (u0 : Etcdraft.Server) (c0 t0 T : Int) (R : Etcdraft.Server → Etcdraft.Msg) (hiC : id ∈ C0)
    (hdst : ma.dest = idAbs id) (hT63 : T < 2 ^ 63)
    (hbL : BootTerms C0.length 1 L) (hwr : PlogWfR (entryID.mk (W64 0) (W64 0)) L)
    (hrq : ∀ a, (R a).type ≠ .appendEntriesRequest) (hre : ∀ a, (R a).entries = [])
    (hr0 : ∀ a, canonMsg (R a) = R a)
    (hra : ∀ a, AckMsg (R a) → (R a).source = ma.dest ∧ (R a).term = a.currentTerm ∧
      (R a).matchIndex = a.commitIndex)
    (hrsd : ∀ a, (R a).source = ma.dest ∧ (R a).dest = ma.source)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      toC (confAbs C0) u0 = toC (confAbs C0) (utSrv a T) ∧
      cs1 = toC (confAbs C0) { utSrv a T with lead := ma.source } ∧ r1 = R (utSrv a T) ∧ ma.term = T ∧
      a.currentTerm = t0 ∧ a.commitIndex = c0 ∧ a.log = logAbs C0 C0.length 1 L ∧ t0 < T)
    (hspec : ∀ (σ : Etcdraft.State) (a : Etcdraft.Server), σ.server = confAbs C0 → σ.preVote = false →
      σ.checkQuorum = false → ma ∈ σ.messages.domain → toC (confAbs C0) a = cs0 → σ.s ma.dest = utSrv a T →
      TraceSpecInv.SpecInv σ →
      TraceSpecInv.SpecInv (withNode σ ma.dest { σ.s ma.dest with lead := ma.source } (fun b => b.without ma)
        (fun b => b.with (R (σ.s ma.dest))))) :
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
  have hσud : σu.s ma.dest = utSrv a T := by rw [hσu, hdst]; simp [withNode, hσa]
  ihave #H1 := simFx_leadReply γ C σu ma (R (σu.s ma.dest)) ma.dest ma.source
    (hspec σu a (by rw [hσu]; exact hsrv) (by rw [hσu]; exact hpv) (by rw [hσu]; exact hcq)
      (by rw [hσu]; exact hmem) hcs hσud) (hrq _) (hre _) (hr0 _) (by rw [hσu]; exact hsrv) (hra _) (by rw [hσu]; exact hmem) (hrsd _) $$ Hu
  iframe Htbl
  isplitl
  · have hs : ∀ k, toC (withNode σu ma.dest { σu.s ma.dest with lead := ma.source } (fun b => b.without ma)
          (fun b => b.with (R (σu.s ma.dest)))).server
        ((withNode σ (idAbs id) a' (fun b => b.without ma)
          (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s k) =
        toC (withNode σu ma.dest { σu.s ma.dest with lead := ma.source } (fun b => b.without ma)
          (fun b => b.with (R (σu.s ma.dest)))).server
          ((withNode σu ma.dest { σu.s ma.dest with lead := ma.source } (fun b => b.without ma)
            (fun b => b.with (R (σu.s ma.dest)))).s k) := by
      intro k
      show toC σu.server (if k = idAbs id then a' else σ.s k) =
        toC σu.server (if k = ma.dest then { σu.s ma.dest with lead := ma.source } else σu.s k)
      rw [hσud, hdst]
      split
      · rw [hσu]; show toC σ.server a' = toC σ.server _; rw [hsrv, hcs', hc1]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    ihave #H3 := simFx_congr γ C
      (withNode σu ma.dest { σu.s ma.dest with lead := ma.source } (fun b => b.without ma)
        (fun b => b.with (R (σu.s ma.dest))))
      (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
      (by rw [hσu]; rfl) (by rw [hσu]; rfl) (by rw [hph, hr1, hσud, hσu]; rfl) hs $$ H1
    iexact H3
  · iintro %v %hv
    have hs : ∀ k, toC σu.server ((withNode σ (idAbs id) v _root_.id _root_.id).s k) = toC σu.server (σu.s k) := by
      intro k
      show toC σu.server (if k = idAbs id then v else σ.s k) = toC σu.server (σu.s k)
      split
      · rename_i hk; subst hk
        rw [← hdst, hσud, hσu]; show toC σ.server v = toC σ.server _; rw [hsrv, hv, hu0]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    ihave #H4 := simFx_congr γ C σu (withNode σ (idAbs id) v _root_.id _root_.id) (by rw [hσu]; rfl)
      (by rw [hσu]; rfl) (by rw [hσu]; rfl) hs $$ Hu
    iexact H4

end fx

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An append request of a higher term than the node's, stale at the new term** (its index below the
node's commit index) or **rejected** (at or above it, the log not matching its previous entry): the two
exits of `handleAppendEntries` after the step-down, `b` telling which. -/
def UTAppSR (b : Bool) (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgApp ∧ uint.Z s.term < uint.Z m.Term' ∧
  (b = true → uint.Z m.Index' < uint.Z s.logst.committed) ∧
  (b = false → uint.Z s.logst.committed ≤ uint.Z m.Index' ∧
    ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index'))

/-- **The reply of `UTAppSR b`'s receive line**, at the first round's server. -/
def utAppResp (b : Bool) (id from' : w64) (u : Etcdraft.Server) : Etcdraft.Msg :=
  if b then stResp u (idAbs id) (idAbs from') "app" else rjResp u (idAbs id) (idAbs from')

/-- **`raft.Step`'s traced bundle on a stale or rejected append request of a higher term**: the receive
line (`UpdateTerm`, then the specification's stale or rejecting handling), the preamble's
`BecomeFollower` line (skipped), then the response's send line (skipped). -/
theorem stepBundle_traced_utAppSR (b : Bool) : stepBundle_traced.on (GF := GF) (hG := hG) (UTAppSR b) := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hgt, hstl, hrjc⟩ := hp
  have hmty : mtypeOf m.Type' = some .app := by rw [hTy]; rfl
  have htrd : MsgType.traced .app = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .app m ents hmty htrd hsh
  have hto' : m.To' = id := hto .app hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2.1 (.inr (.inl hTy)) (by rw [hto', h])
  obtain ⟨hnH, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := app_ne hTy
  have hbf : PreBF m s := ⟨hgt, hnPV, fun h => hnPVR h.1⟩
  have hleadF : preLead m = m.From' := by unfold preLead; rw [if_pos (.inl hTy)]
  have hpre : ∀ pvs, preState s m pvs = { becomeFollower s m.Term' m.From' with prvals := pvs } := by
    intro pvs; simp only [preState, hbf, ↓reduceIte, hleadF]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hT63 : uint.Z m.Term' < 2 ^ 63 := by have hb : traceNumBound = 2 ^ 61 := rfl; rw [hb] at hmT; omega
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
      ma.subtype = "app" ∧ ma.term = uint.Z m.Term' ∧ ma.prevLogIndex = ((uint.nat m.Index' : Nat) : Int) ∧
      ma.prevLogTerm = uint.Z m.LogTerm' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]
    simp [hto']
  obtain ⟨hmd, hms, hmty', hmsub, hmterm, hmprev, hmpt⟩ := hfa
  have hwB : PlogWf base0 (toPState s).log := by have h := hs0.2.1; rw [hs0.1] at h; exact h
  have hbL : BootTerms tn.voters.length 1 (toPState s).log := fun k e hk he => hs0.2.2 k e (by omega) he
  have hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0 := fun h => Hi0 (by
    show uint.Z m.Index' = 0; have := h; word)
  have hiC' : idAbs id ∈ confAbs tn.voters := by rw [mem_confAbs]; exact hidC
  have hidxZ : ((uint.nat m.Index' : Nat) : Int) = uint.Z m.Index' := by word
  -- the reply, and the specification's handling at the new term
  have hRc : ∀ x y, toC (confAbs tn.voters) x = toC (confAbs tn.voters) y →
      utAppResp b id m.From' x = utAppResp b id m.From' y := by
    intro x y h; unfold utAppResp; split
    · exact stResp_toC _ _ _ _ _ _ h
    · exact rjResp_toC _ _ _ _ _ h
  have hRsrc : ∀ u, (utAppResp b id m.From' u).source = idAbs id := by
    intro u; unfold utAppResp; split <;> rfl
  have hRra : ∀ u, AckMsg (utAppResp b id m.From' u) → (utAppResp b id m.From' u).source = ma.dest ∧
      (utAppResp b id m.From' u).term = u.currentTerm ∧ (utAppResp b id m.From' u).matchIndex = u.commitIndex := by
    intro u h
    unfold utAppResp at h ⊢
    cases b
    · exact absurd h.2.1 (by simp [rjResp])
    · exact ⟨by simp [stResp, hmd], rfl, rfl⟩
  have hRsd : ∀ u, (utAppResp b id m.From' u).source = ma.dest ∧ (utAppResp b id m.From' u).dest = ma.source := by
    intro u; unfold utAppResp
    cases b
    · exact ⟨by simp [rjResp, hmd], by simp [rjResp, hms]⟩
    · exact ⟨by simp [stResp, hmd], by simp [stResp, hms]⟩
  have hRrq : ∀ u, (utAppResp b id m.From' u).type ≠ .appendEntriesRequest := by
    intro u; unfold utAppResp; split <;> simp [stResp, rjResp]
  have hRre : ∀ u, (utAppResp b id m.From' u).entries = [] := by
    intro u; unfold utAppResp; split <;> rfl
  have hRr0 : ∀ u, canonMsg (utAppResp b id m.From' u) = utAppResp b id m.From' u := by
    intro u; unfold utAppResp; split <;> simp [stResp, rjResp, canonMsg]
  have hcs1 : (toC (confAbs tn.voters) { utSrv a0 (uint.Z m.Term') with lead := idAbs m.From' }).state =
      Etcdraft.follower := rfl
  imodintro
  iexists bfR bfl γ md c r id s γd tn cs0
    (toC (confAbs tn.voters) { utSrv a0 (uint.Z m.Term') with lead := idAbs m.From' }) P0
    (P0 ++ [utAppResp b id m.From' (utSrv a0 (uint.Z m.Term'))]) Λ
    (RecvLast evt id s c (absMsg .app m ents)) (fun o => o.isSome = true) k ma
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
      -- the log's match at the previous entry, decided
      ihave Hgl : iprop(|={⊤}=> ⌜LogOkL ma (logAbs tn.voters tn.voters.length 1 (toPState s).log) = b⌝ ∗
          ownRaftGhost γ id (toPState s) md.isDyn) $$ [Hg]
      · cases b with
        | true =>
          imod ownRaftGhost_appStaleMatch γ id (toPState s) (absMsg .app m ents ctx) rfl (Int.le_of_lt hgt)
            hs0.1 hwB (hstl rfl) $$ Hm Hg with ⟨Hg, %Hmt0⟩
          imodintro; iframe Hg
          ipureintro
          rw [logOkL_abs _ _ ma _ (uint.nat m.Index') m.LogTerm' hmprev hmpt hbL hlt0 (by word), decide_eq_true_iff]
          unfold PlogMatches
          have : W64 (uint.nat m.Index') = m.Index' := by word
          rw [this]; exact Hmt0
        | false =>
          imodintro; iframe Hg
          ipureintro
          rw [logOkL_abs _ _ ma _ (uint.nat m.Index') m.LogTerm' hmprev hmpt hbL hlt0 (by word)]
          apply decide_eq_false
          have : W64 (uint.nat m.Index') = m.Index' := by word
          rw [this]
          intro h; apply (hrjc rfl).2
          show PlogMatches (toPState s).base (toPState s).log _
          rw [hs0.1]; exact h
      imod Hgl with ⟨%Hlok, Hg⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hreT htrd).1
      have hRA : ∀ a, SimServerR tn.voters tn.voters.length (toPState s) a →
          RecvAt tn.voters (idAbs id) (utSrv a (uint.Z m.Term')) { utSrv a (uint.Z m.Term') with lead := idAbs m.From' }
            ma (fun b => b.without ma) (fun b' => b'.with (utAppResp b id m.From' (utSrv a (uint.Z m.Term')))) := by
        intro a hRa
        have hlog' : (utSrv a (uint.Z m.Term')).log = logAbs tn.voters tn.voters.length 1 (toPState s).log :=
          hRa.2.2.2.2.2.1
        have hcm' : (utSrv a (uint.Z m.Term')).commitIndex = uint.Z s.logst.committed := hRa.2.2.2.2.2.2.1
        cases b with
        | true =>
          have := recvAt_stale tn.voters (idAbs id) (utSrv a (uint.Z m.Term')) ma hmd hiC' hmty' rfl hmterm hmsub
            (by rw [hcm', hmprev, hidxZ]; have := hstl rfl; omega) (by rw [hlog']; exact Hlok)
          rw [hms] at this
          exact this
        | false =>
          have := recvAt_reject tn.voters (idAbs id) (utSrv a (uint.Z m.Term')) ma hmd hiC' hmty' rfl hmterm
            (by rw [hlog']; exact Hlok)
          rw [hms] at this
          exact this
      have hps := phaseStepR_utApp id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hgt hnpc hnb hma
        (utAppResp b id m.From') hRc hRsrc hRA
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .app m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs .app evt bfl k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · have hW1 : W64 (uint.Z s.logst.committed) = s.logst.committed := by word
        have hW2 : W64 (uint.Z s.term) = s.term := by word
        iapply fxPresR_utLeadReply γ id ma _ s tn.voters cs0 _ P0 _ (toPState s).log (utSrv a0 (uint.Z m.Term'))
          (uint.Z s.logst.committed) (uint.Z s.term) (uint.Z m.Term') (utAppResp b id m.From') hidC hmd hT63 hbL Hwr
          hRrq hRre hRr0 hRra hRsd
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
          exact ⟨hux, by rw [hms]; exact toC_lead _ _ _ _ hux, hRc _ _ hux, hmterm, hRa.1, hRa.2.2.2.2.2.2.1,
            hRa.2.2.2.2.2.1, hgt⟩
        · intro σ a hsrv hpv' hcq' hmem hcs hσd hsi
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans hcs.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hf : (σ.s ma.dest).state = Etcdraft.follower := by rw [hσd]; rfl
          have hT' : ma.term = (σ.s ma.dest).currentTerm := by rw [hσd, hmterm]; rfl
          have hlog' : (σ.s ma.dest).log = logAbs tn.voters tn.voters.length 1 (toPState s).log := by
            rw [hσd]; exact hRa.2.2.2.2.2.1
          have hcm' : (σ.s ma.dest).commitIndex = uint.Z s.logst.committed := by
            rw [hσd]; exact hRa.2.2.2.2.2.2.1
          cases b with
          | true =>
            have hstep := handleAER_stale σ ma hf hT' hmsub (by rw [hcm', hmprev, hidxZ]; have := hstl rfl; omega)
              (by rw [hlog']; exact Hlok)
            have := TraceSpecInv.specInv_handleAppendEntriesRequest hsi
              (by rw [hsrv, hmd, mem_confAbs]; exact hidC) hmem rfl hmty' (by rw [hmsub]; decide) hpv' hcq'
              hstep _ (List.mem_singleton_self _)
            rw [staleRecvSt_eq σ ma hmsub] at this
            have e1 : stResp (σ.s ma.dest) ma.dest ma.source "app" = utAppResp true id m.From' (σ.s ma.dest) := by
              rw [hmd, hms]; rfl
            rw [e1] at this
            exact this
          | false =>
            have h1 := TraceSpecInv.specInv_rejectAppendEntriesRequest hsi hpv' hcq'
              (reject_step σ ma.dest ma.source ma hT' hf hpv' hcq')
            have h1' : TraceSpecInv.SpecInv (σ.reply (rjResp (σ.s ma.dest) ma.dest ma.source) ma) := h1
            have h2' := TraceSpecInv.specInv_upd_frame (i := ma.dest) (f := fun w => { w with lead := ma.source }) h1'
              rfl rfl rfl rfl rfl rfl rfl rfl
            have h2 : TraceSpecInv.SpecInv (withLead (σ.reply (rjResp (σ.s ma.dest) ma.dest ma.source) ma)
                ma.dest ma.source) := h2'
            rw [withLead_reply] at h2
            have e1 : rjResp (σ.s ma.dest) ma.dest ma.source = utAppResp false id m.From' (σ.s ma.dest) := by
              rw [hmd, hms]; rfl
            rw [e1] at h2
            exact h2
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
      rw [htr, hleadF]
      have ht1 : uint.nat (becomeFollower s m.Term' m.From').term < traceNumBound := by
        show uint.nat m.Term' < traceNumBound; word
      have hc1' : uint.nat (becomeFollower s m.Term' m.From').logst.committed < traceNumBound := Hb.2
      have hl1 : uint.nat (plastIndex (toPState (becomeFollower s m.Term' m.From'))) < traceNumBound := Hb.1
      iapply bfGate_skip γd γ r id c (becomeFollower s m.Term' m.From') tn.voters _ _ _
        (ownStepGhost γ md c id s) hcs1
        (phaseStepBF_ut id c s _ evt (absMsg .app m ents) tn.voters _ _ (recvEv_name evt id s c _ hev) hgt rfl hT63)
        (fun e he => nodeEvOf_ok _ id _ c e _ he (by decide) ht1 hc1' hl1 (Nat.le_refl _))
      iframe Hgh Hc
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
        · -- the response's send line, skipped by the specification
          iintro %_ %s1 %mm %hres ⟨Hgh, Hc⟩
          have hx : ∃ ht hint : w64, s1 = { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
                lead := m.From' } ∧
              mm = appResp id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
                lead := m.From' } m.From' (!b) (if b then s.logst.committed else m.Index')
                (if b then W64 0 else ht) (if b then W64 0 else hint) ∧
              uint.Z hint ≤ uint.Z m.Index' ∧ uint.Z ht ≤ uint.Z m.LogTerm' := by
            unfold HandleAppResult at hres
            try simp only at hres
            cases b with
            | true =>
              rcases hres with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
              · obtain ⟨h1, h2⟩ := sendMsgs_one_inj h
                exact ⟨W64 0, W64 0, h1, h2, by simp, by simp⟩
              · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; have := hstl rfl; omega)
              · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; have := hstl rfl; omega)
            | false =>
              rcases hres with ⟨h, -⟩ | ⟨-, lastnewi, es', ls', h, -⟩ | ⟨-, -, hint, ht, hrh, hht, h⟩
              · exact absurd h (by show ¬ uint.Z m.Index' < uint.Z s.logst.committed; have := (hrjc rfl).1; omega)
              · exact absurd (plogMaybeAppend_matches h) (hrjc rfl).2
              · obtain ⟨h1, h2⟩ := sendMsgs_one_inj h
                exact ⟨ht, hint, h1, h2, hrh.1, hht⟩
          obtain ⟨ht, hint, rfl, rfl, hhi, hht⟩ := hx
          rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).gh.tr = some γd from htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
          imodintro
          have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
          have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hreT htrd).1
          have hn : (appResp id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
                lead := m.From' } m.From' (!b) (if b then s.logst.committed else m.Index')
                (if b then W64 0 else ht) (if b then W64 0 else hint)).NumsBelow traceNumBound := by
            cases b with
            | true => exact appRespU_nums id _ m.From' s.logst.committed hmT Hb.2
            | false => exact appRespRejU_nums id _ m.From' m.Index' ht hint m.LogTerm' hmT hnb.2.2.2.1 hnb.2.2.1 hht hhi
          have ht2 : uint.nat m.Term' < traceNumBound := by word
          have hOkR : ∀ e, (∃ mm ∈ [appResp id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
                lead := m.From' } m.From' (!b) (if b then s.logst.committed else m.Index')
                (if b then W64 0 else ht) (if b then W64 0 else hint)],
              SendEvOf (W64 11) id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
                lead := m.From' } c mm e) → TraceEv.Ok (elements c.incoming).length e := by
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
      · iintro %h; exfalso; simp [becomeFollower] at h
      · iintro %h; exfalso; simp [becomeFollower] at h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's step-down and stale or rejecting handling, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend %_ Hout
    obtain ⟨pvs, ht, hint, hhi, hht, hse⟩ : ∃ (pvs : GMap w64 Progress) (ht hint : w64),
        uint.Z hint ≤ uint.Z m.Index' ∧ uint.Z ht ≤ uint.Z m.LogTerm' ∧
        s' = sendMsgs { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with lead := m.From' }
          [appResp id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with lead := m.From' }
            m.From' (!b) (if b then s.logst.committed else m.Index')
            (if b then W64 0 else ht) (if b then W64 0 else hint)] := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.1 (by simp [becomeFollower])
      unfold FollowerStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [hTy] at hf
      simp [MsgVoteResp, MsgProp, MsgApp] at hf
      obtain ⟨-, hf⟩ := hf
      unfold HandleAppResult at hf
      try simp only at hf
      cases b with
      | true =>
        rcases hf with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact ⟨pvs, W64 0, W64 0, by simp, by simp, h⟩
        · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; have := hstl rfl; omega)
        · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; have := hstl rfl; omega)
      | false =>
        rcases hf with ⟨h, -⟩ | ⟨-, lastnewi, es', ls', h, -⟩ | ⟨-, -, hint, ht, hrh, hht, h⟩
        · exact absurd h (by show ¬ uint.Z m.Index' < uint.Z s.logst.committed; have := (hrjc rfl).1; omega)
        · exact absurd (plogMaybeAppend_matches h) (hrjc rfl).2
        · exact ⟨pvs, ht, hint, hrh.1, hht, h⟩
    subst hse
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) { utSrv a0 (uint.Z m.Term') with lead := idAbs m.From' })
        (P0 ++ [utAppResp b id m.From' (utSrv a0 (uint.Z m.Term'))]) C cs P →
        SimIdle C (sendMsgs { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with lead := m.From' }
          [appResp id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with lead := m.From' }
            m.From' (!b) (if b then s.logst.committed else m.Index')
            (if b then W64 0 else ht) (if b then W64 0 else hint)]) cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0']
      cases b with
      | true =>
        exact staleEnd_simIdle tn.voters id { becomeFollower s m.Term' (W64 0) with prvals := pvs } m
          (utSrv a0 (uint.Z m.Term')) (simServerR_ut _ _ s a0 m.Term' pvs hR0 hgt) hs0 hT63 bc bl rfl
      | false =>
        exact rejEnd_simIdle tn.voters id { becomeFollower s m.Term' (W64 0) with prvals := pvs } m
          (utSrv a0 (uint.Z m.Term')) (simServerR_ut _ _ s a0 m.Term' pvs hR0 hgt) hs0 hT63 bc bl rfl ht hint
    have hlast : ∀ o, RecvLast evt id s c (absMsg .app m ents) o → stepLastEv Λ o := by
      rintro o ⟨e0, rfl, -⟩; exact .inr rfl
    unfold stepOut
    dsimp only [bfR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | ⟨Hgh, Hc, -⟩ | %h | ⟨%b', %N, %h⟩)
    rotate_right 2
    · exact h.elim
    · exact h.elim
    all_goals
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      have hre : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hre htrd).1
      have hout : OutTrStep s (sendMsgs { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
          lead := m.From' } [appResp id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
            lead := m.From' } m.From' (!b) (if b then s.logst.committed else m.Index')
            (if b then W64 0 else ht) (if b then W64 0 else hint)]) := by
        intro _ x hx
        simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · refine .inr (Msg.trOk_of_nums (by intro h; cases h) (by intro h; cases h) (fun _ => ?_))
          cases b with
          | true => exact appRespU_nums id _ m.From' s.logst.committed hmT Hb.2
          | false => exact appRespRejU_nums id _ m.From' m.Index' ht hint m.LogTerm' hmT hnb.2.2.2.1 hnb.2.2.1 hht hhi
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
