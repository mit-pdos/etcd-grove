/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's stale or rejected `MsgApp`
of its term** (2026-11-11, trace-check Q8 stage 1 slice 22b, `notes/decisions.md`, "Q8 stage 1 (slice
22b)").

Raft's candidate steps down (`stepCandidate`'s `becomeFollower(m.Term, m.From)`, logging a
`BecomeFollower` line) and handles the request as a follower: below the commit index the stale exit, at
or above it with the log not matching the rejection. The specification's receive line does both in two
rounds (`ReturnToFollowerState` to `rtfSrv`, then `AppendEntriesAlreadyDone` or
`RejectAppendEntriesRequest` at the follower: `lineEffect_rtfApp` with `recvAt_stale`/`recvAt_reject`),
and skips the `BecomeFollower` line by `bfCond`'s `ReturnToFollower` case (`phaseStepBF_rtf`); the
response's send line is skipped as at a follower (`skipGate_appresp`). The facts: the step-down's
(`simFx_rtf`), then `simFx_leadReply` (`fxPresR_candLeadReply`). Slice 20b's pieces put together.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTApp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **An append request's receive line at a candidate of its term: its effect**: `ReturnToFollowerState`
(the first round, to `rtfSrv`, the sender `j` adopted), then the handler at the follower (`h2`, a
one-round receipt at `rtfSrv`). -/
theorem lineEffect_rtfApp (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (a a' : Etcdraft.Server) (mabs : Etcdraft.Msg) (j : Etcdraft.ID) (fM fP : Etcdraft.Bag → Etcdraft.Bag)
    (hty : RecvEvTy m evt) (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C)
    (hout : cfg.outgoing = ∅) (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a)
    (hs : LogShapeOk C.length (toPState s)) (hrole : s.role = .candidate) (hterm : m.term = s.term)
    (hmty : mabs.type = .appendEntriesRequest) (hj : mabs.source = j)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (bmt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63)
    (bk : m.entries.length < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hmabs : TraceSim.msgAbs C C.length m = some mabs)
    (h2 : RecvAt C (idAbs m.dst) (rtfSrv a j) a' mabs fM fP) :
    LineEffect C false e (idAbs m.dst) a a' (some mabs) fM fP (· = rtfSrv a j) := by
  obtain ⟨hparse, hrecv, hpred⟩ := recvLine_full C e s cfg m evt mabs hty hev hout bmt bi blt bk bmc hmabs
  obtain ⟨hmt, hmd, -, -, -, -, -⟩ := msgAbs_recvTy hty hmabs
  have hC' : idAbs m.dst ∈ confAbs C := by rw [mem_confAbs]; exact hC
  have hst : a.state = Etcdraft.candidate := by
    rw [hR.2.1]; simp [toPState, hrole, proleRole]; rfl
  have hev' := hev
  obtain ⟨-, -, hterm', -, hcommit', hrl, hlog, ⟨xs, ys, hxs, -, -⟩, -⟩ := hev'
  apply lineEffect_recvU C e (idAbs m.dst) a (rtfSrv a j) a' mabs fM fP _ hparse rfl hrecv hpred hmd
    (srvKey_ne_of_state _ _ (by simp only [rtfSrv]; rw [hst]; decide)) _ h2
  intro σ hsrv hσi _ _
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem]; exact hC'
  refine ⟨?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs
      (by rw [hrole]; decide) hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · have := (firstRound_rtf σ mabs (idAbs m.dst) hmd hcontains hmty
      (by rw [hσi, hR.1, hmt, hterm]; rfl) (by rw [hσi]; exact hst)).1
    rw [this, rtfSt_eq, hσi, hj]

end pure

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An append request's receive line's phase step at a candidate of its term, the stale or rejected
exit**: `ReturnToFollowerState`, then the handler (`hRA`) adopting the leader and replying `R`. -/
theorem phaseStepR_candApp (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .app m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .candidate)
    (hmty : ma.type = .appendEntriesRequest) (hms : ma.source = idAbs m.From')
    (hb : (absMsg .app m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .app m ents) = some ma)
    (R : Etcdraft.Server → Etcdraft.Msg) (hRc : ∀ x y, toC (confAbs C0) x = toC (confAbs C0) y → R x = R y)
    (hRsrc : ∀ u, (R u).source = idAbs id)
    (hRA : ∀ a, SimServerR C0 C0.length (toPState s) a →
      RecvAt C0 (idAbs id) (rtfSrv a (idAbs m.From')) { rtfSrv a (idAbs m.From') with lead := idAbs m.From' } ma
        (fun b => b.without ma) (fun b => b.with (R (rtfSrv a (idAbs m.From'))))) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .app m ents))
      (fun v => toC (confAbs C0) v = toC (confAbs C0) (rtfSrv a0 (idAbs m.From'))) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) { rtfSrv a0 (idAbs m.From') with lead := idAbs m.From' })
        (P0 ++ [R (rtfSrv a0 (idAbs m.From'))])) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
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
    recvPhantoms_nolow ma a (by
      rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z s.term; rw [hterm]; exact Int.lt_irrefl _)
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hux := toC_rtfSrv _ _ _ (idAbs m.From') hcx
  refine ⟨{ rtfSrv a (idAbs m.From') with lead := idAbs m.From' }, [R (rtfSrv a (idAbs m.From'))],
    ⟨rfl, toC_lead _ _ _ _ hux, by rw [hRc _ _ hux]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hRsrc _
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have h2 := hRA a hR
  rw [← hdst] at h2
  have := lineEffect_rtfApp C e s c (absMsg .app m ents) evt a _ ma (idAbs m.From') _ _ hev he' hin hout hC'
    hR hs hrole hterm hmty hms bt bc bl bmt bi blt bk bmc hma h2
  exact lineEffect_mid_mono this (fun v hv => by rw [hv]; exact hux)

/-- **The facts of an append request's receive line at a candidate of its term, the stale or rejected
exit**: at the intermediate state the step-down's (`simFx_rtf`), at the result `simFx_leadReply` (its
`SpecInv` the handler's, `hspec`). -/
theorem fxPresR_candLeadReply (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg)
    (u0 : Etcdraft.Server) (R : Etcdraft.Server → Etcdraft.Msg) (hiC : id ∈ C0)
    (hdst : ma.dest = idAbs id)
    (hrq : ∀ a, (R a).type ≠ .appendEntriesRequest) (hre : ∀ a, (R a).entries = [])
    (hr0 : ∀ a, canonMsg (R a) = R a)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      toC (confAbs C0) u0 = toC (confAbs C0) (rtfSrv a ma.source) ∧
      cs1 = toC (confAbs C0) { rtfSrv a ma.source with lead := ma.source } ∧ r1 = R (rtfSrv a ma.source) ∧
      ma.term = a.currentTerm ∧ a.state = Etcdraft.candidate)
    (hspec : ∀ (σ : Etcdraft.State) (a : Etcdraft.Server), σ.server = confAbs C0 → σ.preVote = false →
      σ.checkQuorum = false → ma ∈ σ.messages.domain → toC (confAbs C0) a = cs0 →
      σ.s ma.dest = rtfSrv a ma.source → TraceSpecInv.SpecInv σ →
      TraceSpecInv.SpecInv (withNode σ ma.dest { σ.s ma.dest with lead := ma.source } (fun b => b.without ma)
        (fun b => b.with (R (σ.s ma.dest))))) :
    ⊢ FxPresR (GF := GF) γ id ma E (fun v => toC (confAbs C0) v = toC (confAbs C0) u0) (recvPhantoms ma)
        (IdlePin s C0 cs0 P0) (VPin C0 cs1 (P0 ++ [r1])) := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hu0, hc1, hr1, hle, hcand⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hle]; exact Int.lt_irrefl _)
  have hiσ : idAbs id ∈ σ.server := by rw [hsrv, mem_confAbs]; exact hiC
  ihave #Hu := simFx_rtf γ C σ (idAbs id) ma.source hiσ (by rw [hσa]; exact hcand) $$ Hfx
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = withNode σ (idAbs id) (rtfSrv (σ.s (idAbs id)) ma.source) _root_.id _root_.id :=
    ⟨_, rfl⟩
  rw [← hσu]
  have hσud : σu.s ma.dest = rtfSrv a ma.source := by rw [hσu, hdst]; simp [withNode, hσa]
  ihave #H1 := simFx_leadReply γ C σu ma (R (σu.s ma.dest)) ma.dest ma.source
    (hspec σu a (by rw [hσu]; exact hsrv) (by rw [hσu]; exact hpv) (by rw [hσu]; exact hcq)
      (by rw [hσu]; exact hmem) hcs hσud) (hrq _) (hre _) (hr0 _) $$ Hu
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

/-- **An append request of a candidate's term, stale** (`b = true`: its index below the commit index)
**or rejected** (`b = false`: at or above it, the log not matching its previous entry): the two exits of
`handleAppendEntries` after the candidate's step-down. -/
def CandAppSR (b : Bool) (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgApp ∧ m.Term' = s.term ∧ s.role = .candidate ∧
  (b = true → uint.Z m.Index' < uint.Z s.logst.committed) ∧
  (b = false → uint.Z s.logst.committed ≤ uint.Z m.Index' ∧
    ¬ PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index'))

/-- The candidate's step-down already has the sender as leader. -/
theorem bfState_lead (s : NState) (j : w64) (pvs : GMap w64 Progress) :
    ({ ({ becomeFollower s s.term j with prvals := pvs } : NState) with lead := j } : NState) =
      { becomeFollower s s.term j with prvals := pvs } := rfl

/-- **`raft.Step`'s traced bundle on a stale or rejected append request of a candidate's term**: the
receive line (`ReturnToFollowerState`, then the specification's stale or rejecting handling), raft's
`BecomeFollower` line (skipped: `bfCond` reads the receive line), then the response's send line, which the
specification skips. -/
theorem stepBundle_traced_candAppSR (b : Bool) : stepBundle_traced.on (GF := GF) (hG := hG) (CandAppSR b) := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hstl, hrjc⟩ := hp
  have hmty : mtypeOf m.Type' = some .app := by rw [hTy]; rfl
  have htrd : MsgType.traced .app = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .app m ents hmty htrd hsh
  have hev10 : evt = W64 10 := by
    rcases hev with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  have hto' : m.To' = id := hto .app hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2 (.inr (.inl hTy)) (by rw [hto', h])
  obtain ⟨hnH, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := app_ne hTy
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hmt2 : mtypeOf m.Type' = some .app ∧ MsgType.traced .app = true := ⟨hmty, htrd⟩
  have hT' : uint.Z s.term < traceNumBound := by omega
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
  -- the reply
  have hRc : ∀ x y, toC (confAbs tn.voters) x = toC (confAbs tn.voters) y →
      utAppResp b id m.From' x = utAppResp b id m.From' y := by
    intro x y h; unfold utAppResp; split
    · exact stResp_toC _ _ _ _ _ _ h
    · exact rjResp_toC _ _ _ _ _ h
  have hRsrc : ∀ u, (utAppResp b id m.From' u).source = idAbs id := by
    intro u; unfold utAppResp; split <;> rfl
  have hRrq : ∀ u, (utAppResp b id m.From' u).type ≠ .appendEntriesRequest := by
    intro u; unfold utAppResp; split <;> simp [stResp, rjResp]
  have hRre : ∀ u, (utAppResp b id m.From' u).entries = [] := by
    intro u; unfold utAppResp; split <;> rfl
  have hRr0 : ∀ u, canonMsg (utAppResp b id m.From' u) = utAppResp b id m.From' u := by
    intro u; unfold utAppResp; split <;> simp [stResp, rjResp, canonMsg]
  have hcs1 : (toC (confAbs tn.voters) { rtfSrv a0 (idAbs m.From') with lead := idAbs m.From' }).state =
      Etcdraft.follower := rfl
  imodintro
  iexists bfR bfl γ md c r id s γd tn cs0
    (toC (confAbs tn.voters) { rtfSrv a0 (idAbs m.From') with lead := idAbs m.From' }) P0
    (P0 ++ [utAppResp b id m.From' (rtfSrv a0 (idAbs m.From'))]) Λ
    (RecvLast evt id s c (absMsg .app m ents)) (RecvLast evt id s c (absMsg .app m ents)) k ma
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
      -- the log's match at the previous entry, decided
      ihave Hgl : iprop(|={⊤}=> ⌜LogOkL ma (logAbs tn.voters tn.voters.length 1 (toPState s).log) = b⌝ ∗
          ownRaftGhost γ id (toPState s) md.isDyn) $$ [Hg]
      · cases b with
        | true =>
          imod ownRaftGhost_appStaleMatch γ id (toPState s) (absMsg .app m ents ctx) rfl
            (by show uint.Z s.term ≤ uint.Z m.Term'; rw [hterm]; exact Int.le_refl _)
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
          RecvAt tn.voters (idAbs id) (rtfSrv a (idAbs m.From'))
            { rtfSrv a (idAbs m.From') with lead := idAbs m.From' }
            ma (fun b => b.without ma) (fun b' => b'.with (utAppResp b id m.From' (rtfSrv a (idAbs m.From')))) := by
        intro a hRa
        have hlog' : (rtfSrv a (idAbs m.From')).log = logAbs tn.voters tn.voters.length 1 (toPState s).log :=
          hRa.2.2.2.2.2.1
        have hcm' : (rtfSrv a (idAbs m.From')).commitIndex = uint.Z s.logst.committed := hRa.2.2.2.2.2.2.1
        have hmT' : ma.term = (rtfSrv a (idAbs m.From')).currentTerm := by
          show ma.term = a.currentTerm; rw [hmterm, hRa.1, hterm]; rfl
        cases b with
        | true =>
          have := recvAt_stale tn.voters (idAbs id) (rtfSrv a (idAbs m.From')) ma hmd hiC' hmty' rfl hmT' hmsub
            (by rw [hcm', hmprev, hidxZ]; have := hstl rfl; omega) (by rw [hlog']; exact Hlok)
          rw [hms] at this
          exact this
        | false =>
          have := recvAt_reject tn.voters (idAbs id) (rtfSrv a (idAbs m.From')) ma hmd hiC' hmty' rfl hmT'
            (by rw [hlog']; exact Hlok)
          rw [hms] at this
          exact this
      have hps := phaseStepR_candApp id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole hmty' hms
        hnb hma (utAppResp b id m.From') hRc hRsrc hRA
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .app m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs .app evt bfl k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · iapply fxPresR_candLeadReply γ id ma _ s tn.voters cs0 _ P0 _ (rtfSrv a0 (idAbs m.From'))
          (utAppResp b id m.From') hidC hmd hRrq hRre hRr0
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hux := toC_rtfSrv _ _ _ (idAbs m.From') hcx
          refine ⟨by rw [hms]; exact hux, by rw [hms]; exact toC_lead _ _ _ _ hux, by rw [hms]; exact hRc _ _ hux,
            by rw [hmterm, hRa.1, hterm]; rfl, ?_⟩
          rw [hRa.2.1]; simp [toPState, hrole, proleRole, roleAbs]
        · intro σ a hsrv hpv' hcq' hmem hcs hσd hsi
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans hcs.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hf : (σ.s ma.dest).state = Etcdraft.follower := by rw [hσd]; rfl
          have hT' : ma.term = (σ.s ma.dest).currentTerm := by
            rw [hσd]; show ma.term = a.currentTerm; rw [hmterm, hRa.1, hterm]; rfl
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
        isplitr
        · -- the step-down's `BecomeFollower` line, skipped
          iintro %_ ⟨Hgh, Hc⟩
          iapply hookGate_fupd
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
          imodintro
          rw [htr]
          subst hev10
          have ht1 : uint.nat (becomeFollower s s.term m.From').term < traceNumBound := by
            show uint.nat s.term < traceNumBound; word
          have hc1' : uint.nat (becomeFollower s s.term m.From').logst.committed < traceNumBound := Hb.2
          have hl1 : uint.nat (plastIndex (toPState (becomeFollower s s.term m.From'))) < traceNumBound := Hb.1
          iapply bfGate_skip γd γ r id c (becomeFollower s s.term m.From') tn.voters _ _ _
            (ownStepGhost γ md c id s) hcs1
            (phaseStepBF_rtf id c s _ (absMsg .app m ents) tn.voters _ _ hrole hterm rfl)
            (fun e he => nodeEvOf_ok _ id _ c e _ he (by decide) ht1 hc1' hl1 (Nat.le_refl _))
          iframe Hgh Hc
        isplitr
        · -- the response's send line, skipped by the specification
          iintro %_ %pvs' %s1 %mm %hres ⟨Hgh, Hc⟩
          have hx : ∃ ht hint : w64, s1 = ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) ∧
              mm = appResp id ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) m.From' (!b)
                (if b then s.logst.committed else m.Index')
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
          rw [htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
          imodintro
          have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
          have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hreT htrd).1
          have hn : (appResp id ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) m.From' (!b)
                (if b then s.logst.committed else m.Index')
                (if b then W64 0 else ht) (if b then W64 0 else hint)).NumsBelow traceNumBound := by
            cases b with
            | true => exact appRespU_nums id _ m.From' s.logst.committed hT' Hb.2
            | false => exact appRespRejU_nums id _ m.From' m.Index' ht hint m.LogTerm' hT' hnb.2.2.2.1 hnb.2.2.1 hht hhi
          have ht2 : uint.nat s.term < traceNumBound := by word
          have hOkR : ∀ e, (∃ mm ∈ [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState)
                m.From' (!b) (if b then s.logst.committed else m.Index')
                (if b then W64 0 else ht) (if b then W64 0 else hint)],
              SendEvOf (W64 11) id ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) c mm e) →
              TraceEv.Ok (elements c.incoming).length e := by
            intro e ⟨mm, hmm, he⟩
            simp only [List.mem_singleton] at hmm; subst hmm
            exact sendEvOf_ok _ id _ c _ e _ he (by decide) ht2 Hb.2 Hb.1 hn (Nat.le_refl _)
          iapply skipGate_appresp γd γ r id c _ _ tn.voters _ _ (ownStepGhost γ md c id s) rfl
            (by simp only [appResp]; exact hne) hOkR
          iframe Hgh Hc
        isplitr; · iintro %hg; exact (hnH hg).elim
        isplitr; · iintro %hg; exact (hnVR hg.1).elim
        isplitr; · iintro %hg; exact (hnVR hg.1).elim
        isplitr; · iintro %hg; exact hg.elim
        isplitr; · imodintro; iintro %hg; exact (hnVR hg.1).elim
        isplitr; · rw [htr]; iexact Hnosnap
        isplitr; · iintro %hg; exact (hnPVR hg.1).elim
        isplitr; · imodintro; iintro %hg; exact (hnPVR hg.1).elim
        iintro %hg
        rcases hg.1 with h | h
        · exact (hnVR h.1).elim
        · exact (hnPVR h.1).elim
      · iintro %h; exfalso; rw [hrole] at h; cases h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's step-down and stale or rejecting handling, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨pvs, ht, hint, hhi, hht, hse⟩ : ∃ (pvs : GMap w64 Progress) (ht hint : w64),
        uint.Z hint ≤ uint.Z m.Index' ∧ uint.Z ht ≤ uint.Z m.LogTerm' ∧
        s' = sendMsgs ({ becomeFollower s s.term m.From' with prvals := pvs } : NState)
          [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs } : NState)
            m.From' (!b) (if b then s.logst.committed else m.Index')
            (if b then W64 0 else ht) (if b then W64 0 else hint)] := by
      obtain ⟨pvs0, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs0] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.2.1 (.inl hrole)
      unfold CandidateStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [hTy] at hf
      simp [MsgVoteResp, MsgProp, MsgApp] at hf
      obtain ⟨-, pvs, hf⟩ := hf
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
        (toC (confAbs tn.voters) { rtfSrv a0 (idAbs m.From') with lead := idAbs m.From' })
        (P0 ++ [utAppResp b id m.From' (rtfSrv a0 (idAbs m.From'))]) C cs P →
        SimIdle C (sendMsgs ({ becomeFollower s s.term m.From' with prvals := pvs } : NState)
          [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs } : NState)
            m.From' (!b) (if b then s.logst.committed else m.Index')
            (if b then W64 0 else ht) (if b then W64 0 else hint)]) cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0', ← bfState_lead s m.From' pvs]
      have hRb := simServerR_bf (GF := GF) (hG := hG) _ _ s a0 m.From' pvs hR0 hrole
      cases b with
      | true =>
        exact staleEnd_simIdle tn.voters id (bfState s m.From' pvs) m (rtfSrv a0 (idAbs m.From')) hRb hs0 bt bc bl rfl
      | false =>
        exact rejEnd_simIdle tn.voters id (bfState s m.From' pvs) m (rtfSrv a0 (idAbs m.From')) hRb hs0 bt bc bl rfl
          ht hint
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
      have hout : OutTrStep s (sendMsgs ({ becomeFollower s s.term m.From' with prvals := pvs } : NState)
          [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs } : NState)
            m.From' (!b) (if b then s.logst.committed else m.Index')
            (if b then W64 0 else ht) (if b then W64 0 else hint)]) := by
        intro _ x hx
        simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · refine .inr (Msg.trOk_of_nums (by intro h; cases h) (by intro h; cases h) (fun _ => ?_))
          cases b with
          | true => exact appRespU_nums id _ m.From' s.logst.committed hT' Hb.2
          | false => exact appRespRejU_nums id _ m.From' m.Index' ht hint m.LogTerm' hT' hnb.2.2.2.1 hnb.2.2.1 hht hhi
      iframe Hgh
      isplitl [Hc]
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ hlast
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ hlast
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout

end paths

end EtcdGrove
end Perennial
