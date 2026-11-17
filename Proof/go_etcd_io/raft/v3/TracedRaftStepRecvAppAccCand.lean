/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's accepted `MsgApp` of its
term** (2026-11-11, trace-check Q8 stage 1 slice 24c, `notes/decisions.md`, "Q8 stage 1 (slice 24c)").

As a candidate's stale or rejected `MsgApp` (`stepBundle_traced_candAppSR`), with the follower's accepted
handling (`stepBundle_traced_folAppAcc`) after the step-down: the receive line's two rounds
(`ReturnToFollowerState`, then the accepted handling at `rtfSrv`: `lineEffect_appRecvU`), raft's
`BecomeFollower` line skipped (`bfCond`), the response's send line skipped. The line's facts: the
step-down's (`simFx_rtf`), then `simFx_appAccMid`/`simFx_appAccEnd` at the step-down's state. Proved for
the capability whose voters fit the bootstrap log (`stepBundle_traced.onRB`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvAppAccFol
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvCandApp

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

/-- **An accepted append request's receive line's phase step at a candidate of its term**:
`ReturnToFollowerState` (to `rtfSrv`), then the accepted handling (`lineEffect_appRecvU`), the server to
`doneSrv` at `rtfSrv`, the response `doneResp` added; the intermediate servers the step-down's or
`AccMid` at it. -/
theorem phaseStepR_candAppAcc (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .app m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .candidate)
    (hmty : ma.type = .appendEntriesRequest) (hms : ma.source = idAbs m.From')
    (hcom : uint.Z (toPState s).commit ≤ uint.Z m.Index')
    (lastnewi : w64) (es' : List EntryM)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))) ents = some (lastnewi, es'))
    (hbe : BootTerms C0.length (uint.nat m.Index' + 1) ents)
    (hwf : ∀ (k : Nat) (x : EntryM), ents[k]? = some x → uint.Z x.Index' = (uint.nat m.Index' : Int) + k + 1)
    (hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0)
    (hnw : (uint.nat m.Index' : Int) + ents.length + 1 < 2 ^ 64)
    (hb : (absMsg .app m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .app m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .app m ents))
      (fun v => toC (confAbs C0) v = toC (confAbs C0) (rtfSrv a0 (idAbs m.From')) ∨
        AccMid C0 (rtfSrv a0 (idAbs m.From')) (idAbs m.From') (toPState s).log ents es' (uint.nat m.Index') v)
      (recvPhantoms ma) (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) (doneSrv (rtfSrv a0 (idAbs m.From')) (logAbs C0 C0.length 1 es') (idAbs m.From')
          (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length))))
        (P0 ++ [doneResp (rtfSrv a0 (idAbs m.From')) ma (uint.nat m.Index') ents.length])) := by
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
  have hev10 : evt = W64 10 := by
    rcases hev with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  subst hev10
  obtain ⟨hmt, hmd, -, -, -, -, -⟩ := msgAbs_recvTy hev hma
  have hph : recvPhantoms ma a = [] :=
    recvPhantoms_nolow ma a (by
      rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z s.term; rw [hterm]; exact Int.lt_irrefl _)
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hux := toC_rtfSrv _ _ _ (idAbs m.From') hcx
  have hsrc : (absMsg .app m ents).src = m.From' := rfl
  have hst : a.state = Etcdraft.candidate := by
    rw [hR.2.1]; simp [toPState, hrole, proleRole]; rfl
  refine ⟨doneSrv (rtfSrv a (idAbs m.From')) (logAbs C C.length 1 es') (idAbs m.From')
      (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length)),
    [doneResp (rtfSrv a (idAbs m.From')) ma (uint.nat m.Index') ents.length],
    ⟨rfl, toC_doneSrv _ _ _ _ _ _ hux, by rw [doneResp_toC _ _ _ _ _ _ hux]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx
    simp only [doneResp]
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]; simp [hto]
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have hFR : ∀ σ : Etcdraft.State, σ.server = confAbs C → σ.s (idAbs (absMsg .app m ents).dst) = a →
      σ.preVote = false → σ.checkQuorum = false →
      FirstRound σ (withNode σ (idAbs (absMsg .app m ents).dst) (rtfSrv a (idAbs m.From')) _root_.id _root_.id)
        ma (idAbs (absMsg .app m ents).dst) := by
    intro σ hsrv hσi _ _
    have hcontains : σ.server.contains (idAbs (absMsg .app m ents).dst) = true := by
      rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC'
    have := firstRound_rtf σ ma (idAbs (absMsg .app m ents).dst) hmd hcontains hmty
      (by rw [hσi, hR.1, hmt]; show uint.Z m.Term' = uint.Z s.term; rw [hterm]) (by rw [hσi]; exact hst)
    rw [rtfSt_eq, hσi, hms] at this
    exact this
  have := lineEffect_appRecvU C e s c (absMsg .app m ents) a (rtfSrv a (idAbs m.From')) ma rfl he' hin hout hC'
    hR hs (by rw [hrole]; decide) hcom lastnewi es' happ hbe hwf hlt0 bt bc bl bi blt bk bmc bmt hnw hma hFR
  rw [hsrc] at this
  refine lineEffect_mid_mono this ?_
  rintro v (rfl | hv)
  · exact .inl hux
  · exact .inr (appMid_accMid C _ _ _ _ _ _ _ hux v hv)

/-- **The facts of an accepted append request's receive line at a candidate of its term**: at the
step-down's state `simFx_rtf`, then the follower's facts there (`simFx_appAccMid` at every intermediate
state, drawn with the vote table, `simFx_appAccEnd` at the end), related to the line's servers by
`simFx_congr`. -/
theorem fxPresR_candAppAcc (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (u0 : Etcdraft.Server)
    (L ents es' : List EntryM) (p : Nat) (lt lastnewi : w64) (c0 T0 : Int)
    (hiC : id ∈ C0) (hdst : ma.dest = idAbs id) (hty : ma.type = .appendEntriesRequest) (hsub : ma.subtype = "app")
    (hbL : BootTerms C0.length 1 L) (hwr : PlogWfR base0 L) (hln : L.length < 2 ^ 63)
    (hcp : c0 ≤ p) (hc0 : 0 ≤ c0)
    (hprev : ma.prevLogIndex = p) (hents : ma.entries = logAbs C0 C0.length (p + 1) ents)
    (hbe : BootTerms C0.length (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) L (entryID.mk lt (W64 p)) ents = some (lastnewi, es'))
    (hwr' : PlogWfR base0 es') (hln' : es'.length < 2 ^ 63)
    (src T : w64) (bL : entryID) (l fp ents0 : List EntryM) (idx lt0 : w64)
    (hTm : ma.term = uint.Z T) (hin : plogTermAt bL l idx = some lt0)
    (hsl : ents0 <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : ma.prevLogIndex = uint.Z idx) (hents0 : ma.entries = logAbs C0 C0.length (uint.nat idx + 1) ents0)
    (hE0 : ents0 = ents) (hidxp : uint.nat idx = p) (hlt0 : lt0 = lt)
    (cc : Int) (hcc : cc = max c0 (min ma.commitIndex ((p : Int) + ents.length))) (hccl : cc ≤ es'.length)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      cs1 = toC (confAbs C0) (doneSrv (rtfSrv a ma.source) (logAbs C0 C0.length 1 es') ma.source
        (min ma.commitIndex ((p : Int) + ents.length))) ∧
      r1 = doneResp (rtfSrv a ma.source) ma p ents.length ∧ ma.term = a.currentTerm ∧
      a.state = Etcdraft.candidate ∧ a.commitIndex = c0 ∧ a.currentTerm = T0 ∧
      a.log = logAbs C0 C0.length 1 L ∧ toC (confAbs C0) (rtfSrv a ma.source) = toC (confAbs C0) u0) :
    logRecs (GF := GF) γ base0 L ∗ logRecs γ base0 es' ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ∗
      commitIn γ es' (W64 cc) (W64 T0) ∗ isCommitted γ (es'.take cc.toNat) ⊢
      FxPresR (GF := GF) γ id ma E
        (fun v => toC (confAbs C0) v = toC (confAbs C0) u0 ∨ AccMid C0 u0 ma.source L ents es' p v)
        (recvPhantoms ma) (IdlePin s C0 cs0 P0) (VPin C0 cs1 (P0 ++ [r1])) := by
  iintro ⟨#HL, #HN, #Hp, #Hf, #Hci, #Hcm⟩
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hc1, hr1, hle, hcand, hcm1, hT, hlog, hu0⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hle]; exact Int.lt_irrefl _)
  have hσi : σ.s (idAbs id) = a := hσa
  have hiσ : idAbs id ∈ σ.server := by rw [hsrv, mem_confAbs]; exact hiC
  ihave #Hu := simFx_rtf γ C σ (idAbs id) ma.source hiσ (by rw [hσi]; exact hcand) $$ Hfx
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = withNode σ (idAbs id) (rtfSrv (σ.s (idAbs id)) ma.source) _root_.id _root_.id :=
    ⟨_, rfl⟩
  rw [← hσu]
  have hσui : σu.s (idAbs id) = rtfSrv a ma.source := by rw [hσu, hσi]; exact withNode_s_self _ _ _ _ _
  have hσuo : ∀ k, k ≠ idAbs id → σu.s k = σ.s k := by
    intro k hk; rw [hσu]; show (if k = idAbs id then _ else σ.s k) = σ.s k; exact ite_eq_right_of_eq_false _ _ (eq_false hk)
  have hsrvu : σu.server = confAbs C := by rw [hσu]; exact hsrv
  have hmemu : ma ∈ σu.messages.domain := by rw [hσu]; exact hmem
  have hfu : (σu.s (idAbs id)).state = Etcdraft.follower := by rw [hσui]; rfl
  have hleu : ma.term = (σu.s (idAbs id)).currentTerm := by rw [hσui]; exact hle
  have hlogu : (σu.s (idAbs id)).log = logAbs C C.length 1 L := by rw [hσui]; exact hlog
  have hcmu : (σu.s (idAbs id)).commitIndex = c0 := by rw [hσui]; exact hcm1
  -- every intermediate state's facts at the step-down's state, drawn with the vote table
  icases votesTbl_forall_list γ
      (fun _ => iprop(simFx γ C σu ∗ logRecs γ base0 L ∗ logRecs γ base0 es' ∗ leadPrefix γ src T bL l ∗
        lpfull γ src T bL l fp))
      (fun L' => iprop(∀ (_ : (∃ k, p ≤ k ∧ k < L.length ∧ ConflictBy ents L p k ∧ L' = L.take k) ∨ L' = es'),
        simFx γ C (withNode σu (idAbs id)
          { σu.s (idAbs id) with log := logAbs C C.length 1 L', lead := ma.source } _root_.id _root_.id)))
      (fun L' => by
        iintro ⟨Htbl, #Hfx, #HL, #HN, #Hp, #Hf⟩
        by_cases hL' : (∃ k, p ≤ k ∧ k < L.length ∧ ConflictBy ents L p k ∧ L' = L.take k) ∨ L' = es'
        · icases simFx_appAccMid γ C σu id ma L ents es' p lt lastnewi ma.source hsrvu hiC hdst
              hfu hleu hmemu hlogu hbL hwr hln (by rw [hcmu]; exact hcp) (by rw [hcmu]; exact hc0) hprev hents hbe
              hwf hp hnw happ hwr' hln' src T bL l fp ents0 idx lt0 hTm hin hsl hidx1 hidx hents0 hE0 hidxp L' hL'
              $$ [$Htbl $Hfx $HL $HN $Hp $Hf] with ⟨Htbl, #H⟩
          iframe Htbl
          iintro %_
          iexact H
        · iframe Htbl
          iintro %h
          exact (hL' h).elim)
      (accLogs L es') $$ [$Htbl] with ⟨Htbl, #Hmid⟩
  · imodintro
    iintro %_ %_
    iframe Hu HL HN Hp Hf
  -- the end state's facts
  icases simFx_appAccEnd γ C σu id ma L ents es' p lt lastnewi hsrvu hiC hdst hfu hty hleu hsub hmemu hlogu hbL
      hwr hln (by rw [hcmu]; exact hcp) (by rw [hcmu]; exact hc0) hprev hents hbe hwf hp hnw happ hwr' hln' src T bL
      l fp ents0 idx lt0 hTm hin hsl hidx1 hidx hents0 hE0 hidxp hlt0 cc (by rw [hcmu]; exact hcc) hccl
      $$ [$Htbl $Hu $HL $HN $Hp $Hf] with ⟨Htbl, #H1⟩
  · rw [hσui, show (rtfSrv a ma.source).currentTerm = T0 from hT]; iframe Hci Hcm
  iframe Htbl
  have hkey : ∀ (v : Etcdraft.Server) (k : Etcdraft.ID), toC σ.server v = toC σ.server (σu.s (idAbs id)) →
      toC σ.server (if k = idAbs id then v else σ.s k) = toC σ.server ((withNode σu (idAbs id) v _root_.id _root_.id).s k) := by
    intro v k _
    show toC σ.server (if k = idAbs id then v else σ.s k) = toC σ.server (if k = idAbs id then v else σu.s k)
    split
    · rfl
    · rename_i hk; rw [hσuo k hk]
  isplitl
  · iapply simFx_congr γ C (withNode σu (idAbs id) (doneSrv (σu.s (idAbs id)) (logAbs C C.length 1 es') ma.source
        (min ma.commitIndex ((p : Int) + ents.length))) (fun b => b.without ma)
        (fun b => b.with (doneResp (σu.s (idAbs id)) ma p ents.length)))
      (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
      (by rw [hσu]; rfl) (by rw [hσu]; rfl) (by rw [hph, hr1, hσui, hσu]; rfl)
    · intro k
      show toC σu.server (if k = idAbs id then a' else σ.s k) =
        toC σu.server (if k = idAbs id then doneSrv (σu.s (idAbs id)) (logAbs C C.length 1 es') ma.source
          (min ma.commitIndex ((p : Int) + ents.length)) else σu.s k)
      split
      · rw [hsrvu, hcs', hc1, hσui]
      · rename_i hk; rw [hσuo k hk]
    iexact H1
  · iintro %v %hv
    rcases hv with hv | ⟨L', hL', hvC⟩
    · iapply simFx_congr γ C σu (withNode σ (idAbs id) v _root_.id _root_.id) (by rw [hσu]; rfl) (by rw [hσu]; rfl)
        (by rw [hσu]; rfl)
      · intro k
        show toC σu.server (if k = idAbs id then v else σ.s k) = toC σu.server (σu.s k)
        split
        · rename_i hk; subst hk; rw [hsrvu, hv, hσui, hu0]
        · rename_i hk; rw [hσuo k hk]
      iexact Hu
    · ihave #Hv := Hmid $$ %L' %(mem_accLogs L ents es' p L' hL')
      ihave #Hv' := Hv $$ %hL'
      iapply simFx_congr γ C (withNode σu (idAbs id)
          { σu.s (idAbs id) with log := logAbs C C.length 1 L', lead := ma.source } _root_.id _root_.id)
        (withNode σ (idAbs id) v _root_.id _root_.id) (by rw [hσu]; rfl) (by rw [hσu]; rfl) (by rw [hσu]; rfl)
      · intro k
        show toC σu.server (if k = idAbs id then v else σ.s k) =
          toC σu.server (if k = idAbs id then { σu.s (idAbs id) with log := logAbs C C.length 1 L', lead := ma.source }
            else σu.s k)
        split
        · rw [hsrvu, hvC, hσui]; exact (toC_logLead _ _ _ _ _ hu0).symm
        · rename_i hk; rw [hσuo k hk]
      iexact Hv'

end fx

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An accepted append request of a candidate's term** (at or above the commit index, the log
matching its previous entry): `handleAppendEntries`'s accepting exit after the candidate's step-down. -/
def CandAppAcc (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgApp ∧ m.Term' = s.term ∧ s.role = .candidate ∧ uint.Z s.logst.committed ≤ uint.Z m.Index' ∧
  PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index')

/-- **`raft.Step`'s traced bundle on an accepted append request of a candidate's term**: the receive line
(`ReturnToFollowerState`, then the accepted handling), raft's `BecomeFollower` line (skipped: `bfCond`
reads the receive line), then the response's send line, which the specification skips. Proved for the
capability whose voters fit the bootstrap log (`stepBundle_traced.onRB`). -/
theorem stepBundle_traced_candAppAcc : stepBundle_traced.onRB (GF := GF) (hG := hG) CandAppAcc := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hge, hmt⟩ := hp
  have hmty : mtypeOf m.Type' = some .app := by rw [hTy]; rfl
  have htrd : MsgType.traced .app = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .app m ents hmty htrd hsh
  have hev10 : evt = W64 10 := by
    rcases hev with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  have hto' : m.To' = id := hto .app hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2.1 (.inr (.inl hTy)) (by rw [hto', h])
  obtain ⟨hnH, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := app_ne hTy
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hmt2 : mtypeOf m.Type' = some .app ∧ MsgType.traced .app = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.app %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  ihave #Hmc := Hmsg $$ %MsgType.app %hmt2
  ihave #Hm := isMessageC_isMessage γ _ $$ Hmc
  icases isMessage_app_inv γ (absMsg .app m ents ctx) rfl $$ Hm with
    ⟨%Hpay, -, ⟨%bL, %l, %fpL, #Hlp, %Hpl, #Hlf, -, -, -⟩, -⟩
  icases isMessage_app_index0 γ (absMsg .app m ents ctx) rfl $$ Hm with %Hi0
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hCB⟩, hidC⟩ := hI0
  ihave Hcap := trCapB_mono (some γd) γ r id c bfl _ (IdlePin s tn.voters cs0 P0) Λ
    (fun C cs P h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) $$ Hcap
  have hfa : ma.dest = idAbs id ∧ ma.source = idAbs m.From' ∧ ma.type = .appendEntriesRequest ∧
      ma.subtype = "app" ∧ ma.term = uint.Z m.Term' ∧ ma.prevLogIndex = ((uint.nat m.Index' : Nat) : Int) ∧
      ma.entries = logAbs tn.voters tn.voters.length (uint.nat m.Index' + 1) ents ∧
      ma.commitIndex = uint.Z m.Commit' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]
    simp [hto']
  obtain ⟨hmd, hms, hmty', hmsub, hmterm, hmprev, hments, hmcm⟩ := hfa
  have hbase : (toPState s).base = base0 := hs0.1
  have hmatch : PlogMatches base0 (toPState s).log (entryID.mk m.LogTerm' m.Index') := by
    rw [← hbase]; exact hmt
  obtain ⟨⟨lastnewi, es'⟩, happ⟩ := plogMaybeAppend_some_of ents hmatch
  have hWi : W64 (uint.nat m.Index') = m.Index' := by word
  have happ' : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))) ents = some (lastnewi, es') := by
    rw [hWi]; exact happ
  obtain ⟨hwfE, hnwE⟩ := Hpay
  have hpZ : ((uint.nat m.Index' : Nat) : Int) = uint.Z m.Index' := by word
  have hwfZ : ∀ (k : Nat) (x : EntryM), ents[k]? = some x →
      uint.Z x.Index' = (uint.nat m.Index' : Int) + k + 1 := by
    intro k x hx
    have h2 : uint.Z x.Index' = uint.Z m.Index' + ((k + 1 : Nat) : Int) := hwfE k x hx
    rw [h2, ← hpZ]; push_cast; omega
  have hnw : (uint.nat m.Index' : Int) + ents.length + 1 < 2 ^ 64 := by
    have h2 : uint.Z m.Index' + (ents.length : Int) + 1 < 2 ^ 64 := hnwE
    rw [hpZ]; exact h2
  have hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0 := fun h => Hi0 (by
    show uint.Z m.Index' = 0; have := h; word)
  have hwB : PlogWf base0 (toPState s).log := by have h := hs0.2.1; rw [hs0.1] at h; exact h
  have hbL : BootTerms tn.voters.length 1 (toPState s).log := fun k e hk he => hs0.2.2 k e (by omega) he
  have hcp : uint.Z s.logst.committed ≤ (uint.nat m.Index' : Int) := by rw [hpZ]; exact hge
  have hbN0 : ∀ (hreb : (γ.reBoot.length : Int) ≤ uint.Z s.logst.committed),
      BootTerms tn.voters.length (uint.nat m.Index' + 1) ents := by
    intro hreb k e hk _; omega
  have hT2 : uint.nat s.term < traceNumBound := by word
  have hT' : uint.Z s.term < traceNumBound := by omega
  have hcs1 : (toC (confAbs tn.voters) (doneSrv (rtfSrv a0 (idAbs m.From')) (logAbs tn.voters tn.voters.length 1 es')
      (idAbs m.From') (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length)))).state =
      Etcdraft.follower := rfl
  imodintro
  iexists bfR bfl γ md c r id s γd tn cs0
    (toC (confAbs tn.voters) (doneSrv (rtfSrv a0 (idAbs m.From')) (logAbs tn.voters tn.voters.length 1 es')
      (idAbs m.From') (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length)))) P0
    (P0 ++ [doneResp (rtfSrv a0 (idAbs m.From')) ma (uint.nat m.Index') ents.length]) Λ
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
      imod ownStepGhost_appAccFacts γ md c id s (absMsg .app m ents ctx) lastnewi es' rfl (Int.le_of_eq (congrArg (fun x => uint.Z x) hterm.symm)) hbase hge happ hfit
        $$ [$Hm $Hgh] with ⟨Hgh, ⟨#HL, #HN, #Hci, #Hcm⟩, %Hf⟩
      obtain ⟨hwr, hwr', hwN, hcl, hli, hreb, hBN⟩ := Hf
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hreT htrd).1
      have hbe := hbN0 hreb
      have hps := phaseStepR_candAppAcc id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole hmty' hms
        hge lastnewi es' happ' hbe hwfZ hlt0 hnw hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .app m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs .app evt bfl k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · have hli' : uint.Z lastnewi = (uint.nat m.Index' : Int) + ents.length := by rw [hpZ]; exact hli
        have hlast : uint.Z lastnewi ≤ es'.length := by
          obtain ⟨-, -, hq, -, -⟩ := newLog_pure tn.voters (toPState s).log ents es' (uint.nat m.Index') m.LogTerm'
            lastnewi 0 hbL hbe hwfZ (by word) hnw (Nat.zero_le _) happ'
          omega
        have hccZ : uint.Z (accCommit (toPState s).commit m.Commit' lastnewi) =
            max (uint.Z s.logst.committed) (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length)) := by
          rw [hmcm, ← hli']
          unfold accCommit plogCommitTo
          show _ = max (uint.Z (toPState s).commit) _
          repeat' split
          all_goals omega
        have hW1 : W64 (uint.Z (accCommit (toPState s).commit m.Commit' lastnewi)) =
            accCommit (toPState s).commit m.Commit' lastnewi := by word
        have hW2 : W64 (uint.Z s.term) = (absMsg .app m ents ctx).term := by
          show W64 (uint.Z s.term) = m.Term'; rw [hterm]; word
        have hBN' : (es'.length : Int) < 2 ^ 63 := by
          have : traceNumBound = 2 ^ 61 := rfl
          omega
        have hlnL : (toPState s).log.length < 2 ^ 63 := by
          have h1 := bl; have h2 := plogWf_len_lt _ hwB
          unfold plastIndex plogLastIndexZ at h1; rw [hbase, base0_index] at h1
          simp only [Int.zero_add] at h1
          have : uint.Z (W64 ((toPState s).log.length : Int)) = (toPState s).log.length := by word
          omega
        rw [← hms]
        iapply fxPresR_candAppAcc γ id ma _ s tn.voters cs0 _ P0 _ (rtfSrv a0 ma.source) (toPState s).log ents es'
          (uint.nat m.Index') m.LogTerm' lastnewi (uint.Z s.logst.committed) (uint.Z s.term) hidC hmd hmty' hmsub hbL
          hwr hlnL
          hcp (uint_Z_nonneg _) hmprev hments hbe hwfZ (by word) hnw happ' hwr' (by omega)
          (absMsg .app m ents ctx).src (absMsg .app m ents ctx).term bL l fpL ents m.Index' m.LogTerm' hmterm
          Hpl.1 Hpl.2
          (by have h2 : uint.Z m.Index' + (ents.length : Int) + 1 < 2 ^ 64 := hnwE; omega) (by rw [hmprev, hpZ]) hments rfl rfl rfl
          (uint.Z (accCommit (toPState s).commit m.Commit' lastnewi)) hccZ (by
            rw [hccZ]; have := hcl; omega)
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hux := toC_rtfSrv _ _ _ ma.source hcx
          refine ⟨toC_doneSrv _ _ _ _ _ _ hux, doneResp_toC _ _ _ _ _ _ hux,
            by rw [hmterm, hRa.1, hterm]; rfl, ?_, hRa.2.2.2.2.2.2.1, by rw [hRa.1]; rfl, hRa.2.2.2.2.2.1, hux.symm⟩
          rw [hRa.2.1]; simp [toPState, hrole, proleRole, roleAbs]
        · rw [hW1, hW2, show (absMsg .app m ents ctx).commit = m.Commit' from rfl]
          iframe HL HN Hlp Hlf Hci Hcm
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
          have hx : ∃ ls' : LogState,
              s1 = { ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) with logst := ls' } ∧
              mm = appResp id ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) m.From' false
                lastnewi (W64 0) (W64 0) ∧
              ls'.prev = s.logst.prev ∧ ls'.sents ++ ls'.uents = es' ∧
              ls'.committed = accCommit s.logst.committed m.Commit' lastnewi := by
            unfold HandleAppResult at hres
            try simp only at hres
            rcases hres with ⟨h, -⟩ | ⟨-, ln2, es2, ls', h2, hp', hes2, -, hc2, -, -, h⟩ | ⟨-, hnm, -⟩
            · exact absurd h (by show ¬ uint.Z m.Index' < uint.Z s.logst.committed; omega)
            · have h2' : plogMaybeAppend base0 (toPState s).log (entryID.mk m.LogTerm' m.Index') ents =
                  some (ln2, es2) := by rw [← hbase]; exact h2
              have h3 := h2'.symm.trans happ
              simp only [Option.some.injEq, Prod.mk.injEq] at h3
              obtain ⟨rfl, rfl⟩ := h3
              obtain ⟨h1, h4⟩ := sendMsgs_one_inj h
              exact ⟨ls', h1, h4, hp', hes2, by rw [hc2]; rfl⟩
            · exact absurd hmt hnm
          obtain ⟨ls', rfl, rfl, hprev', hes', hcm'⟩ := hx
          rw [htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_appAccFacts γ md c id s (absMsg .app m ents ctx) lastnewi es' rfl (Int.le_of_eq (congrArg (fun x => uint.Z x) hterm.symm)) hbase hge happ hfit
            $$ [$Hm $Hgh] with ⟨Hgh, -, %Hf⟩
          obtain ⟨hwr, hwr', hwN, hcl, hli, hreb, hBN⟩ := Hf
          imodintro
          have hli' : uint.Z lastnewi = (uint.nat m.Index' : Int) + ents.length := by rw [hpZ]; exact hli
          have hb61 : traceNumBound = 2 ^ 61 := rfl
          have hlast : uint.Z lastnewi ≤ es'.length := by
            obtain ⟨-, -, hq, -, -⟩ := newLog_pure tn.voters (toPState s).log ents es' (uint.nat m.Index') m.LogTerm'
              lastnewi 0 hbL (hbN0 hreb) hwfZ (by word) hnw (Nat.zero_le _) happ'
            omega
          have hacc : uint.Z (accCommit s.logst.committed m.Commit' lastnewi) ≤ es'.length := by
            unfold accCommit plogCommitTo
            repeat' split
            all_goals omega
          have hlnb : uint.nat lastnewi < traceNumBound := by
            have := uint_Z_nonneg lastnewi
            rw [hb61] at hBN ⊢; word
          have hn := appRespU_nums id ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) m.From'
            lastnewi hT' hlnb
          have hc1 : uint.nat ({ ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) with logst := ls' } :
              NState).logst.committed < traceNumBound := by
            show uint.nat ls'.committed < traceNumBound
            rw [hcm']; have := uint_Z_nonneg (accCommit s.logst.committed m.Commit' lastnewi)
            rw [hb61] at hBN ⊢; word
          have hl1 : uint.nat (plastIndex (toPState ({ ({ becomeFollower s s.term m.From' with prvals := pvs' } :
              NState) with logst := ls' } : NState))) < traceNumBound := by
            unfold plastIndex plogLastIndexZ
            show uint.nat (W64 (uint.Z ls'.prev.index' + ((ls'.sents ++ ls'.uents).length : Int))) < traceNumBound
            rw [hprev', hes', show s.logst.prev = base0 from hbase, base0_index]
            rw [hb61] at hBN ⊢
            have h0 : (0 : Int) + (es'.length : Int) < 2 ^ 61 := by omega
            word
          have hOkR : ∀ e, (∃ mm ∈ [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState)
                m.From' false lastnewi (W64 0) (W64 0)],
              SendEvOf (W64 11) id { ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) with
                logst := ls' } c mm e) →
              TraceEv.Ok (elements c.incoming).length e := by
            intro e ⟨mm, hmm, he⟩
            simp only [List.mem_singleton] at hmm; subst hmm
            exact sendEvOf_ok _ id _ c _ e _ he (by decide) hT2 hc1 hl1 hn (Nat.le_refl _)
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
  · -- the closing wand: raft's step-down and accepted handling, the specification's
    have hoty : ∀ s', (s.gh.tr.isSome → StepEnd c id m ents ctx s s') → OutTyStep s s' := by
      intro s' hend
      obtain ⟨pvs, ls', hse, hprev', hes', hcm'⟩ : ∃ (pvs : GMap w64 Progress) (ls' : LogState),
          s' = sendMsgs { ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) with logst := ls' }
            [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) m.From' false
              lastnewi (W64 0) (W64 0)] ∧
          ls'.prev = s.logst.prev ∧ ls'.sents ++ ls'.uents = es' ∧
          ls'.committed = accCommit s.logst.committed m.Commit' lastnewi := by
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
        rcases hf with ⟨h, -⟩ | ⟨-, ln2, es2, ls', h2, hp', hes2, -, hc2, -, -, h⟩ | ⟨-, hnm, -⟩
        · exact absurd h (by show ¬ uint.Z m.Index' < uint.Z s.logst.committed; omega)
        · have h2' : plogMaybeAppend base0 (toPState s).log (entryID.mk m.LogTerm' m.Index') ents =
              some (ln2, es2) := by rw [← hbase]; exact h2
          have h3 := h2'.symm.trans happ
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          exact ⟨pvs, ls', h, hp', hes2, by rw [hc2]; rfl⟩
        · exact absurd hmt hnm
      subst hse; outty_tac
    iapply stepClose_anyB_end hoty
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend %_ Hout
    obtain ⟨pvs, ls', hse, hprev', hes', hcm'⟩ : ∃ (pvs : GMap w64 Progress) (ls' : LogState),
        s' = sendMsgs { ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) with logst := ls' }
          [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) m.From' false
            lastnewi (W64 0) (W64 0)] ∧
        ls'.prev = s.logst.prev ∧ ls'.sents ++ ls'.uents = es' ∧
        ls'.committed = accCommit s.logst.committed m.Commit' lastnewi := by
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
      rcases hf with ⟨h, -⟩ | ⟨-, ln2, es2, ls', h2, hp', hes2, -, hc2, -, -, h⟩ | ⟨-, hnm, -⟩
      · exact absurd h (by show ¬ uint.Z m.Index' < uint.Z s.logst.committed; omega)
      · have h2' : plogMaybeAppend base0 (toPState s).log (entryID.mk m.LogTerm' m.Index') ents =
            some (ln2, es2) := by rw [← hbase]; exact h2
        have h3 := h2'.symm.trans happ
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨pvs, ls', h, hp', hes2, by rw [hc2]; rfl⟩
      · exact absurd hmt hnm
    subst hse
    have hlastE : ∀ o, RecvLast evt id s c (absMsg .app m ents) o → stepLastEv Λ o := by
      rintro o ⟨e0, rfl, -⟩; exact .inr rfl
    unfold stepOut
    dsimp only [bfR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | ⟨Hgh, Hc, -⟩ | %h | ⟨%b', %N, %h⟩)
    rotate_right 2
    · exact h.elim
    · exact h.elim
    all_goals
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_appAccFacts γ md c id s (absMsg .app m ents ctx) lastnewi es' rfl (Int.le_of_eq (congrArg (fun x => uint.Z x) hterm.symm)) hbase hge happ hfit
        $$ [$Hm $Hgh] with ⟨Hgh, -, %Hf⟩
      obtain ⟨hwr, hwr', hwN, hcl, hli, hreb, hBN⟩ := Hf
      have hre : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hb61 : traceNumBound = 2 ^ 61 := rfl
      obtain ⟨hbN, -, hq, -, -⟩ := newLog_pure tn.voters (toPState s).log ents es' (uint.nat m.Index') m.LogTerm'
        lastnewi 0 hbL (hbN0 hreb) hwfZ (by word) hnw (Nat.zero_le _) happ'
      have hli' : uint.Z lastnewi = (uint.nat m.Index' : Int) + ents.length := by rw [hpZ]; exact hli
      have hlast : uint.Z lastnewi ≤ es'.length := by omega
      have hmono : ∀ C cs P, VPin tn.voters
          (toC (confAbs tn.voters) (doneSrv (rtfSrv a0 (idAbs m.From')) (logAbs tn.voters tn.voters.length 1 es')
            (idAbs m.From') (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length))))
          (P0 ++ [doneResp (rtfSrv a0 (idAbs m.From')) ma (uint.nat m.Index') ents.length]) C cs P →
          SimIdle C (sendMsgs { ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) with logst := ls' }
            [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) m.From' false
              lastnewi (W64 0) (W64 0)]) cs P := by
        rintro C cs P ⟨rfl, rfl, rfl⟩
        have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
        rw [hP0']
        have hRb := simServerR_bf (GF := GF) (hG := hG) _ _ s a0 m.From' pvs hR0 hrole
        exact accEnd_simIdle tn.voters id (bfState s m.From' pvs) m (rtfSrv a0 (idAbs m.From')) ma ls' es' lastnewi
          (uint.nat m.Index') ents.length hRb hs0 bt rfl hprev' hes' hcm' hbN hwN hBN hli' hlast hcp hmcm hmsub hmd hms
      have hout : OutTrStep s (sendMsgs { ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) with
          logst := ls' } [appResp id ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) m.From' false
            lastnewi (W64 0) (W64 0)]) := by
        intro _ x hx
        simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · exact .inr (Msg.trOk_of_nums (by intro h; cases h) (by intro h; cases h)
            (fun _ => appRespU_nums id _ m.From' lastnewi hT' (by
              show uint.nat lastnewi < traceNumBound; have := uint_Z_nonneg lastnewi
              rw [hb61] at hBN ⊢; word)))
      iframe Hgh
      isplitl [Hc]
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ hlastE
      iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
    · ipureintro; exact hout
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ hlastE
      iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
    · ipureintro; exact hout
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
    · ipureintro; exact hout


/-- (Amendment A6, Q24) **`raft.Step`'s traced bundle on an accepted append request at a follower**, for
every capability (`stepBundle_traced_folAppAcc` with the capability's bootstrap fit, `trCapB_bootFit`). -/
theorem stepBundle_traced_folAppAcc_on : stepBundle_traced.on (GF := GF) (hG := hG) FolAppAcc :=
  stepBundle_traced.on_of_onRB (fun tr γ r id c b s Λ => trCapB_bootFit tr γ r id c b _ Λ)
    stepBundle_traced_folAppAcc

/-- (Amendment A6, Q24) **… and at a candidate** (`stepBundle_traced_candAppAcc`, `trCapB_bootFit`). -/
theorem stepBundle_traced_candAppAcc_on : stepBundle_traced.on (GF := GF) (hG := hG) CandAppAcc :=
  stepBundle_traced.on_of_onRB (fun tr γ r id c b s Λ => trCapB_bootFit tr γ r id c b _ Λ)
    stepBundle_traced_candAppAcc

end paths

end EtcdGrove
end Perennial
