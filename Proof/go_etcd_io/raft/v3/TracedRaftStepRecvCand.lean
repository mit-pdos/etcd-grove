/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's `MsgHeartbeat` of its
term** (2026-11-10, trace-check Q8 stage 1 slice 20b, `notes/decisions.md`, "Q8 stage 1 (slice 20b)").

Raft's candidate steps down (`stepCandidate`'s `becomeFollower(m.Term, m.From)`, logging a
`BecomeFollower` line) and handles the heartbeat as a follower. The specification's receive line does
both in two rounds (`ReturnToFollowerState`, then the follower's heartbeat handling:
`lineEffect_candHbRecv`, from `lineEffect_recvU`), and skips the `BecomeFollower` line by
`bfCond`'s `ReturnToFollower` case, which reads the node's previous line: the receive line's event.
So the capability after the receive line keeps the receive event as the node's last event
(`recvGate_tracedL`, the family `bfR`), the `BecomeFollower` line is the skip (`phaseStepBF_rtf`;
its facts `FxPresBF` vacuous at a follower's share, `fxPresBF_vpin`), then the response's send line is
skipped as at a follower (`skipGate_hbresp`). The receive line's facts are the follower heartbeat's
(`simFx_hb`) at the intermediate state (`simFx_rtf`: the step-down keeps the facts).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvHb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

section bfst
variable [GoGlobalContext] [GoSemanticsFunctions]

/-- A candidate's step-down at its term (`stepCandidate`'s `becomeFollower(m.Term, m.From)`), with the
`Progress` map `pvs` `reset` leaves. -/
def bfState (s : NState) (j : w64) (pvs : GMap w64 Progress) : NState :=
  { becomeFollower s s.term j with prvals := pvs }

end bfst

/-- A candidate's server after `ReturnToFollowerState`, the append request's sender adopted as leader
(`handleAppendEntriesRequest`'s `lead' = j`; `rtfSt`). -/
def rtfSrv (a : Etcdraft.Server) (j : Etcdraft.ID) : Etcdraft.Server :=
  { a with state := Etcdraft.follower, lead := j }

theorem rtfSt_eq (σ : Etcdraft.State) (i j : Etcdraft.ID) :
    rtfSt σ i j = withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id := by
  unfold rtfSt withLead withNode Etcdraft.State.upd rtfSrv
  simp only
  congr 1
  funext k; by_cases hk : k = i <;> simp [hk]

/-- `toC` of the step-down, from `toC` of the server. -/
theorem toC_rtfSrv (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (j : Etcdraft.ID) (h : toC S x = toC S y) :
    toC S (rtfSrv x j) = toC S (rtfSrv y j) := by
  simp only [toC, rtfSrv] at h ⊢
  injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, h3, h5, h6, h7, h8, h9, h10, h11, h12]

/-- `toC` of a heartbeat's receiver, from `toC` of the server. -/
theorem toC_hbSrv (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (j : Etcdraft.ID) (c : Int)
    (h : toC S x = toC S y) : toC S (hbSrv x j c) = toC S (hbSrv y j c) := by
  simp only [toC, hbSrv] at h ⊢
  injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12]

/-- A heartbeat's response reads the receiver's term only. -/
theorem hbResp_toC (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (i j : Etcdraft.ID) (h : toC S x = toC S y) :
    hbResp x i j = hbResp y i j := by
  have h1 : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  unfold hbResp; rw [h1]

/-- **A line's effect with a larger intermediate shape**: `LineEffect` reads its `Mid` only as a premise. -/
theorem lineEffect_mid_mono {C : List w64} {bf : Bool} {e : TraceEv} {i : Etcdraft.ID} {a a' : Etcdraft.Server}
    {rcv : Option Etcdraft.Msg} {fM fP : Etcdraft.Bag → Etcdraft.Bag} {Mid Mid' : Etcdraft.Server → Prop}
    (h : LineEffect C bf e i a a' rcv fM fP Mid) (hm : ∀ v, Mid v → Mid' v) :
    LineEffect C bf e i a a' rcv fM fP Mid' := by
  obtain ⟨ln, hp, hn, hall⟩ := h
  refine ⟨ln, hp, hn, ?_⟩
  intro t l pl σ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hmid hfin
  exact hall t l pl σ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (fun v hv => hmid v (hm v hv)) hfin

/-- **A heartbeat of the node's term at a candidate: its effect**: `ReturnToFollowerState` (the first
round, to `rtfSrv`), then the follower's heartbeat handling (`recvAt_heartbeat`). -/
theorem lineEffect_candHbRecv (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (hty : m.ty = .heartbeat)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .candidate) (hterm : m.term = s.term) (hents : m.entries = [])
    (hc1 : 1 ≤ uint.Z (toPState s).commit)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hmabs : TraceSim.msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a (hbSrv (rtfSrv a (idAbs m.src)) (idAbs m.src) mabs.commitIndex)
      (some mabs) (fun b => b.without mabs)
      (fun b => b.with (hbResp (rtfSrv a (idAbs m.src)) (idAbs m.dst) (idAbs m.src)))
      (· = rtfSrv a (idAbs m.src)) := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hmt : mabs.type = .appendEntriesRequest := by simp [TraceSim.msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsub : mabs.subtype = "heartbeat" := by simp [TraceSim.msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [TraceSim.msgAbs, hty] at hmabs; rw [← hmabs]
  have hmprev : mabs.prevLogIndex = 0 := by simp [TraceSim.msgAbs, hty] at hmabs; rw [← hmabs]
  have hments : mabs.entries = [] := by simp [TraceSim.msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [TraceSim.msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [TraceSim.msgAbs, hty] at hmabs; rw [← hmabs]
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_heartbeat C C.length e m.dst s.vote xs m tm hmsg hm hty hents (by rw [hterm]; exact bt) bmc
    simp only [hmabs, Option.get_some] at this; exact this
  have hC' : idAbs m.dst ∈ confAbs C := by rw [mem_confAbs]; exact hC
  have hst : a.state = Etcdraft.candidate := by
    rw [hR.2.1]; simp [toPState, hrole, proleRole]; rfl
  apply lineEffect_recvU C e (idAbs m.dst) a (rtfSrv a (idAbs m.src)) _ mabs _ _ _
    (aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inr hty)) rfl
    (by simp only [msgLine, evConv]; rw [hname']; rfl) hpred hmdst
    (srvKey_ne_of_state _ _ (by simp only [rtfSrv]; rw [hst]; decide))
  · intro σ hsrv hσi _ _
    have hcontains : σ.server.contains (idAbs m.dst) = true := by
      rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
    refine ⟨?_, ?_⟩
    · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
      have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs
        (by rw [hrole]; decide) hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
      unfold Etcdraft.Line.stateMatches at hsm ⊢
      simpa [msgLine, nodeLine] using hsm
    · have := (firstRound_rtf σ mabs (idAbs m.dst) hmdst hcontains hmt
        (by rw [hσi, hR.1, hmterm, hterm]; rfl) (by rw [hσi]; exact hst)).1
      rw [this, rtfSt_eq, hσi, hmsrc]
  · rw [← hmsrc]
    exact recvAt_heartbeat C (idAbs m.dst) (rtfSrv a mabs.source) mabs hmdst hC' hmt rfl
      (by simp only [rtfSrv]; rw [hR.1, hmterm, hterm]; rfl) hmsub hmprev hments
      (by simp only [rtfSrv]; rw [hR.2.2.2.2.2.2.1]; exact hc1)

/-- **`ReturnToFollowerState` keeps the specification invariant**, the leader adopted (`rtfSt`). -/
theorem specInv_rtf {σ : Etcdraft.State} {i j : Etcdraft.ID} (h : TraceSpecInv.SpecInv σ) (hi : i ∈ σ.server) :
    TraceSpecInv.SpecInv (withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id) := by
  have := TraceSpecInv.specInv_upd_follower (f := fun v => rtfSrv v j) h rfl (Int.le_refl _) rfl rfl rfl
    (fun l hl _ hll ht => h.commitInDurable i hi l hl hll ht.symm)
  rwa [upd_eq_withNode] at this

/-- The specification's heartbeat at a candidate of its term, as `bfCond` reads the receive line
(`ReturnToFollower`'s case): the receive event of an append request or a heartbeat at the node's term,
at a candidate, and a `BecomeFollower` event at that term. -/
theorem bfCond_rtf (evt : w64) (id : w64) (s s1 : NState) (c : CfgM) (m : Msg) (e0 e : TraceEv)
    (hevt : evt = W64 10) (h0 : SendEvOf evt id s c m e0) (h1 : NodeEvOf (W64 2) id s1 c e)
    (hrole : s.role = .candidate) (hterm : m.term = s.term) (hterm1 : s1.term = s.term) :
    bfCond (evConv e0) (evConv e) = true := by
  subst hevt
  obtain ⟨hname0, -, ht0, -, -, hr0, -, -, ⟨tm, hmsg, hm⟩, -⟩ := h0
  obtain ⟨-, -, ht1, -⟩ := h1
  have hn0 : e0.name = go!"ReceiveAppendEntriesRequest" := by
    simp only [evtNames] at hname0; have := hname0; simp at this; exact this.symm
  unfold bfCond evConv
  simp only [hmsg, Option.map_some]
  rw [hn0, ht0, hr0, ht1, hterm1, hm.2.1, hterm, hrole]
  simp [Etcdraft.isReceiveName, gsStr, roleStr, Etcdraft.candidate]
  decide

end pure

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- A non-leader's facts read its server's log, commit index and term only. -/
theorem srvFacts_congr_nl (γ : RaftNames) (C : List w64) (j : w64) (v w : Etcdraft.Server)
    (hl : w.log = v.log) (hc : w.commitIndex = v.commitIndex) (ht : w.currentTerm = v.currentTerm)
    (hv : v.state ≠ Etcdraft.leader) (hw : w.state ≠ Etcdraft.leader) :
    srvFacts (GF := GF) γ C j v ⊢ srvFacts γ C j w := by
  unfold srvFacts
  simp only [hl, hc, ht, hv, hw, ↓reduceIte, ne_eq, not_false_eq_true, forall_const]
  exact .rfl

end ghost

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`ReturnToFollowerState` keeps the facts** (a candidate's step-down at its term, the leader
adopted: no log, commit, term or message changes, and neither role leads). -/
theorem simFx_rtf (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i j : Etcdraft.ID)
    (hi : i ∈ σ.server) (hc : (σ.s i).state = Etcdraft.candidate) :
    simFx (GF := GF) γ C σ ⊢ simFx γ C (withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id) := by
  have hWs : ∀ k, (withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id).s k =
      if k = i then rtfSrv (σ.s i) j else σ.s k := fun k => rfl
  have hcl : Etcdraft.candidate ≠ Etcdraft.leader := by decide
  have hfl : Etcdraft.follower ≠ Etcdraft.leader := by decide
  have hF : ∀ k, ((withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id).s k).log = (σ.s k).log ∧
      ((withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id).s k).commitIndex = (σ.s k).commitIndex ∧
      ((withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id).s k).currentTerm = (σ.s k).currentTerm ∧
      ((withNode σ i (rtfSrv (σ.s i) j) _root_.id _root_.id).s k).config = (σ.s k).config := by
    intro k; rw [hWs]; split
    · rename_i hk; subst hk; simp [rtfSrv]
    · simp
  iintro Hfx
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hq, hu, hsh, has⟩ := Hp
  iunfold simFx
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %k %hk
    ihave #Hk := Hal $$ %k %hk
    rw [hWs]
    by_cases hki : idAbs k = i
    · simp only [hki, ↓reduceIte]
      iapply srvFacts_congr_nl γ C k (σ.s (idAbs k)) _ (by rw [hki]; rfl) (by rw [hki]; rfl) (by rw [hki]; rfl)
        (by rw [hki, hc]; exact hcl) (by simp [rtfSrv]; exact hfl)
      rw [hki]
      iexact Hk
    · simp only [hki, ↓reduceIte]
      iexact Hk
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf; ipureintro; exact hx
  ipureintro
  refine ⟨specInv_rtf hsi hi, quorumLogF_congr σ _ rfl (fun k => (hF k).1) (fun k => (hF k).2.1)
    (fun k => (hF k).2.2.2) hq, hu, hsh, ?_⟩
  intro m hm hty k hk hlk htk hs k' e he
  rw [hWs] at hlk htk ⊢
  split at hlk
  · simp [rtfSrv] at hlk; exact absurd hlk hfl
  · rename_i hki
    simp only [hki, ↓reduceIte] at htk ⊢
    exact has m hm hty k hk hlk htk hs k' e he

end fx

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A heartbeat's receive line's phase step, at a candidate of its term**: the server to the
step-down's (`rtfSrv`, the intermediate shape, up to `toC`) then to `hbSrv` of it, its response added. -/
theorem phaseStepR_candHb (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .heartbeat m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .candidate) (hents : ents = [])
    (hc1 : 1 ≤ uint.Z (toPState s).commit)
    (hb : (absMsg .heartbeat m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .heartbeat m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .heartbeat m ents))
      (fun v => toC (confAbs C0) v = toC (confAbs C0) (rtfSrv a0 (idAbs m.From'))) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) (hbSrv (rtfSrv a0 (idAbs m.From')) (idAbs m.From') ma.commitIndex))
        (P0 ++ [hbResp (rtfSrv a0 (idAbs m.From')) (idAbs id) (idAbs m.From')])) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg .heartbeat m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .heartbeat m ents).dst s c (absMsg .heartbeat m ents) e := by
    rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .heartbeat m ents).dst ∈ C := by rw [hdst]; exact hC
  have hev10 : evt = W64 10 := by
    rcases hev with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  subst hev10
  obtain ⟨hmt, -⟩ := msgAbs_recvTy hev hma
  have hnl : ¬ ma.term < a.currentTerm := by
    rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z (toPState s).term; rw [hterm]; exact Int.lt_irrefl _
  have hph := recvPhantoms_nolow ma a hnl
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hsrc : (absMsg .heartbeat m ents).src = m.From' := rfl
  have hux := toC_rtfSrv _ _ _ (idAbs m.From') hcx
  refine ⟨hbSrv (rtfSrv a (idAbs m.From')) (idAbs m.From') ma.commitIndex,
    [hbResp (rtfSrv a (idAbs m.From')) (idAbs id) (idAbs m.From')],
    ⟨rfl, toC_hbSrv _ _ _ _ _ hux, by rw [hbResp_toC _ _ _ _ _ hux]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have := lineEffect_candHbRecv C e s c _ a ma rfl he' hin hout hC' hR hs hrole hterm hents hc1
    bt bc bl bmc hma
  rw [hsrc] at this
  exact lineEffect_mid_mono this (fun v hv => by rw [hv]; exact hux)

/-- **The facts of a heartbeat's receive line, at a candidate of its term** (`FxPresR` at
`recvPhantoms m`, none): at the intermediate state the step-down's (`simFx_rtf`), at the result the
follower heartbeat's (`simFx_hb`) from it. -/
theorem fxPresR_candHb (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (L : List EntryM)
    (u0 : Etcdraft.Server) (c0 T : Int) (hiC : id ∈ C0) (hdst : ma.dest = idAbs id)
    (hty : ma.type = .appendEntriesRequest)
    (hsub : ma.subtype = "heartbeat") (hprev : ma.prevLogIndex = 0) (hents : ma.entries = [])
    (hbL : BootTerms C0.length 1 L) (hwL : PlogWf base0 L)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      toC (confAbs C0) u0 = toC (confAbs C0) (rtfSrv a ma.source) ∧
      cs1 = toC (confAbs C0) (hbSrv (rtfSrv a ma.source) ma.source ma.commitIndex) ∧
      r1 = hbResp a (idAbs id) ma.source ∧ ma.term = a.currentTerm ∧ a.state = Etcdraft.candidate ∧
      1 ≤ a.commitIndex ∧ a.commitIndex = c0 ∧ a.currentTerm = T ∧ a.log = logAbs C0 C0.length 1 L) :
    logRecs (GF := GF) γ base0 L ∗
      (⌜¬ c0 < ma.commitIndex⌝ ∨
        (⌜c0 < ma.commitIndex ∧ ma.commitIndex ≤ L.length⌝ ∗ commitIn γ L (W64 ma.commitIndex) (W64 T) ∗
          isCommitted γ (L.take ma.commitIndex.toNat))) ⊢
      FxPresR (GF := GF) γ id ma E (fun v => toC (confAbs C0) v = toC (confAbs C0) u0) (recvPhantoms ma)
        (IdlePin s C0 cs0 P0) (VPin C0 cs1 (P0 ++ [r1])) := by
  iintro ⟨#HL, #Hcert⟩
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hu0, hc1, hr1, hle, hcand, hcm1, hc0, hT, hlog⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hle]; exact Int.lt_irrefl _)
  have hσd : σ.s ma.dest = a := by rw [hdst]; exact hσa
  have hiσ : idAbs id ∈ σ.server := by rw [hsrv, mem_confAbs]; exact hiC
  ihave #Hu := simFx_rtf γ C σ (idAbs id) ma.source hiσ (by rw [hσa]; exact hcand) $$ Hfx
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = withNode σ (idAbs id) (rtfSrv (σ.s (idAbs id)) ma.source) _root_.id _root_.id :=
    ⟨_, rfl⟩
  rw [← hσu]
  have hσud : σu.s ma.dest = rtfSrv a ma.source := by
    rw [hσu, hdst]; simp [withNode, hσa]
  ihave #H1 := simFx_hb γ C σu ma L id (by rw [hσu]; exact hsrv) hiC hdst (by rw [hσu]; exact hpv)
    (by rw [hσu]; exact hcq) (by rw [hσud]; rfl) hty (by rw [hσud]; exact hle) hsub hprev hents
    (by rw [hσud]; exact hcm1) (by rw [hσu]; exact hmem) (by rw [hσud]; exact hlog) hbL hwL $$ [$Hu $HL]
  · rw [hσud]; simp only [rtfSrv]
    rw [hc0, hT]
    iexact Hcert
  iframe Htbl
  isplitl
  · iapply simFx_congr γ C (hbRecvSt σu ma) _ (by rw [hbRecvSt_eq, hσu]; rfl) (by rw [hbRecvSt_eq, hσu]; rfl)
      (by rw [hbRecvSt_eq, hσud, hph, hr1, hdst, hσu]; rfl)
    · intro k
      rw [hbRecvSt_eq]
      show toC σu.server (if k = idAbs id then a' else σ.s k) =
        toC σu.server (if k = ma.dest then hbSrv (σu.s ma.dest) ma.source ma.commitIndex else σu.s k)
      rw [hσud, hdst]
      split
      · rw [hσu]; show toC σ.server a' = toC σ.server _; rw [hsrv, hcs', hc1]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    iexact H1
  · iintro %v %hv
    iapply simFx_congr γ C σu _ (by rw [hσu]; rfl) (by rw [hσu]; rfl) (by rw [hσu]; rfl)
    · intro k
      show toC σu.server (if k = idAbs id then v else σ.s k) = toC σu.server (σu.s k)
      split
      · rename_i hk; subst hk
        rw [hσu]; show toC σ.server v = toC σ.server _; rw [hsrv, hv, hu0]; simp [withNode, hσa]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    iexact Hu

/-- **A step-down's facts at a follower's share**: vacuous (`FxPresBF` asks them of a leader or a
candidate only). -/
theorem fxPresBF_vpin (γ : RaftNames) (id : w64) (C0 : List w64) (cs1 : ServerC) (P1 : List Etcdraft.Msg)
    (hst : cs1.state = Etcdraft.follower) : ⊢ FxPresBF (GF := GF) γ id (VPin C0 cs1 P1) := by
  iunfold FxPresBF
  imodintro
  iintro %C %P %σ %h
  exfalso
  obtain ⟨⟨-, hcs, -⟩, -, -, -, -, hl⟩ := h
  have : (σ.s (idAbs id)).state = Etcdraft.follower := by
    have := congrArg ServerC.state hcs; rw [hst] at this; exact this
  rcases hl with hl | hl <;> rw [this] at hl <;> exact absurd hl (by decide)

/-- The node's last event: the receive line's (a family's `Λ` after it). -/
abbrev RecvLast (evt id : w64) (s : NState) (c : CfgM) (mm : Msg) : Option TraceEv → Prop :=
  fun o => ∃ e0, o = some e0 ∧ SendEvOf evt id s c mm e0

/-- **A `BecomeFollower` line after a candidate's receive line of an append request or a heartbeat
of its term**: the skip (`bfCond`'s `ReturnToFollower` case, `bfCond_rtf`), the share unchanged. -/
theorem phaseStepBF_rtf (id : w64) (c : CfgM) (s s1 : NState) (mm : Msg) (C0 : List w64) (cs1 : ServerC)
    (P1 : List Etcdraft.Msg) (hrole : s.role = .candidate) (hterm : mm.term = s.term) (hterm1 : s1.term = s.term) :
    PhaseStepBF id c s1 (VPin C0 cs1 P1) (VPin C0 cs1 P1) (RecvLast (W64 10) id s c mm) := by
  intro C cs P o hΦ hΛ _ e e0 he ho
  obtain ⟨e0', rfl, he0⟩ := hΛ
  obtain rfl : e0' = e0 := Option.some.inj ho
  refine ⟨fun _ => hΦ, fun hf => ?_⟩
  have := bfCond_rtf (W64 10) id s s1 c mm e0' e rfl he0 he hrole hterm hterm1
  rw [hf] at this; cases this

/-- **The receive hook's gate, traced, the receive event kept as the last event** (`recvGate_traced`
with `Λ' := RecvLast`): a `BecomeFollower` line after it reads it (`bfCond`). -/
theorem recvGate_tracedL (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s : NState)
    (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ty : MsgType) (evt : w64) (b : Bool) (k : Nat) (ma : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (ph : Etcdraft.Server → List Etcdraft.Msg) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ : Option TraceEv → Prop) (X : IProp GF)
    (htr : s.gh.tr = some γd) (hty : mtypeOf m.Type' = some ty) (hevt : recvEvt ty = some evt)
    (hps : PhaseStepR id c ma (SendEvOf evt id s c (absMsg ty m ents)) Mid ph Φ Φ')
    (hOk : ∀ e, SendEvOf evt id s c (absMsg ty m ents) e → TraceEv.Ok (elements c.incoming).length e) :
    (X ∗ trCapB (some γd) γ r id c b Φ Λ ∗
        FxPresR γ id ma (SendEvOf evt id s c (absMsg ty m ents)) Mid ph Φ Φ' ∗
        (∃ tn, traceDir γd tn ∗ inFlight tn k ma) : IProp GF) ⊢
      HookGateOpt s.gh.tr r (recvGate id s c ⟨m, ents, sn, ctx, rs⟩)
        iprop(X ∗ trCapB (some γd) γ r id c true Φ' (RecvLast evt id s c (absMsg ty m ents))) := by
  have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = some (SendEvOf evt id s c (absMsg ty m ents)) := by
    simp [recvGate, hty, hevt]
  rw [hrg, htr]
  iintro ⟨HX, Hcap, Hfx, Htok⟩
  iapply hookGateOpt_frame
  iframe HX
  icases trCapB_logger γd γ r id c b Φ Λ $$ Hcap with ⟨%tl, #Htl, Hcap⟩
  iapply trCapB_hookGateRecv (some γd) γ r id c tl _ b k ma Mid ph Φ Φ' Λ _ hps
    (fun e he => ⟨e, rfl, he⟩) (fun _ => hOk) (fun h => by cases h)
  simp only [FxPresRT, recvTok]
  iframe Htl Hcap Hfx Htok

/-- **A `BecomeFollower` line skipped after the receive line** (`trCapB_hookGate_bf` at the skip),
a frame `X`: from the capability at the pinned follower's share with the receive event last, to it
with the line's event last. -/
theorem bfGate_skip (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s1 : NState)
    (C0 : List w64) (cs1 : ServerC) (P1 : List Etcdraft.Msg) (Λr : Option TraceEv → Prop) (X : IProp GF)
    (hst : cs1.state = Etcdraft.follower) (hbf : PhaseStepBF id c s1 (VPin C0 cs1 P1) (VPin C0 cs1 P1) Λr)
    (hOk : ∀ e, NodeEvOf (W64 2) id s1 c e → TraceEv.Ok (elements c.incoming).length e) :
    (X ∗ trCapB (some γd) γ r id c true (VPin C0 cs1 P1) Λr : IProp GF) ⊢
      HookGate (some γd) r (NodeEvOf (W64 2) id s1 c)
        iprop(X ∗ trCapB (some γd) γ r id c true (VPin C0 cs1 P1) (fun o => o.isSome = true)) := by
  iintro ⟨HX, Hc⟩
  iapply hookGate_mono
  isplitl [HX]
  · iintro Hc; iframe HX Hc
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  iapply trCapB_hookGate_bf (some γd) γ r id c c tl s1 true (VPin C0 cs1 P1) (VPin C0 cs1 P1) Λr
    (fun o => o.isSome = true) (fun _ => rfl) (fun h => by cases h) (fun _ => hbf) (fun h => by cases h)
    (fun _ _ => rfl) (fun _ => ⟨fun _ => hOk, fun h => by cases h⟩) (fun h => by cases h)
  iframe Htl Hc
  simp only [trOwn, ↓reduceIte]
  iapply fxPresBF_vpin γ id C0 cs1 P1 hst

/-- The tracker's step-down at a candidate's term, related to the specification's (`rtfSrv`). -/
theorem simServerR_bf (C : List w64) (bl : Nat) (s : NState) (a : Etcdraft.Server) (j : w64)
    (pvs : GMap w64 Progress) (hR : SimServerR C bl (toPState s) a) (hrole : s.role = .candidate) :
    SimServerR C bl (toPState (bfState s j pvs)) (rtfSrv a (idAbs j)) := by
  unfold bfState
  obtain ⟨hT, -, hV, -, hB, hLog, hCm, hCfg, hPc, -, -⟩ := hR
  refine ⟨hT, ?_, ?_, ?_, hB, hLog, hCm, hCfg, hPc, ?_, ?_⟩
  · simp [rtfSrv, toPState, becomeFollower, proleRole, roleAbs]
  · simp only [rtfSrv]; rw [hV]
    simp [toPState, becomeFollower, resetTo, resetTo0]
  · simp [rtfSrv, toPState, becomeFollower]
  · intro h; simp [toPState, becomeFollower, proleRole] at h
  · intro h; simp [toPState, becomeFollower, proleRole] at h

end steps

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The resources of a receive path with a skipped `BecomeFollower` line**: after the receive line
(`G0`) raft's ghost state and the capability at the pinned share with the receive event last (`Λr`);
after the preamble (`G1`) the same with `Λ1` (`Λr` when the preamble logs nothing); after the step-down
(`Gf`) and the response's skipped send line (`GE`) with an event last; `False` at the others. -/
def bfR (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (γd : GName)
    (tn : TraceNames) (cs0 cs1 : ServerC) (P0 P1 : List Etcdraft.Msg) (Λ Λr Λ1 : Option TraceEv → Prop)
    (k : Nat) (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c true (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(ownStepGhost γ md c id s ∗ trCapB (some γd) γ r id c true (VPin tn.voters cs1 P1) Λr)
  G1 := fun _ => iprop(ownStepGhost γ md c id s ∗ trCapB (some γd) γ r id c true (VPin tn.voters cs1 P1) Λ1)
  GE := fun _ => iprop(ownStepGhost γ md c id s ∗
    (trCapB (some γd) γ r id c true (VPin tn.voters cs1 P1) (fun o => o.isSome = true) ∗ emp))
  Gf := iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (VPin tn.voters cs1 P1) (fun o => o.isSome = true))
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **A heartbeat of the node's term at a candidate.** -/
def CandHb (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgHeartbeat ∧ m.Term' = s.term ∧ s.role = .candidate

/-- **`raft.Step`'s traced bundle on a heartbeat of the node's term at a candidate**: the receive line
(the specification's two rounds, `ReturnToFollowerState` then the heartbeat handling, the commit raised
with the certificates the heartbeat's raft facts give, `ownRaftGhost_hbFacts`), raft's `BecomeFollower`
line (skipped: `bfCond` reads the receive line), then the response's send line, which the specification
skips; the end state is `heartbeatResult`'s at the step-down (`hbEnd_simIdle` with `simServerR_bf`). -/
theorem stepBundle_traced_candHb : stepBundle_traced.on (GF := GF) (hG := hG) CandHb := by
  intro γ md c r id s m ents sn ctx rs γd Λ hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole⟩ := hp
  have hmty : mtypeOf m.Type' = some .heartbeat := by rw [hTy]; rfl
  have htrd : MsgType.traced .heartbeat = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .heartbeat m ents hmty htrd hsh
  have hev10 : evt = W64 10 := by
    rcases hev with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  have hto' : m.To' = id := hto .heartbeat hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2 (.inr (.inr hTy)) (by rw [hto', h])
  have hents : ents = [] := hsh.1 hTy
  have hb0 : γ.reBoot ≠ [] := hboot (.inl hTy)
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  obtain ⟨hnA, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := hb_ne hTy
  have hmt2 : mtypeOf m.Type' = some .heartbeat ∧ MsgType.traced .heartbeat = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.heartbeat %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  ihave #Hmc := Hmsg $$ %MsgType.heartbeat %hmt2
  ihave #Hm := isMessageC_isMessage γ _ $$ Hmc
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c true _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hidC⟩ := hI0
  -- the specification's heartbeat
  have hfa : ma.dest = idAbs id ∧ ma.source = idAbs m.From' ∧ ma.type = .appendEntriesRequest ∧
      ma.subtype = "heartbeat" ∧ ma.prevLogIndex = 0 ∧ ma.entries = [] ∧ ma.commitIndex = uint.Z m.Commit' ∧
      ma.term = uint.Z m.Term' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]
    simp [hto']
  obtain ⟨hmd, hms, hmty', hmsub, hmprev, hments, hmcm, hmterm⟩ := hfa
  have hlogA : a0.log = logAbs tn.voters tn.voters.length 1 (toPState s).log := hR0.2.2.2.2.2.1
  have hwB : PlogWf base0 (toPState s).log := by have h := hs0.2.1; rw [hs0.1] at h; exact h
  have hbL : BootTerms tn.voters.length 1 (toPState s).log := fun k e hk he => hs0.2.2 k e (by omega) he
  have hcs1 : (toC (confAbs tn.voters) (hbSrv (rtfSrv a0 (idAbs m.From')) (idAbs m.From') ma.commitIndex)).state =
      Etcdraft.follower := rfl
  imodintro
  iexists bfR γ md c r id s γd tn cs0
    (toC (confAbs tn.voters) (hbSrv (rtfSrv a0 (idAbs m.From')) (idAbs m.From') ma.commitIndex)) P0
    (P0 ++ [hbResp (rtfSrv a0 (idAbs m.From')) (idAbs id) (idAbs m.From')]) Λ
    (RecvLast evt id s c (absMsg .heartbeat m ents)) (RecvLast evt id s c (absMsg .heartbeat m ents)) k ma
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
      imod ownRaftGhost_hbFacts γ id (toPState s) (absMsg .heartbeat m ents ctx) rfl hto'
        (by show m.Term' = s.term; exact hterm) (by show proleRole s.role ≠ .leader; rw [hrole]; nofun)
        hs0.1 hwB $$ Hm Hg with ⟨Hg, %Hbc, #HL, #Hcert⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .heartbeat m ents).NumsBelow traceNumBound := (hok .heartbeat hmty hreT htrd).1
      have hc1 : 1 ≤ uint.Z (toPState s).commit := by
        have : (1 : Int) ≤ γ.reBoot.length := by
          have := List.length_pos_iff.mpr hb0; omega
        omega
      have hps := phaseStepR_candHb id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole hents hc1
        hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .heartbeat m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs .heartbeat evt true k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · iapply fxPresR_candHb γ id ma _ s tn.voters cs0 _ P0 _ (toPState s).log (rtfSrv a0 (idAbs m.From'))
          (uint.Z s.logst.committed) (uint.Z s.term) hidC hmd hmty' hmsub hmprev hments hbL hwB
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hux := toC_rtfSrv _ _ _ (idAbs m.From') hcx
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hRa.2.2.2.2.2.2.1, hRa.1, hRa.2.2.2.2.2.1⟩
          · rw [hms]; exact hux
          · rw [hms]; exact toC_hbSrv _ _ _ _ _ hux
          · rw [hms]; show hbResp a0 (idAbs id) (idAbs m.From') = _; exact hbResp_toC _ _ _ _ _ hcx
          · rw [hmterm, hRa.1, hterm]; rfl
          · rw [hRa.2.1]; simp [toPState, hrole, proleRole, roleAbs]
          · rw [hRa.2.2.2.2.2.2.1]; exact hc1
        · have hW1 : W64 (uint.Z m.Commit') = m.Commit' := by word
          have hW2 : W64 (uint.Z s.term) = s.term := by word
          rw [hmcm, hW1, hW2, show (absMsg .heartbeat m ents ctx).commit = m.Commit' from rfl,
            show (toPState s).term = s.term from rfl]
          iframe HL
          icases Hcert with (%H0 | ⟨%H1, #H2, #H3⟩)
          · ileft; ipureintro; exact H0
          · iright
            isplitr; · ipureintro; exact H1
            isplitr
            · iexact H2
            · iexact H3
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
            (phaseStepBF_rtf id c s _ (absMsg .heartbeat m ents) tn.voters _ _ hrole hterm rfl)
            (fun e he => nodeEvOf_ok _ id _ c e _ he (by decide) ht1 hc1' hl1 (Nat.le_refl _))
          iframe Hgh Hc
        isplitr
        · iintro %hg; exact (hnA hg).elim
        isplitr
        · -- the response's send line, skipped by the specification
          iintro %_ %pvs' ⟨Hgh, Hc⟩
          rw [htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
          imodintro
          have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
          have hnb : (absMsg .heartbeat m ents).NumsBelow traceNumBound := (hok .heartbeat hmty hreT htrd).1
          have hn := hbresp_nums id s m ctx hT
          have hcm : uint.nat (plogCommitTo s.logst.committed m.Commit') < traceNumBound := by
            unfold plogCommitTo; split
            · exact hnb.2.2.2.2.1
            · exact Hb.2
          have ht2 : uint.nat s.term < traceNumBound := by word
          have hOkR : ∀ e, (∃ mm ∈ [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := ctx }],
              SendEvOf (W64 11) id { ({ becomeFollower s s.term m.From' with prvals := pvs' } : NState) with
                logst := { s.logst with committed := plogCommitTo s.logst.committed m.Commit' } } c mm e) →
              TraceEv.Ok (elements c.incoming).length e := by
            intro e ⟨mm, hmm, he⟩
            simp only [List.mem_singleton] at hmm; subst hmm
            exact sendEvOf_ok _ id _ c _ e _ he (by decide) ht2 hcm Hb.1 hn (Nat.le_refl _)
          iapply skipGate_hbresp γd γ r id c _ { Msg.plain .heartbeatResp id m.From' s.term false with ctx := ctx }
            tn.voters _ _ (ownStepGhost γ md c id s) rfl (by simp only [Msg.plain]; exact hne) hOkR
          iframe Hgh Hc
        isplitr; · iintro %hg; exact (hnVR hg.1).elim
        isplitr; · iintro %hg; exact hg.elim
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
  · -- the closing wand: raft's step-down and heartbeat handling, the specification's
    iunfold stepClose
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨pvs, hse⟩ : ∃ pvs : GMap w64 Progress,
        s' = heartbeatResult id (bfState s m.From' pvs) m ctx := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.2.1 (.inl hrole)
      unfold CandidateStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [hTy] at hf
      simp [MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat] at hf
      exact hf.2
    subst hse
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) (hbSrv (rtfSrv a0 (idAbs m.From')) (idAbs m.From') ma.commitIndex))
        (P0 ++ [hbResp (rtfSrv a0 (idAbs m.From')) (idAbs id) (idAbs m.From')]) C cs P →
        SimIdle C (heartbeatResult id (bfState s m.From' pvs) m ctx) cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hnb := (hok .heartbeat hmty hre htrd).1
      have hmc63 : uint.Z m.Commit' < 2 ^ 63 := (numsBelow_63 hnb).2.2.2.2
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0']
      exact hbEnd_simIdle tn.voters id (bfState s m.From' pvs) m ents ctx
        (rtfSrv a0 (idAbs m.From')) ma (simServerR_bf _ _ s a0 m.From' pvs hR0 hrole) hs0 bt bc bl rfl hmc63 hma
    have hout : OutTrStep s (heartbeatResult id (bfState s m.From' pvs) m ctx) := by
      intro _ x hx
      simp only [heartbeatResult, sendMsgs, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact .inl hx
      · exact .inr (Msg.trOk_of_nums_hbresp rfl rfl (fun _ => hbresp_nums id s m ctx hT))
    unfold stepOut
    dsimp only [bfR]
    have hlast : ∀ o, RecvLast evt id s c (absMsg .heartbeat m ents) o → stepLastEv Λ o := by
      rintro o ⟨e0, rfl, -⟩; exact .inr rfl
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
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ hlast
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact hout

end paths

end EtcdGrove
end Perennial
