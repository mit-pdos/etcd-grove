/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a heartbeat of a higher term**
(2026-11-10, trace-check Q8 stage 1 slice 20b, `notes/decisions.md`, "Q8 stage 1 (slice 20b)").

Raft steps down in `Step`'s preamble (`becomeFollower(m.Term, m.From)`, its `BecomeFollower` line skipped:
`phaseStepBF_ut`), then handles the heartbeat as a follower and answers (the answer's send line
skipped). The specification's receive line: `UpdateTerm`, then the follower's heartbeat handling
(`lineEffect_ut` with `recvAt_heartbeat`). A heartbeat of a higher term carries commit `0`
(`ownRaftGhost_hbHigher`: its commit is at most the receiver's acknowledgement at the heartbeat's term,
and the receiver acknowledges only at its own, lower, term), so the receiver's commit index does not
move and no certificate is needed (`simFx_hb`'s first case).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTResp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **A heartbeat of a higher term than its receiver's carries commit `0`** (`heartbeat_commit_le_last`'s
argument: the heartbeat's commit is at most the receiver's acknowledgement at its term, which is the
trivial one, the receiver acknowledging only at its own term, `AcksTerm`). -/
theorem ownRaftGhost_hbHigher (E : CoPset) (γ : RaftNames) (id : w64) (ps : PState) (m : Msg) {md : Bool} :
    ↑(slotN γ id) ⊆ E → m.ty = .heartbeat → m.dst = id → uint.Z ps.term < uint.Z m.term →
    ⊢ ownRaftGhost (GF := GF) γ id ps md -∗ isMessage γ m ={E}=∗
      ownRaftGhost γ id ps md ∗ ⌜uint.Z m.commit = 0 ∧ (γ.reBoot.length : Int) ≤ uint.Z ps.commit⌝ := by
  intro HE Hty Hto Hlt
  simp only [isMessage, Hty]
  unfold ownRaftGhost isAcked
  iintro ⟨%γs, %V, %πc, %kl, H⟩ ⟨-, -, ⟨%i, %Hci, Hack⟩, -⟩
  iNamed H
  icases persistent_entails_right (wand_entails (ownLogGhost_boot (GF := GF) γ id ps kl (virt V πc))) $$ Hlg
    with ⟨⟨%Hbt, -⟩, Hlg⟩
  have hc0 := uint_Z_nonneg m.commit
  icases Hack with (%H0 | ⟨⟨%γa', %Hγa', #Hfrag⟩, -⟩)
  · imodintro
    isplitl
    · iexists γs, V, πc, kl
      iframe % # ∗
    · ipureintro; exact ⟨by omega, Hbt.1⟩
  rw [Hto] at Hγa'
  imod slot_open E γ id γs V Hsname HE $$ Hslot Hvirt with ⟨%E0, %HEV, Hsh, Hvirt, Hcl'⟩
  icases durShares_ack γ id _ E0 γa' m.term i Hγa' $$ Hsh Hfrag with ⟨%Hk0, Hsh⟩
  imod Hcl' $$ Hsh with -
  have Hk' := virt_acks_isSome V πc (m.term, i) (HEV.2.1 _ (by rw [Hk0]; rfl))
  obtain ⟨u, Hk⟩ := Option.isSome_iff_exists.mp Hk'
  icases persistent_entails_right (wand_entails (ownLogGhost_acks_term (GF := GF) γ id ps kl (virt V πc))) $$ Hlg
    with ⟨%Hacks_term, Hlg⟩
  have Hkt : uint.Z m.term ≤ uint.Z ps.term := Hacks_term _ (by rw [Hk]; rfl)
  exfalso
  omega

end ghost

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A higher-term heartbeat's receive line's phase step**: `UpdateTerm` (the intermediate shape,
`utSrv`, up to `toC`), then the follower's heartbeat handling at the new term (`hbSrv`, `hbResp`). -/
theorem phaseStepR_utHb (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .heartbeat m ents) evt)
    (hto : m.To' = id) (hgt : uint.Z s.term < uint.Z m.Term') (hpre : s.role ≠ .preCandidate)
    (hents : ents = []) (hc1 : 1 ≤ uint.Z (toPState s).commit)
    (hb : (absMsg .heartbeat m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .heartbeat m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .heartbeat m ents))
      (fun v => toC (confAbs C0) v = toC (confAbs C0) (utSrv a0 (uint.Z m.Term'))) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) (hbSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma.commitIndex))
        (P0 ++ [hbResp (utSrv a0 (uint.Z m.Term')) (idAbs id) (idAbs m.From')])) := by
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
  have hC'' : idAbs (absMsg .heartbeat m ents).dst ∈ confAbs C := by rw [mem_confAbs]; exact hC'
  have hfa : ma.type = .appendEntriesRequest ∧ ma.subtype = "heartbeat" ∧ ma.prevLogIndex = 0 ∧
      ma.entries = [] ∧ ma.dest = idAbs (absMsg .heartbeat m ents).dst ∧ ma.source = idAbs m.From' ∧
      ma.term = uint.Z m.Term' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]
    simp [hents]
    rfl
  obtain ⟨hmt, hmsub, hmprev, hments, hmd, hmsrc, hmterm⟩ := hfa
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hmterm, hR.1]; show ¬ uint.Z m.Term' < uint.Z s.term; omega)
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
  refine ⟨hbSrv (utSrv a (uint.Z m.Term')) (idAbs m.From') ma.commitIndex,
    [hbResp (utSrv a (uint.Z m.Term')) (idAbs id) (idAbs m.From')],
    ⟨rfl, toC_hbSrv _ _ _ _ _ hux, by rw [hbResp_toC _ _ _ _ _ hux]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have h2 := recvAt_heartbeat C (idAbs (absMsg .heartbeat m ents).dst) (utSrv a ma.term) ma hmd hC'' hmt rfl rfl
    hmsub hmprev hments (by simp only [utSrv]; rw [hR.2.2.2.2.2.2.1]; exact hc1)
  have := lineEffect_ut C e s c (absMsg .heartbeat m ents) evt a _ ma _ _ hev he' hin hout hC' hR hs hpre hgt
    bt bc bl bmt bi blt bk bmc hma h2
  rw [hmterm, hmsrc] at this
  exact lineEffect_mid_mono this (fun v hv => by rw [hv]; exact hux)

/-- **The facts of a higher-term heartbeat's receive line**: at the intermediate state `simFx_ut` (from
raft's facts of the receiver's log `L`), at the result `simFx_hb` from it, the commit index not
raised (the heartbeat's commit `0`). -/
theorem fxPresR_utHb (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (L : List EntryM)
    (u0 : Etcdraft.Server) (c0 t0 T : Int) (hiC : id ∈ C0) (hdst : ma.dest = idAbs id)
    (hty : ma.type = .appendEntriesRequest) (hsub : ma.subtype = "heartbeat") (hprev : ma.prevLogIndex = 0)
    (hents : ma.entries = []) (hcm0 : ma.commitIndex = 0) (hT63 : T < 2 ^ 63)
    (hbL : BootTerms C0.length 1 L) (hwL : PlogWf base0 L) (hwr : PlogWfR (entryID.mk (W64 0) (W64 0)) L)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      toC (confAbs C0) u0 = toC (confAbs C0) (utSrv a T) ∧
      cs1 = toC (confAbs C0) (hbSrv (utSrv a T) ma.source ma.commitIndex) ∧
      r1 = hbResp (utSrv a T) (idAbs id) ma.source ∧ ma.term = T ∧
      a.currentTerm = t0 ∧ a.commitIndex = c0 ∧ a.log = logAbs C0 C0.length 1 L ∧ t0 < T ∧ 1 ≤ c0) :
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
  obtain ⟨hu0, hc1, hr1, hmT, ht0, hc0, hlog, hlt, hc1'⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hmT, ht0]; omega)
  icases simFx_ut γ C σ id T L hsrv hiC (by rw [hσa, ht0]; exact hlt) hT63 (by rw [hσa]; exact hlog) hbL hwr
    c0 t0 (by rw [hσa]; exact hc0) (by rw [hσa]; exact ht0) $$ [$Htbl $Hfx $HL $Hcm $Hci] with ⟨Htbl, #Hu⟩
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = withNode σ (idAbs id) (utSrv (σ.s (idAbs id)) T) _root_.id _root_.id :=
    ⟨_, rfl⟩
  rw [← hσu]
  have hσud : σu.s ma.dest = utSrv a T := by rw [hσu, hdst]; simp [withNode, hσa]
  ihave #H1 := simFx_hb γ C σu ma L id (by rw [hσu]; exact hsrv) hiC hdst (by rw [hσu]; exact hpv)
    (by rw [hσu]; exact hcq) (by rw [hσud]; rfl) hty (by rw [hσud, hmT]; rfl) hsub hprev hents
    (by rw [hσud]; show 1 ≤ a.commitIndex; rw [hc0]; exact hc1') (by rw [hσu]; exact hmem)
    (by rw [hσud]; exact hlog) hbL hwL $$ [$Hu $HL]
  · ileft; ipureintro; rw [hσud, hcm0]; show ¬ a.commitIndex < 0; rw [hc0]; omega
  iframe Htbl
  isplitl
  · have hs : ∀ k, toC (hbRecvSt σu ma).server ((withNode σ (idAbs id) a' (fun b => b.without ma)
          (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s k) =
        toC (hbRecvSt σu ma).server ((hbRecvSt σu ma).s k) := by
      intro k
      rw [hbRecvSt_eq]
      show toC σu.server (if k = idAbs id then a' else σ.s k) =
        toC σu.server (if k = ma.dest then hbSrv (σu.s ma.dest) ma.source ma.commitIndex else σu.s k)
      rw [hσud, hdst]
      split
      · rw [hσu]; show toC σ.server a' = toC σ.server _; rw [hsrv, hcs', hc1]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    ihave #H3 := simFx_congr γ C (hbRecvSt σu ma)
      (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
      (by rw [hbRecvSt_eq, hσu]; rfl) (by rw [hbRecvSt_eq, hσu]; rfl)
      (by rw [hbRecvSt_eq, hσud, hph, hr1, hdst, hσu]; rfl) hs $$ H1
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

/-- A heartbeat response's numbers, at a term within the bound. -/
theorem hbresp_nums' (id : w64) (t : w64) (from' : w64) (cl : List w8) (hT : uint.Z t < traceNumBound) :
    ({ Msg.plain .heartbeatResp id from' t false with ctx := cl } : Msg).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hT
  unfold Msg.plain Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨by word, by simp, by simp, by simp, by simp, by simp⟩

end fx

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A heartbeat of a higher term than the node's.** -/
def UTHb (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgHeartbeat ∧ uint.Z s.term < uint.Z m.Term'

/-- **`raft.Step`'s traced bundle on a heartbeat of a higher term**: the receive line (`UpdateTerm`,
then the follower's heartbeat handling, the commit index unchanged), the preamble's `BecomeFollower`
line (skipped), then the response's send line (skipped). The end state is `heartbeatResult`'s at the
step-down (`hbEnd_simIdle` with `simServerR_ut`). -/
theorem stepBundle_traced_utHb : stepBundle_traced.on (GF := GF) (hG := hG) UTHb := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hgt⟩ := hp
  have hmty : mtypeOf m.Type' = some .heartbeat := by rw [hTy]; rfl
  have htrd : MsgType.traced .heartbeat = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .heartbeat m ents hmty htrd hsh
  have hto' : m.To' = id := hto .heartbeat hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2 (.inr (.inr hTy)) (by rw [hto', h])
  have hents : ents = [] := hsh.1 hTy
  have hb0 : γ.reBoot ≠ [] := hboot (.inl hTy)
  obtain ⟨hnA, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := hb_ne hTy
  have hbf : PreBF m s := ⟨hgt, hnPV, fun h => hnPVR h.1⟩
  have hleadF : preLead m = m.From' := by unfold preLead; rw [if_pos (.inr (.inl hTy))]
  have hpre : ∀ pvs, preState s m pvs = { becomeFollower s m.Term' m.From' with prvals := pvs } := by
    intro pvs; simp only [preState, hbf, ↓reduceIte, hleadF]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hT63 : uint.Z m.Term' < 2 ^ 63 := by have hb : traceNumBound = 2 ^ 61 := rfl; rw [hb] at hmT; omega
  have hmt2 : mtypeOf m.Type' = some .heartbeat ∧ MsgType.traced .heartbeat = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.heartbeat %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  ihave #Hmc := Hmsg $$ %MsgType.heartbeat %hmt2
  ihave #Hm := isMessageC_isMessage γ _ $$ Hmc
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hidC⟩ := hI0
  have hfa : ma.dest = idAbs id ∧ ma.source = idAbs m.From' ∧ ma.type = .appendEntriesRequest ∧
      ma.subtype = "heartbeat" ∧ ma.prevLogIndex = 0 ∧ ma.entries = [] ∧ ma.commitIndex = uint.Z m.Commit' ∧
      ma.term = uint.Z m.Term' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]
    simp [hto']
  obtain ⟨hmd, hms, hmty', hmsub, hmprev, hments, hmcm, hmterm⟩ := hfa
  have hwB : PlogWf base0 (toPState s).log := by have h := hs0.2.1; rw [hs0.1] at h; exact h
  have hbL : BootTerms tn.voters.length 1 (toPState s).log := fun k e hk he => hs0.2.2 k e (by omega) he
  have hcs1 : (toC (confAbs tn.voters) (hbSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma.commitIndex)).state =
      Etcdraft.follower := rfl
  imodintro
  iexists bfR bfl γ md c r id s γd tn cs0
    (toC (confAbs tn.voters) (hbSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma.commitIndex)) P0
    (P0 ++ [hbResp (utSrv a0 (uint.Z m.Term')) (idAbs id) (idAbs m.From')]) Λ
    (RecvLast evt id s c (absMsg .heartbeat m ents)) (fun o => o.isSome = true) k ma
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
      imod ownRaftGhost_hbHigher ⊤ γ id (toPState s) (absMsg .heartbeat m ents ctx) CoPset.subseteq_top rfl hto'
        hgt $$ Hg Hm with ⟨Hg, %Hcz⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .heartbeat m ents).NumsBelow traceNumBound := (hok .heartbeat hmty hreT htrd).1
      have hc1 : 1 ≤ uint.Z (toPState s).commit := by
        have : (1 : Int) ≤ γ.reBoot.length := by
          have := List.length_pos_iff.mpr hb0; omega
        have := Hcz.2; omega
      have hps := phaseStepR_utHb id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hgt hnpc hents hc1
        hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .heartbeat m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs .heartbeat evt bfl k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · have hW1 : W64 (uint.Z s.logst.committed) = s.logst.committed := by word
        have hW2 : W64 (uint.Z s.term) = s.term := by word
        iapply fxPresR_utHb γ id ma _ s tn.voters cs0 _ P0 _ (toPState s).log (utSrv a0 (uint.Z m.Term'))
          (uint.Z s.logst.committed) (uint.Z s.term) (uint.Z m.Term') hidC hmd hmty' hmsub hmprev hments
          (by rw [hmcm]; exact Hcz.1) hT63 hbL hwB Hwr
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
          refine ⟨hux, by rw [hms]; exact toC_hbSrv _ _ _ _ _ hux, ?_, hmterm, hRa.1, hRa.2.2.2.2.2.2.1,
            hRa.2.2.2.2.2.1, hgt, hc1⟩
          rw [hms]; rfl
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
        (phaseStepBF_ut id c s _ evt (absMsg .heartbeat m ents) tn.voters _ _ (recvEv_name evt id s c _ hev) hgt
          rfl hT63)
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
        isplitr; · iintro %hg; exact (hnA hg).elim
        isplitr
        · -- the response's send line, skipped by the specification
          iintro %_ ⟨Hgh, Hc⟩
          rw [show ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).gh.tr = some γd from htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
          imodintro
          have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
          have hnb : (absMsg .heartbeat m ents).NumsBelow traceNumBound := (hok .heartbeat hmty hreT htrd).1
          have hn := hbresp_nums' id m.Term' m.From' ctx hmT
          have hcm : uint.nat (plogCommitTo s.logst.committed m.Commit') < traceNumBound := by
            unfold plogCommitTo; split
            · exact hnb.2.2.2.2.1
            · exact Hb.2
          have ht2 : uint.nat m.Term' < traceNumBound := by word
          have hOkR : ∀ e, (∃ mm ∈ [{ Msg.plain .heartbeatResp id m.From'
                ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).term false with ctx := ctx }],
              SendEvOf (W64 11) id { ({ ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
                lead := m.From' } : NState) with
                logst := { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).logst with
                  committed := plogCommitTo ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).logst.committed
                    m.Commit' } } c mm e) →
              TraceEv.Ok (elements c.incoming).length e := by
            intro e ⟨mm, hmm, he⟩
            simp only [List.mem_singleton] at hmm; subst hmm
            exact sendEvOf_ok _ id _ c _ e _ he (by decide) ht2 hcm Hb.1 hn (Nat.le_refl _)
          iapply skipGate_hbresp γd γ r id c _ { Msg.plain .heartbeatResp id m.From'
              ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState).term false with ctx := ctx }
            tn.voters _ _ (ownStepGhost γ md c id s) rfl (by simp only [Msg.plain]; exact hne) hOkR
          iframe Hgh Hc
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
  · -- the closing wand: raft's step-down and heartbeat handling, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨pvs, hse⟩ : ∃ pvs : GMap w64 Progress,
        s' = heartbeatResult id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
          lead := m.From' } m ctx := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.1 (by simp [becomeFollower])
      unfold FollowerStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [hTy] at hf
      simp [MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat] at hf
      exact ⟨pvs, hf.2⟩
    subst hse
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) (hbSrv (utSrv a0 (uint.Z m.Term')) (idAbs m.From') ma.commitIndex))
        (P0 ++ [hbResp (utSrv a0 (uint.Z m.Term')) (idAbs id) (idAbs m.From')]) C cs P →
        SimIdle C (heartbeatResult id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
          lead := m.From' } m ctx) cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hnb := (hok .heartbeat hmty hre htrd).1
      have hmc63 : uint.Z m.Commit' < 2 ^ 63 := (numsBelow_63 hnb).2.2.2.2
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0']
      exact hbEnd_simIdle tn.voters id { becomeFollower s m.Term' (W64 0) with prvals := pvs } m ents ctx
        (utSrv a0 (uint.Z m.Term')) ma (simServerR_ut _ _ s a0 m.Term' pvs hR0 hgt) hs0 hT63 bc bl rfl hmc63 hma
    have hlast : ∀ o, RecvLast evt id s c (absMsg .heartbeat m ents) o → stepLastEv Λ o := by
      rintro o ⟨e0, rfl, -⟩; exact .inr rfl
    have hout : OutTrStep s (heartbeatResult id { ({ becomeFollower s m.Term' m.From' with prvals := pvs } : NState) with
        lead := m.From' } m ctx) := by
      intro _ x hx
      simp only [heartbeatResult, sendMsgs, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact .inl hx
      · exact .inr (Msg.trOk_of_nums_hbresp rfl rfl (fun _ => hbresp_nums' id m.Term' m.From' ctx hmT))
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
