/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a response of a higher term**
(`MsgAppResp`, `MsgHeartbeatResp`; 2026-11-10, trace-check Q8 stage 1 slice 20b, `notes/decisions.md`,
"Q8 stage 1 (slice 20b)").

Raft steps down in `Step`'s preamble (`becomeFollower(m.Term, None)`, its `BecomeFollower` line skipped
by the specification: `phaseStepBF_ut`), then ignores the response as a follower. The specification's
receive line: `UpdateTerm`, then the response recorded at the follower (`respSrv`, in fields a
follower's idle relation does not read): `lineEffect_ut` with `recvAt_resp`; its facts `simFx_ut` then
`simFx_resp`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUT

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Raft's facts of the node's log** (uncompacted): its records, committed prefix and commit
certificate at its term, and its shape; the ghost state unchanged. -/
theorem ownRaftGhost_logFacts (γ : RaftNames) (id : w64) (s : PState) {md : Bool} (hb : s.base = base0) :
    ownRaftGhost (GF := GF) γ id s md ⊢ ownRaftGhost γ id s md ∗
      (logRecs γ base0 s.log ∗ isCommitted γ (s.log.take (uint.Z s.commit).toNat) ∗
        commitIn γ s.log s.commit s.term) ∗ ⌜PlogWfR base0 s.log⌝ := by
  iintro Hg
  ihave %Hok := ownRaftGhost_logOk γ id s $$ Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  ihave #HcI := ownLogGhost_commitIn γ id s kl (virt V πc) $$ Hlg
  icases HcI with ⟨%fpw, %Hfo, -, #Hr, #Hcom⟩
  ihave #Hcm := ownLogGhost_cmt γ id s kl (virt V πc) $$ Hlg
  icases Hcm with ⟨%fp2, %Hf2, -, #Hcp⟩
  have h1 : fpw = [] := by
    have h := Hfo.1.1; rw [hb, base0_index] at h; exact List.eq_nil_of_length_eq_zero (by omega)
  have h2 : fp2 = [] := by
    have h := Hf2.1; rw [hb, base0_index] at h; exact List.eq_nil_of_length_eq_zero (by omega)
  subst h1 h2
  rw [hb]
  simp only [cprefix, List.nil_append]
  isplitl [Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd]
  · iunfold ownRaftGhost
    iexists γs, V, πc, kl
    iframe Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd
    ipureintro; exact ⟨Hsname, Hfresh, Hidnz, Hhist, Hlead_ok, Hfollower_votes, Hrole_ok, Hmode⟩
  isplitr
  · iframe Hr Hcp Hcom
  · ipureintro; have h := Hok.1; rw [hb] at h; exact h

/-- **A higher-term response's receive line's phase step**: `UpdateTerm` (the intermediate shape,
`utSrv`, up to `toC`), then the response recorded at the follower (`respSrv`); the list kept. -/
theorem phaseStepR_utResp (id : w64) (c : CfgM) (s : NState) (ty : MsgType) (m : MessageM)
    (ents : List EntryM) (evt : w64) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (a0 : Etcdraft.Server) (ha0 : toC (confAbs C0) a0 = cs0)
    (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg ty m ents) evt) (hto : m.To' = id)
    (hresp : ty = .appResp ∨ ty = .heartbeatResp)
    (hgt : uint.Z s.term < uint.Z m.Term') (hpre : s.role ≠ .preCandidate)
    (hb : (absMsg ty m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg ty m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg ty m ents))
      (fun v => toC (confAbs C0) v = toC (confAbs C0) (utSrv a0 (uint.Z m.Term'))) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0) (VPin C0 (toC (confAbs C0) (respSrv (utSrv a0 (uint.Z m.Term')) ma)) P0) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg ty m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg ty m ents).dst s c (absMsg ty m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg ty m ents).dst ∈ C := by rw [hdst]; exact hC
  obtain ⟨hmt, hmd, -, -, -, hr, -⟩ := msgAbs_recvTy hev hma
  have hrt : ma.type = .appendEntriesResponse := by
    rcases hresp with rfl | rfl
    · exact hr (.inl rfl)
    · exact hr (.inr rfl)
  have hph := recvPhantoms_resp ma a (.inl hrt)
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
  have hC'' : idAbs (absMsg ty m ents).dst ∈ confAbs C := by rw [mem_confAbs]; exact hC'
  refine ⟨respSrv (utSrv a (uint.Z m.Term')) ma, [],
    ⟨rfl, toC_respSrv _ _ _ ma hux, by rw [List.append_nil]⟩, fun x hx => by simp at hx, ?_⟩
  rw [← hdst]
  simp only [List.nil_append, hph, List.foldl_nil]
  have h2 := recvAt_resp C (idAbs (absMsg ty m ents).dst) (utSrv a ma.term) ma hmd hC'' (.inr hrt) rfl
    (by simp only [utSrv]; decide)
  have := lineEffect_ut C e s c (absMsg ty m ents) evt a (respSrv (utSrv a ma.term) ma) ma _ _ hev he' hin hout
    hC' hR hs hpre hgt bt bc bl bmt bi blt bk bmc hma h2
  rw [hmt] at this
  exact lineEffect_mid_mono this (fun v hv => by rw [hv]; exact hux)

/-- **The facts of a higher-term response's receive line**: at the intermediate state `simFx_ut` (from
raft's facts of the receiver's log `L`), at the result `simFx_resp` from it. -/
theorem fxPresR_utResp (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (L : List EntryM) (u0 : Etcdraft.Server)
    (c0 t0 T : Int) (hiC : id ∈ C0) (hdst : ma.dest = idAbs id) (hty : ma.type = .appendEntriesResponse)
    (hT63 : T < 2 ^ 63) (hbL : BootTerms C0.length 1 L) (hwr : PlogWfR (entryID.mk (W64 0) (W64 0)) L)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      toC (confAbs C0) u0 = toC (confAbs C0) (utSrv a T) ∧ cs1 = toC (confAbs C0) (respSrv (utSrv a T) ma) ∧
      a.currentTerm = t0 ∧ a.commitIndex = c0 ∧ a.log = logAbs C0 C0.length 1 L ∧ t0 < T) :
    logRecs (GF := GF) γ base0 L ∗ isCommitted γ (L.take c0.toNat) ∗ commitIn γ L (W64 c0) (W64 t0) ⊢
      FxPresR (GF := GF) γ id ma E (fun v => toC (confAbs C0) v = toC (confAbs C0) u0) (recvPhantoms ma)
        (IdlePin s C0 cs0 P0) (VPin C0 cs1 P0) := by
  iintro ⟨#HL, #Hcm, #Hci⟩
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [] := by simpa using hP
  subst hP'
  obtain ⟨hu0, hc1, ht0, hc0, hlog, hlt⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_resp ma a (.inl hty)
  icases simFx_ut γ C σ id T L hsrv hiC (by rw [hσa, ht0]; exact hlt) hT63 (by rw [hσa]; exact hlog) hbL hwr
    c0 t0 (by rw [hσa]; exact hc0) (by rw [hσa]; exact ht0) $$ [$Htbl $Hfx $HL $Hcm $Hci] with ⟨Htbl, #Hu⟩
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = withNode σ (idAbs id) (utSrv (σ.s (idAbs id)) T) _root_.id _root_.id :=
    ⟨_, rfl⟩
  rw [← hσu]
  have hσud : σu.s (idAbs id) = utSrv a T := by rw [hσu]; simp [withNode, hσa]
  have hfl : Etcdraft.follower ≠ Etcdraft.leader := by decide
  ihave #H1 := simFx_resp γ C σu (idAbs id) ma (.inr (by rw [hty]; decide))
    (.inl (by rw [hσud]; exact hfl)) $$ Hu
  iframe Htbl
  isplitl
  · have hs : ∀ k, toC (withNode σu (idAbs id) (respSrv (σu.s (idAbs id)) ma) (fun b => b.without ma)
          _root_.id).server ((withNode σ (idAbs id) a' (fun b => b.without ma)
          (fun b => ([] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s k) =
        toC (withNode σu (idAbs id) (respSrv (σu.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).server
          ((withNode σu (idAbs id) (respSrv (σu.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).s k) := by
      intro k
      show toC σu.server (if k = idAbs id then a' else σ.s k) =
        toC σu.server (if k = idAbs id then respSrv (σu.s (idAbs id)) ma else σu.s k)
      split
      · rw [hσud, hσu]; show toC σ.server a' = toC σ.server _; rw [hsrv, hcs', hc1]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    ihave #H3 := simFx_congr γ C
      (withNode σu (idAbs id) (respSrv (σu.s (idAbs id)) ma) (fun b => b.without ma) _root_.id)
      (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
      (by rw [hσu]; rfl) (by rw [hσu]; rfl) (by rw [hph, hσu]; rfl) hs $$ H1
    iexact H3
  · iintro %v %hv
    iapply simFx_congr γ C σu (withNode σ (idAbs id) v _root_.id _root_.id) (by rw [hσu]; rfl) (by rw [hσu]; rfl)
      (by rw [hσu]; rfl)
    · intro k
      show toC σu.server (if k = idAbs id then v else σ.s k) = toC σu.server (σu.s k)
      split
      · rename_i hk; subst hk
        rw [hσud, hσu]; show toC σ.server v = toC σ.server _; rw [hsrv, hv, hu0]
      · rename_i hk
        rw [hσu]; simp [withNode, hk]
    iexact Hu

end ghost

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The tracker's step-down to a higher term with no leader** (`Step`'s preamble on a message not
from a leader), related to the specification's `UpdateTerm` (`utSrv`). -/
theorem simServerR_ut (C : List w64) (bl : Nat) (s : NState) (a : Etcdraft.Server) (t : w64)
    (pvs : GMap w64 Progress) (hR : SimServerR C bl (toPState s) a) (hgt : uint.Z s.term < uint.Z t) :
    SimServerR C bl (toPState { becomeFollower s t (W64 0) with prvals := pvs }) (utSrv a (uint.Z t)) := by
  obtain ⟨hT, -, -, -, hB, hLog, hCm, hCfg, hPc, -, -⟩ := hR
  have hne : a.currentTerm ≠ uint.Z t := by rw [hT]; show uint.Z s.term ≠ _; omega
  have hne' : t ≠ s.term := fun h => by rw [h] at hgt; omega
  refine ⟨rfl, ?_, ?_, ?_, hB, hLog, hCm, hCfg, hPc, ?_, ?_⟩
  · simp [utSrv, toPState, becomeFollower, proleRole, roleAbs]
  · simp [utSrv, hne, toPState, becomeFollower, resetTo, resetTo0, hne', idAbs, Etcdraft.nil]
  · simp [utSrv, toPState, becomeFollower, idAbs, Etcdraft.nil]
  · intro h; simp [toPState, becomeFollower, proleRole] at h
  · intro h; simp [toPState, becomeFollower, proleRole] at h

end pure

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An append or heartbeat response of a higher term than the node's.** -/
def UTResp (s : NState) (m : MessageM) : Prop :=
  (m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp) ∧ uint.Z s.term < uint.Z m.Term'

/-- **`raft.Step`'s traced bundle on a response of a higher term**: the receive line (`UpdateTerm`, then
the response recorded at the follower), the preamble's `BecomeFollower` line (skipped: `bfCond` reads
the receive line), nothing else (a follower ignores a response). The resources are `bfR`'s with the
receive event last after the receive line and an event last after the step-down. -/
theorem stepBundle_traced_utResp : stepBundle_traced.on (GF := GF) (hG := hG) UTResp := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hgt⟩ := hp
  obtain ⟨ty, hmty, hresp⟩ : ∃ ty, mtypeOf m.Type' = some ty ∧ (ty = .appResp ∨ ty = .heartbeatResp) := by
    rcases hTy with h | h
    · exact ⟨.appResp, by rw [h]; rfl, .inl rfl⟩
    · exact ⟨.heartbeatResp, by rw [h]; rfl, .inr rfl⟩
  have htrd : ty.traced = true := by rcases hresp with rfl | rfl <;> rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of ty m ents hmty htrd hsh
  have hto' : m.To' = id := hto ty hmty htrd
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup⟩ :=
    resp_ne (by rcases hTy with h | h; exact .inl h; exact .inr (.inl h))
  have hnS : m.Type' ≠ MsgSnap := by
    rcases hTy with h | h <;> rw [h] <;> simp [MsgAppResp, MsgHeartbeatResp, MsgSnap]
  have hbf : PreBF m s := ⟨hgt, hnPV, fun h => hnPVR h.1⟩
  have hlead0 : preLead m = W64 0 := by
    unfold preLead; rw [if_neg]; rintro (h | h | h) <;> first | exact hnA h | exact hnH h | exact hnS h
  have hpre : ∀ pvs, preState s m pvs = { becomeFollower s m.Term' (W64 0) with prvals := pvs } := by
    intro pvs; simp only [preState, hbf, ↓reduceIte, hlead0]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hT63 : uint.Z m.Term' < 2 ^ 63 := by have hb : traceNumBound = 2 ^ 61 := rfl; rw [hb] at hmT; omega
  have hmt2 : mtypeOf m.Type' = some ty ∧ ty.traced = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %ty %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hidC⟩ := hI0
  obtain ⟨hmt, hmd0, -, -, -, hr, -⟩ := msgAbs_recvTy hev hma
  have hmd : ma.dest = idAbs id := by rw [hmd0]; show idAbs m.To' = _; rw [hto']
  have hmty' : ma.type = .appendEntriesResponse := by
    rcases hresp with rfl | rfl
    · exact hr (.inl rfl)
    · exact hr (.inr rfl)
  have hbL : BootTerms tn.voters.length 1 (toPState s).log := fun k e hk he => hs0.2.2 k e (by omega) he
  have hcs1 : (toC (confAbs tn.voters) (respSrv (utSrv a0 (uint.Z m.Term')) ma)).state = Etcdraft.follower := by
    show (respSrv (utSrv a0 (uint.Z m.Term')) ma).state = _
    rw [(respSrv_fields _ _).2.2.2.1]; rfl
  imodintro
  iexists bfR bfl γ md c r id s γd tn cs0 (toC (confAbs tn.voters) (respSrv (utSrv a0 (uint.Z m.Term')) ma)) P0 P0
    Λ (RecvLast evt id s c (absMsg ty m ents)) (fun o => o.isSome = true) k ma
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
      have hnb : (absMsg ty m ents).NumsBelow traceNumBound := (hok ty hmty hreT htrd).1
      have hps := phaseStepR_utResp id c s ty m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hresp hgt hnpc
        hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg ty m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_tracedL γd γ r id c s m ents sn ctx rs ty evt bfl k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · have hW1 : W64 (uint.Z s.logst.committed) = s.logst.committed := by word
        have hW2 : W64 (uint.Z s.term) = s.term := by word
        iapply fxPresR_utResp γ id ma _ s tn.voters cs0 _ P0 (toPState s).log (utSrv a0 (uint.Z m.Term'))
          (uint.Z s.logst.committed) (uint.Z s.term) (uint.Z m.Term') hidC hmd hmty' hT63 hbL Hwr
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          have hux := toC_utSrv _ _ _ (uint.Z m.Term') hcx
          exact ⟨hux, toC_respSrv _ _ _ ma hux, hRa.1, hRa.2.2.2.2.2.2.1, hRa.2.2.2.2.2.1, hgt⟩
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
        (phaseStepBF_ut id c s _ evt (absMsg ty m ents) tn.voters _ _ (recvEv_name evt id s c _ hev) hgt rfl hT63)
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
  · -- the closing wand: raft's step-down, the response ignored
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => by
      rcases hTy with h | h
      · exact CloseAt.of_traced (ty := .appResp) (by rw [h]; rfl) rfl
      · exact CloseAt.of_traced (ty := .heartbeatResp) (by rw [h]; rfl) rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨pvs, hse⟩ : ∃ pvs : GMap w64 Progress, s' = { becomeFollower s m.Term' (W64 0) with prvals := pvs } := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.1 (by simp [becomeFollower])
      unfold FollowerStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      refine ⟨pvs, ?_⟩
      rcases hTy with h' | h' <;> rw [h'] at hf <;>
        simp [MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat, MsgBeat, MsgAppResp, MsgHeartbeatResp,
          MsgCheckQuorum] at hf <;> exact hf.2
    subst hse
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) (respSrv (utSrv a0 (uint.Z m.Term')) ma)) P0 C cs P →
        SimIdle C { becomeFollower s m.Term' (W64 0) with prvals := pvs } cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      refine ⟨respSrv (utSrv a0 (uint.Z m.Term')) ma, rfl,
        simServerR_respSrv ma (simServerR_ut _ _ s a0 m.Term' pvs hR0 hgt) (.inr (by rw [hmty']; decide))
          (.inl (by simp [toPState, becomeFollower, proleRole])), hs0, hP0, hT63, bc, bl⟩
    have hlast : ∀ o, RecvLast evt id s c (absMsg ty m ents) o → stepLastEv Λ o := by
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
    · ipureintro; exact OutTrStep.of_sub (fun _ h => h)
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact OutTrStep.of_sub (fun _ h => h)
    · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (hmono hre) $$ Hc
    · ipureintro; exact OutTrStep.of_sub (fun _ h => h)

end paths

end EtcdGrove
end Perennial
