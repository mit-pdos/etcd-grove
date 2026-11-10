/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a follower's `MsgHeartbeat` of its
term** (2026-11-10, trace-check Q8 stage 1 slice 19b, `notes/decisions.md`, "Q8 stage 1 (slice 19b)").

The receive line is the specification's heartbeat handling at a follower (`lineEffect_heartbeatRecv`:
the commit raised to the heartbeat's, the leader adopted, the response pending), and the response's
send line is skipped by the specification (`phaseStepB_skip`). The receive line's facts (`FxPresR`)
need the receiver's `srvFacts` at the raised commit index: its commit certificate and committed prefix,
which come from the heartbeat's raft facts (`isMessage`, which the bundle takes since this slice), moved
to the receiver's log as raft's own proof moves them (`ownRaftGhost_step_heartbeat`):
`ownRaftGhost_hbFacts` derives them, persistently, from raft's ghost state lent to the receive gate,
without changing it; `srvFacts_log_eq` identifies the specification server's recorded log with raft's
(their terms agree through `logAbs`, both have records).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- An empty full prefix at the zero base. -/
theorem fullOk_base0_nil : FullOk base0 ([] : List EntryM) :=
  ⟨by simp [base0_index], by intro k e h; simp at h, rfl⟩

/-- A heartbeat's raft facts (`Refinement.lean`'s private `isMessage_heartbeat_inv`). -/
theorem isMessage_hb_inv (γ : RaftNames) (m : Msg) :
    m.ty = .heartbeat →
    ⊢ isMessage (GF := GF) γ m -∗
      isLeader γ m.src m.term ∗
      (∃ Fl, leadFull γ m.term Fl ∗ commitIn γ Fl m.commit m.term ∗
         isCommitted γ (Fl.take (uint.Z m.commit).toNat)) ∗
      (∃ i, ⌜uint.Z m.commit ≤ uint.Z i⌝ ∗ isAcked γ m.dst m.term i) ∗
      ⌜m.src ≠ W64 0⌝ ∗
      (⌜m.ctx = []⌝ ∨ ∃ (q : w64) (recs : List RqRec),
         ⌜m.ctx = u64Le q ∧ uint.nat q ≤ recs.length⌝ ∗ rqLb γ m.src m.term recs ∗
         [∗list] r ∈ recs, rqRecOk γ m.term r) := by
  intro Hty
  unfold isMessage; rw [Hty]
  iintro H; iexact H

/-- **A heartbeat's commit certificates, moved to the receiver's log** (raft's
`ownRaftGhost_step_heartbeat`'s commit bullets, without the step): at a non-leader of the heartbeat's
term with an uncompacted log, raft's ghost state and the heartbeat's facts give, persistently, the
log's records and, when the heartbeat raises the commit index, the raised index within the log, its
commit certificate at the node's term and the committed prefix; the ghost state is unchanged. -/
theorem ownRaftGhost_hbFacts (γ : RaftNames) (id : w64) (s : PState) (m : Msg) {md : Bool} :
    m.ty = .heartbeat → m.dst = id → m.term = s.term → s.role ≠ .leader → s.base = base0 →
    PlogWf base0 s.log →
    ⊢ isMessage (GF := GF) γ m -∗ ownRaftGhost γ id s md ={⊤}=∗
      ownRaftGhost γ id s md ∗ logRecs γ base0 s.log ∗
      (⌜¬ uint.Z s.commit < uint.Z m.commit⌝ ∨
        (⌜uint.Z s.commit < uint.Z m.commit ∧ uint.Z m.commit ≤ s.log.length⌝ ∗ commitIn γ s.log m.commit s.term ∗
          isCommitted γ (s.log.take (uint.Z m.commit).toNat))) := by
  intro Hty Hto Hterm Hrole Hbase Hw
  iintro #Hm Hown
  imod heartbeat_commit_le_last ⊤ γ id s m CoPset.subseteq_top Hty Hto (by rw [Hterm]; exact Int.le_refl _)
    (fun _ => Hrole) $$ Hown Hm with ⟨Hown, %Hcm⟩
  have Hlen : plogLastIndexZ s.base s.log = s.log.length := by
    unfold plogLastIndexZ; rw [Hbase, base0_index]; simp
  rw [Hlen] at Hcm
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  ihave ⟨%Hok, #Hrecs⟩ := ownLogGhost_recs $$ Hlg
  rw [Hbase]
  icases isMessage_hb_inv γ m Hty $$ Hm with ⟨-, ⟨%Fl, #Hfl, #Hmc, #Hmcm⟩, ⟨%i, %Hi, #Hack⟩, -, -⟩
  rw [Hto, Hterm]
  imod ownLogGhost_ack_agree ⊤ γ id s kl γs V πc i Hsname CoPset.subseteq_top $$ Hslot Hvirt Hlg Hack
    with ⟨Hvirt, Hlg, #Hagree⟩
  by_cases Hlt : uint.Z s.commit < uint.Z m.commit
  · have Hci : uint.Z s.commit < uint.Z i := by omega
    ihave #Ha := Hagree $$ %(⟨Hrole, Hci⟩)
    rw [Hbase]
    icases ackAgree_full γ base0 s.log [] s.term i fullOk_base0_nil (by rw [base0_index]; exact uint_Z_nonneg _)
      $$ Ha with ⟨%X, #HX, %HsX, %HXi⟩
    simp only [List.nil_append] at HXi
    icases leadFull_wf γ s.term X $$ HX with ⟨%HwX, #HrX⟩
    ihave %Hmt := full_match γ X s.log i HwX.1 Hw HsX HXi $$ HrX Hrecs
    icases leadFull_wf γ s.term Fl $$ Hfl with ⟨%HwFl, #HrFl⟩
    ihave #Hmcj := commitIn_j γ _ _ _ $$ Hmc
    have HsXc : (plogTermAt base0 X m.commit).isSome := full_term_at_some X m.commit i HsX (by omega)
    have HmX := Hmt m.commit (by omega)
    have HsF : (plogTermAt base0 s.log m.commit).isSome := by rw [← HmX]; exact HsXc
    iunfold commitJ at Hmcj
    icases Hmcj with (%H0 | ⟨%t, %n, %G, #Hq, %Hc', %Ht, %HG⟩)
    · -- a commit index within the bootstrap log, which both logs start with
      obtain ⟨Hcb, Hct⟩ := H0
      have HsFl : (plogTermAt base0 Fl m.commit).isSome := by
        rw [← Hct]
        exact plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by
          unfold plogLastIndexZ; rw [base0_index]; omega⟩
      obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp HsFl
      have HcFl := (plogTermAt_some_range _ _ _ _ Hx).2
      unfold plogLastIndexZ at HcFl; rw [base0_index] at HcFl
      icases logRecs_boot_take γ s.log Hw $$ Hrecs with %Ht1
      icases logRecs_boot_take γ Fl HwFl.1 $$ HrFl with %Ht2
      icases logRecs_boot_termAt γ s.log Hw $$ Hrecs with %Ha1
      icases logRecs_boot_termAt γ Fl HwFl.1 $$ HrFl with %Ha2
      have Htk : s.log.take (uint.Z m.commit).toNat = Fl.take (uint.Z m.commit).toNat := by
        rw [Ht1 _ (by omega) (by omega), Ht2 _ (by omega) (by omega)]
      have Hta : plogTermAt base0 s.log m.commit = plogTermAt base0 Fl m.commit := by
        rw [← Ha1 m.commit Hcb (by omega), ← Ha2 m.commit Hcb (by omega)]
      imodintro
      isplitl [Hvirt Hlg Hlcm Hrd]
      · iunfold ownRaftGhost
        iexists γs, V, πc, kl
        iframe Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd
        ipureintro; exact ⟨Hsname, Hfresh, Hidnz, Hhist, Hlead_ok, Hfollower_votes, Hrole_ok, Hmode⟩
      iframe Hrecs
      iright
      isplitr; · ipureintro; exact ⟨Hlt, by omega⟩
      isplitr
      · iapply commitIn_agree γ Fl s.log m.commit s.term s.term (Int.le_refl _) Hta Htk $$ Hmc
      · rw [Htk]; iexact Hmcm
    · ihave %Hn := cq_term _ _ _ _ $$ Hq
      have HsG : (plogTermAt base0 G m.commit).isSome :=
        full_term_at_some G m.commit n (by rw [Hn]; rfl) Hc'
      ihave %HXl := leadFull_agree γ s.term X Fl m.commit HsXc (by rw [← HG]; exact HsG) $$ HX Hfl
      ihave %Htk := full_take_eq γ s.log Fl m.commit Hw HwFl.1 HsF (HmX.symm.trans HXl) $$ Hrecs HrFl
      imodintro
      isplitl [Hvirt Hlg Hlcm Hrd]
      · iunfold ownRaftGhost
        iexists γs, V, πc, kl
        iframe Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd
        ipureintro; exact ⟨Hsname, Hfresh, Hidnz, Hhist, Hlead_ok, Hfollower_votes, Hrole_ok, Hmode⟩
      iframe Hrecs
      iright
      isplitr; · ipureintro; exact ⟨Hlt, by omega⟩
      isplitr
      · iapply commitIn_move γ Fl s.log m.commit s.term s.term (Int.le_refl _) HwFl.1 Hw
          (by rw [← HG]; exact HsG) ((HmX).symm.trans HXl) $$ HrFl Hrecs Hmc
      · rw [Htk]; iexact Hmcm
  · imodintro
    isplitl [Hvirt Hlg Hlcm Hrd]
    · iunfold ownRaftGhost
      iexists γs, V, πc, kl
      iframe Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd
      ipureintro; exact ⟨Hsname, Hfresh, Hidnz, Hhist, Hlead_ok, Hfollower_votes, Hrole_ok, Hmode⟩
    iframe Hrecs
    ileft; ipureintro; exact Hlt

/-- **A recorded log is determined by its abstraction** (with the bootstrap positions' terms):
two logs with records whose abstractions (`logAbs`, which keeps the terms past the bootstrap
positions) agree are equal (`full_take_eq` at their last index). -/
theorem log_eq_of_abs (γ : RaftNames) (C : List w64) (es L : List EntryM)
    (hb1 : BootTerms C.length 1 es) (hb2 : BootTerms C.length 1 L)
    (habs : logAbs C C.length 1 es = logAbs C C.length 1 L)
    (hw1 : PlogWf base0 es) (hw2 : PlogWf base0 L) (hl : L.length < 2 ^ 63) :
    logRecs (GF := GF) γ base0 es ∗ logRecs γ base0 L ⊢ ⌜es = L⌝ := by
  have hlen : es.length = L.length := by
    have := congrArg List.length habs; simpa [logAbs_length] using this
  iintro ⟨#H1, #H2⟩
  rcases Nat.eq_zero_or_pos L.length with h0 | hpos
  · ipureintro
    rw [List.length_eq_zero_iff.1 h0, List.length_eq_zero_iff.1 (hlen.trans h0)]
  · have hn1 : L.length - 1 < es.length := by omega
    have hn2 : L.length - 1 < L.length := by omega
    have ht := terms_of_absTerms C es L hb1 hb2 (L.length - 1) hn1 hn2 (by rw [habs])
    have hk : ((L.length - 1 : Nat) : Int) + 1 < 2 ^ 63 := by omega
    have hS : (plogTermAt base0 es (W64 (((L.length - 1 : Nat) : Int) + 1))).isSome := by
      rw [plogTermAt_succ _ _ hk, List.getElem?_eq_getElem hn1]; rfl
    have hE : plogTermAt base0 es (W64 (((L.length - 1 : Nat) : Int) + 1)) =
        plogTermAt base0 L (W64 (((L.length - 1 : Nat) : Int) + 1)) := by
      rw [plogTermAt_succ _ _ hk, plogTermAt_succ _ _ hk, ht]
    icases full_take_eq γ es L _ hw1 hw2 hS hE $$ H1 H2 with %Htk
    ipureintro
    have hc : (uint.Z (W64 (((L.length - 1 : Nat) : Int) + 1))).toNat = L.length := by
      have : uint.Z (W64 (((L.length - 1 : Nat) : Int) + 1)) = ((L.length - 1 : Nat) : Int) + 1 := by word
      rw [this]; omega
    rw [hc, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at Htk
    exact Htk

/-- A heartbeat's receiver after it (the specification's `hbRecvSt`), as a node update. -/
theorem hbRecvSt_eq (σ : Etcdraft.State) (ma : Etcdraft.Msg) :
    hbRecvSt σ ma = withNode σ ma.dest (hbSrv (σ.s ma.dest) ma.source ma.commitIndex) (fun b => b.without ma)
      (fun b => b.with (hbResp (σ.s ma.dest) ma.dest ma.source)) := by
  unfold hbRecvSt Etcdraft.State.commitTo
  exact withLead_reply_upd σ ma.dest ma.source
    (fun v => { v with commitIndex := max v.commitIndex ma.commitIndex }) (hbResp (σ.s ma.dest) ma.dest ma.source) ma

/-- The specification's handling of a heartbeat at a follower of its term (`receive_heartbeat`'s). -/
theorem handleAER_hb (σ : Etcdraft.State) (ma : Etcdraft.Msg) (hf : (σ.s ma.dest).state = Etcdraft.follower)
    (hterm : ma.term = (σ.s ma.dest).currentTerm) (hsub : ma.subtype = "heartbeat")
    (hprev : ma.prevLogIndex = 0) (hents : ma.entries = []) (hc : 1 ≤ (σ.s ma.dest).commitIndex) :
    σ.handleAppendEntriesRequest ma.dest ma.source ma = .ok [hbRecvSt σ ma] := by
  apply handleAER_accept σ ma.dest ma.source ma _ hf hterm (by simp [hprev]) (by rw [hsub]; decide) none none
  · unfold Etcdraft.State.conflictAppendEntriesRequest; simp [hents, Pure.pure, Except.pure]
  · unfold Etcdraft.State.noConflictAppendEntriesRequest; simp [hents, Pure.pure, Except.pure]
  · rw [alreadyDone_heartbeat σ ma.dest ma.source ma hc hsub hprev hents]
    rfl


end ghost

section hb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The facts after a follower's heartbeat of its term** (`hbRecvSt`): the commit index raised to
the heartbeat's, the leader adopted, the response pending. The receiver's raised commit needs its
certificate and committed prefix (the last premise, from the heartbeat's raft facts moved to raft's log
`L`: `ownRaftGhost_hbFacts`), and the receiver's recorded log is `L` (`log_eq_of_abs`). -/
theorem simFx_hb (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (ma : Etcdraft.Msg) (L : List EntryM)
    (i : w64) (hsrv : σ.server = confAbs C) (hiC : i ∈ C) (hdst : ma.dest = idAbs i)
    (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hf : (σ.s ma.dest).state = Etcdraft.follower) (hty : ma.type = .appendEntriesRequest)
    (hterm : ma.term = (σ.s ma.dest).currentTerm) (hsub : ma.subtype = "heartbeat")
    (hprev : ma.prevLogIndex = 0) (hents : ma.entries = []) (hc1 : 1 ≤ (σ.s ma.dest).commitIndex)
    (hmem : ma ∈ σ.messages.domain)
    (hlog : (σ.s ma.dest).log = logAbs C C.length 1 L) (hbL : BootTerms C.length 1 L) (hwL : PlogWf base0 L)
    (hlL : L.length < 2 ^ 63) :
    simFx (GF := GF) γ C σ ∗ logRecs γ base0 L ∗
      (⌜¬ (σ.s ma.dest).commitIndex < ma.commitIndex⌝ ∨
        (⌜(σ.s ma.dest).commitIndex < ma.commitIndex ∧ ma.commitIndex ≤ L.length⌝ ∗
          commitIn γ L (W64 ma.commitIndex) (W64 (σ.s ma.dest).currentTerm) ∗
          isCommitted γ (L.take ma.commitIndex.toNat))) ⊢
      simFx γ C (hbRecvSt σ ma) := by
  have heq := hbRecvSt_eq σ ma
  obtain ⟨W, hW⟩ : ∃ W, W = withNode σ ma.dest (hbSrv (σ.s ma.dest) ma.source ma.commitIndex)
      (fun b => b.without ma) (fun b => b.with (hbResp (σ.s ma.dest) ma.dest ma.source)) := ⟨_, rfl⟩
  rw [heq, ← hW]
  have hWs : ∀ k, W.s k = if k = ma.dest then hbSrv (σ.s ma.dest) ma.source ma.commitIndex else σ.s k := by
    intro k; rw [hW]; rfl
  have hF : ∀ k, (W.s k).log = (σ.s k).log ∧ (W.s k).currentTerm = (σ.s k).currentTerm ∧
      (W.s k).state = (σ.s k).state ∧ (W.s k).config = (σ.s k).config ∧
      (W.s k).commitIndex = (if k = ma.dest then max (σ.s k).commitIndex ma.commitIndex else (σ.s k).commitIndex) := by
    intro k; rw [hWs]
    split
    · rename_i hk; subst hk; simp [hbSrv]
    · simp_all
  have hsub' : ∀ x ∈ W.messages.domain ++ W.pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain ∨ x = hbResp (σ.s ma.dest) ma.dest ma.source := by
    intro x hx
    have hx' : x ∈ ((σ.discard ma).send (hbResp (σ.s ma.dest) ma.dest ma.source)).messages.domain ++
        ((σ.discard ma).send (hbResp (σ.s ma.dest) ma.dest ma.source)).pendingMessages.domain := by
      rw [hW] at hx; exact hx
    rcases TraceSpecInv.mem_msgs_send _ _ x hx' with hx | rfl
    · left
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
      · exact List.mem_append_right _ hx
    · right; rfl
  have hWsrv : W.server = σ.server := by rw [hW]; rfl
  iintro ⟨Hfx, #HL, #Hcert⟩
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hq, hu, hsh, has⟩ := Hp
  -- the receiver's facts
  ihave #Hal1 : allFacts γ C W $$ []
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %k %hk
    by_cases hki : idAbs k = ma.dest
    · ihave #Hk := Hal $$ %k %hk
      rw [hki]
      simp only [hWs, ↓reduceIte]
      iunfold srvFacts at Hk
      icases Hk with ⟨%es, %pend, %Hpk, #Hrec, #Hcm, -, #Hci⟩
      obtain ⟨hlg, hbt, hwr, hln, hc0, hcl, ht0, ht1, hpn, hpt⟩ := Hpk
      have hpend : pend = [] := hpn (by rw [hf]; exact TraceSpecInv.follower_ne_leader)
      subst hpend
      simp only [List.append_nil] at hlg hbt hwr hln
      have hwe : PlogWf base0 es := PlogWfR_wf _ _ hwr (by unfold plogLastIndexZ; rw [base0_index]; omega)
      icases log_eq_of_abs γ C es L hbt hbL (hlg.symm.trans hlog) hwe hwL hlL $$ [$Hrec $HL] with %HeL
      subst HeL
      iunfold srvFacts
      iexists es, []
      simp only [List.append_nil]
      have hst : (hbSrv (σ.s ma.dest) ma.source ma.commitIndex).state ≠ Etcdraft.leader := by
        simp only [hbSrv, hf]; exact TraceSpecInv.follower_ne_leader
      simp only [hst, ↓reduceIte]
      icases Hcert with (%Hle | ⟨%Hcl, #Hci', #Hcm'⟩)
      · have hmx : max (σ.s ma.dest).commitIndex ma.commitIndex = (σ.s ma.dest).commitIndex := by omega
        simp only [hbSrv, hmx]
        iframe Hrec Hcm Hci
        ipureintro
        exact ⟨hlg, hbt, hwr, hln, hc0, hcl, ht0, ht1, fun _ => by simp, fun e he => by simp at he⟩
      · obtain ⟨Hlt', Hcl⟩ := Hcl
        have hmx : max (σ.s ma.dest).commitIndex ma.commitIndex = ma.commitIndex := by omega
        simp only [hbSrv, hmx]
        iframe Hrec Hcm' Hci'
        ipureintro
        exact ⟨hlg, hbt, hwr, hln, by omega, Hcl, ht0, ht1, fun _ => by simp, fun e he => by simp at he⟩
    · simp only [hWs, hki, ↓reduceIte]
      iapply Hal $$ %k %hk
  -- the pure facts
  have hmmem : ma ∈ σ.messages.domain ++ σ.pendingMessages.domain := List.mem_append_left _ hmem
  obtain ⟨hsrcS, -⟩ := hsi.reqCommitC ma hmmem hty
  have hsi' : TraceSpecInv.SpecInv W := by
    rw [hW, ← heq]
    exact TraceSpecInv.specInv_handleAppendEntriesRequest hsi (by rw [hdst, hsrv, mem_confAbs]; exact hiC) hmem rfl
      hty (by rw [hsub]; decide) hpv hcq (handleAER_hb σ ma hf hterm hsub hprev hents hc1) _ (List.mem_singleton_self _)
  icases allFacts_logInv γ C W (by rw [hWsrv, hsrv]) $$ Hal1 with %HlogInv
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %Hco
  -- `QuorumLogInv`'s fact, at the specification's intermediate state (before `withLead`)
  obtain ⟨σ2, hσ2⟩ : ∃ σ2, σ2 = (σ.commitTo ma.dest ma.commitIndex).reply
      (hbResp (σ.s ma.dest) ma.dest ma.source) ma := ⟨_, rfl⟩
  have h2s : ∀ k, (σ2.s k).log = (W.s k).log ∧ (σ2.s k).commitIndex = (W.s k).commitIndex ∧
      (σ2.s k).config = (W.s k).config := by
    intro k
    have : σ2.s k = if k = ma.dest then { σ.s ma.dest with commitIndex := max (σ.s ma.dest).commitIndex ma.commitIndex }
        else σ.s k := by
      rw [hσ2]; unfold Etcdraft.State.reply Etcdraft.State.commitTo Etcdraft.State.upd; simp only
    rw [this, hWs]
    split <;> simp [hbSrv]
  have hcmp : TraceSpecInv.CommittedCmp σ2 ma.dest ma.source := by
    have := HlogInv ma.dest (by rw [hWsrv, hdst, hsrv, mem_confAbs]; exact hiC) ma.source (by rw [hWsrv]; exact hsrcS)
    unfold TraceSpecInv.CommittedCmp
    have hcl : ∀ k, TraceSim.committedL σ2 k = TraceSim.committedL W k := by
      intro k; unfold TraceSim.committedL; rw [(h2s k).1, (h2s k).2.1]
    rw [hcl, hcl]; exact this
  have hq2 : TraceSpecInv.QuorumLogS σ2 := by
    have hstep : σ.appendEntriesAlreadyDone ma.dest ma.source (ma.prevLogIndex + 1) ma = some σ2 := by
      rw [hσ2]; exact alreadyDone_heartbeat σ ma.dest ma.source ma hc1 hsub hprev hents
    exact TraceSpecInv.quorumLog_appendEntriesAlreadyDone hsi hq hmem hty Hco hstep hcmp
  have hqW : QuorumLogF W :=
    quorumLogF_congr σ2 W (by rw [hWsrv, hσ2]; rfl) (fun k => (h2s k).1.symm) (fun k => (h2s k).2.1.symm)
      (fun k => (h2s k).2.2.symm) hq2
  -- uniqueness and shape: after the discard, the response sent
  have hxq : (hbResp (σ.s ma.dest) ma.dest ma.source).type ≠ .appendEntriesRequest := by simp [hbResp]
  have hx0 : canonMsg (hbResp (σ.s ma.dest) ma.dest ma.source) = hbResp (σ.s ma.dest) ma.dest ma.source := by
    unfold hbResp canonMsg; simp
  have hud : MsgsUniq (σ.discard ma) := msgsUniq_mono (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx) hu
  have hshd : MsgsShape (σ.discard ma) := fun x hx => hsh x (by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx)
  obtain ⟨hu', hsh'⟩ := msgsUniq_send_canon (σ.discard ma) _ hud hshd hx0
    (fun y _ => ContentLogged.pinned (fun h => absurd h hxq) y)
  iunfold simFx
  iframe Hal1
  isplitl
  · imodintro
    iintro %x %hx
    rcases hsub' x hx with hx | rfl
    · iapply Hmf; ipureintro; exact hx
    · iapply msgFacts_plain γ C _ hxq rfl
  ipureintro
  refine ⟨hsi', hqW, by rw [hW]; exact hu', by rw [hW]; exact hsh', ?_⟩
  intro m hm hty' k hk hlk htk hs k' e he
  have hk' : k ∈ σ.server := by rw [hWsrv] at hk; exact hk
  rcases hsub' m hm with hm | rfl
  · rw [(hF k).1]
    rw [(hF k).2.2.1] at hlk; rw [(hF k).2.1] at htk
    exact has m hm hty' k hk' hlk htk hs k' e he
  · exact absurd hty' hxq

/-- **A heartbeat's receive line's phase step, at a follower of its term**: the server to `hbSrv`
(the commit raised, the leader adopted), its response `hbResp` added (both read the server through
`toC`, so they are pinned at the pinned server's `a0`). -/
theorem phaseStepR_hb (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .heartbeat m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .follower) (hents : ents = [])
    (hc1 : 1 ≤ uint.Z (toPState s).commit)
    (hb : (absMsg .heartbeat m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .heartbeat m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .heartbeat m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) (hbSrv a0 (idAbs m.From') ma.commitIndex))
        (P0 ++ [hbResp a0 (idAbs id) (idAbs m.From')])) := by
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
  have hc1' : toC (confAbs C) (hbSrv a (idAbs m.From') ma.commitIndex) =
      toC (confAbs C) (hbSrv a0 (idAbs m.From') ma.commitIndex) := by
    have h1 : a.commitIndex = a0.commitIndex := congrArg ServerC.commitIndex hcx
    simp only [toC, hbSrv] at hcx ⊢
    injection hcx with h1' h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    rw [h1]
    congr 1
  have hr1 : hbResp a (idAbs id) (idAbs m.From') = hbResp a0 (idAbs id) (idAbs m.From') := by
    have h1 : a.currentTerm = a0.currentTerm := congrArg ServerC.currentTerm hcx
    unfold hbResp; rw [h1]
  refine ⟨hbSrv a (idAbs m.From') ma.commitIndex, [hbResp a (idAbs id) (idAbs m.From')],
    ⟨rfl, hc1', by rw [hr1]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have := lineEffect_heartbeatRecv C e s c _ a ma (fun _ => False) rfl he' hin hout hC' hR hs hrole hterm hents hc1
    bt bc bl bmc hma
  rw [hsrc] at this
  exact this

/-- **The facts of a heartbeat's receive line, at a follower of its term** (`FxPresR` at
`recvPhantoms m`, none): `simFx_hb` at the pinned phases, given raft's log `L` with its records and the
moved certificates (`ownRaftGhost_hbFacts`). -/
theorem fxPresR_hb (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (L : List EntryM)
    (c0 T : Int) (hiC : id ∈ C0) (hdst : ma.dest = idAbs id) (hty : ma.type = .appendEntriesRequest)
    (hsub : ma.subtype = "heartbeat") (hprev : ma.prevLogIndex = 0) (hents : ma.entries = [])
    (hbL : BootTerms C0.length 1 L) (hwL : PlogWf base0 L) (hlL : L.length < 2 ^ 63)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 → cs1 = toC (confAbs C0) (hbSrv a ma.source ma.commitIndex) ∧
      r1 = hbResp a (idAbs id) ma.source ∧ ma.term = a.currentTerm ∧ a.state = Etcdraft.follower ∧
      1 ≤ a.commitIndex ∧ a.commitIndex = c0 ∧ a.currentTerm = T ∧ a.log = logAbs C0 C0.length 1 L) :
    logRecs (GF := GF) γ base0 L ∗
      (⌜¬ c0 < ma.commitIndex⌝ ∨
        (⌜c0 < ma.commitIndex ∧ ma.commitIndex ≤ L.length⌝ ∗ commitIn γ L (W64 ma.commitIndex) (W64 T) ∗
          isCommitted γ (L.take ma.commitIndex.toNat))) ⊢
      FxPresR (GF := GF) γ id ma E (fun _ => False) (recvPhantoms ma) (IdlePin s C0 cs0 P0)
        (VPin C0 cs1 (P0 ++ [r1])) := by
  iintro ⟨#HL, #Hcert⟩
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hc1, hr1, hle, hfol, hcm1, hc0, hT, hlog⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hle]; exact Int.lt_irrefl _)
  have hσd : σ.s ma.dest = a := by rw [hdst]; exact hσa
  ihave #H1 := simFx_hb γ C σ ma L id hsrv hiC hdst hpv hcq (by rw [hσd]; exact hfol) hty
    (by rw [hσd]; exact hle) hsub hprev hents (by rw [hσd]; exact hcm1) hmem (by rw [hσd]; exact hlog) hbL hwL hlL
    $$ [$Hfx $HL]
  · rw [hσd, hc0, hT]
    iexact Hcert
  rw [hbRecvSt_eq σ ma]
  have hs : ∀ k, toC (withNode σ ma.dest (hbSrv (σ.s ma.dest) ma.source ma.commitIndex) (fun b => b.without ma)
        (fun b => b.with (hbResp (σ.s ma.dest) ma.dest ma.source))).server
      ((withNode σ (idAbs id) a' (fun b => b.without ma)
        (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s k) =
      toC (withNode σ ma.dest (hbSrv (σ.s ma.dest) ma.source ma.commitIndex) (fun b => b.without ma)
        (fun b => b.with (hbResp (σ.s ma.dest) ma.dest ma.source))).server
        ((withNode σ ma.dest (hbSrv (σ.s ma.dest) ma.source ma.commitIndex) (fun b => b.without ma)
          (fun b => b.with (hbResp (σ.s ma.dest) ma.dest ma.source))).s k) := by
    intro k
    show toC σ.server (if k = idAbs id then a' else σ.s k) =
      toC σ.server (if k = ma.dest then hbSrv (σ.s ma.dest) ma.source ma.commitIndex else σ.s k)
    rw [hdst]
    split
    · rw [hsrv, hcs', hc1, ← hdst, hσd]
    · rfl
  ihave #H3 := simFx_congr γ C
    (withNode σ ma.dest (hbSrv (σ.s ma.dest) ma.source ma.commitIndex) (fun b => b.without ma)
      (fun b => b.with (hbResp (σ.s ma.dest) ma.dest ma.source)))
    (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
    rfl rfl (by rw [hph, hr1, hσd, hdst]; rfl) hs $$ H1
  iframe Htbl
  isplitl
  · iexact H3
  · iintro %v %hv
    exact hv.elim

/-- A heartbeat's response's numbers (the node's term). -/
theorem hbresp_nums (id : w64) (s : NState) (m : MessageM) (cl : List w8)
    (hT : uint.Z s.term + 1 < traceNumBound) :
    ({ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl } : Msg).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hT
  unfold Msg.plain Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨by word, by simp, by simp, by simp, by simp, by simp⟩

/-- The send line of a heartbeat's response, skipped by the specification: its gate from the
capability at a pinned phase, with a frame `X` (`skipGate_vresp`'s counterpart). -/
theorem skipGate_hbresp (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s1 : NState) (x : Msg)
    (C0 : List w64) (cs1 : ServerC) (P1 : List Etcdraft.Msg) (X : IProp GF)
    (hty : x.ty = .heartbeatResp) (hne : x.src ≠ x.dst)
    (hOk : ∀ e, (∃ mm ∈ [x], SendEvOf (W64 11) id s1 c mm e) → TraceEv.Ok (elements c.incoming).length e) :
    (X ∗ trCapB (some γd) γ r id c true (VPin C0 cs1 P1) (fun o => o.isSome = true) : IProp GF) ⊢
      HookGateOpt (some γd) r (sendOutGate id s1 c MsgHeartbeatResp [x])
        iprop(X ∗ (trCapB (some γd) γ r id c true (VPin C0 cs1 P1) (fun o => o.isSome = true) ∗ emp)) := by
  have hg : sendOutGate id s1 c MsgHeartbeatResp [x] =
      some (fun e => ∃ mm ∈ [x], SendEvOf (W64 11) id s1 c mm e) := rfl
  rw [hg]
  iintro ⟨HX, Hc⟩
  iapply hookGateOpt_frame
  iframe HX
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  iapply hookGate_opt
  iapply trCapB_hookGate (some γd) γ r id c tl _ true _ _ _ _ iprop(emp)
    (phaseStepB_skip id c s1 (W64 11) x C0 cs1 P1 (.inl rfl) hne (.inr (.inl hty)))
    (fun h => by cases h) (fun _ _ => rfl) (fun _ => hOk) (fun h => by cases h)
  iframe Htl Hc
  simp only [FxPresUT]
  iapply fxPres_upd
  iapply fxPres_skip

/-- **The idle relation after a follower's heartbeat of its term**: raft's end state
(`heartbeatResult`, the commit raised, the leader adopted, the response queued) is related to the
specification's server and pending list after the receive line. -/
theorem hbEnd_simIdle (C : List w64) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM) (cl : List w8)
    (a0 : Etcdraft.Server) (ma : Etcdraft.Msg) (hR : SimServerR C C.length (toPState s) a0)
    (hs : LogShapeOk C.length (toPState s)) (bt : uint.Z s.term < 2 ^ 63)
    (bc : uint.Z s.logst.committed < 2 ^ 63) (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hrole : s.role = .follower) (hmc : uint.Z m.Commit' < 2 ^ 63)
    (hma : TraceSim.msgAbs C C.length (absMsg .heartbeat m ents) = some ma) :
    SimIdle C (heartbeatResult id { s with lead := m.From' } m cl)
      (toC (confAbs C) (hbSrv a0 (idAbs m.From') ma.commitIndex))
      (pendAbs C s.outbox ++ [hbResp a0 (idAbs id) (idAbs m.From')]) := by
  simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
  cases hma
  obtain ⟨hT, hSt, hV, hL, hB, hLog, hCm, hCfg, hPc, -, -⟩ := hR
  have hcm : uint.Z (plogCommitTo s.logst.committed m.Commit') =
      max (uint.Z s.logst.committed) (uint.Z m.Commit') := by
    unfold plogCommitTo; split <;> omega
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hbSrv]; rw [hT]; rfl
    · simp only [hbSrv]; rw [hSt]; simp [toPState, heartbeatResult, sendMsgs, hrole]
    · simp only [hbSrv]; rw [hV]; rfl
    · simp [hbSrv, toPState, heartbeatResult, sendMsgs, hrole]
    · exact hB
    · simp only [hbSrv]; rw [hLog]; rfl
    · simp only [hbSrv]; rw [hCm]; show _ = uint.Z (plogCommitTo s.logst.committed m.Commit'); rw [hcm]; rfl
    · exact hCfg
    · exact hPc
    · intro h; simp [toPState, heartbeatResult, sendMsgs, hrole, proleRole] at h
    · intro h; simp [toPState, heartbeatResult, sendMsgs, hrole, proleRole] at h
  · exact hs
  · show _ = pendAbs C (s.outbox ++ _)
    rw [pendAbs_append]
    simp [pendAbs, TraceSim.msgAbs, Msg.plain, hbResp, hT, toPState]
  · exact bt
  · show uint.Z (plogCommitTo s.logst.committed m.Commit') < 2 ^ 63
    rw [hcm]; omega
  · exact bl

end hb

end EtcdGrove
end Perennial
