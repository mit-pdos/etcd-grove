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
      ownRaftGhost γ id s md ∗ ⌜(γ.reBoot.length : Int) ≤ uint.Z s.commit⌝ ∗ logRecs γ base0 s.log ∗
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
  icases persistent_entails_right (wand_entails (ownLogGhost_boot (GF := GF) γ id s kl (virt V πc))) $$ Hlg
    with ⟨⟨%Hbt, -⟩, Hlg⟩
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
      isplitr; · ipureintro; exact Hbt.1
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
      isplitr; · ipureintro; exact Hbt.1
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
    isplitr; · ipureintro; exact Hbt.1
    iframe Hrecs
    ileft; ipureintro; exact Hlt

/-- **A recorded log is determined by its abstraction** (with the bootstrap positions' terms):
two logs with records whose abstractions (`logAbs`, which keeps the terms past the bootstrap
positions) agree are equal (`full_take_eq` at their last index). -/
theorem log_eq_of_abs (γ : RaftNames) (C : List w64) (es L : List EntryM)
    (hb1 : BootTerms C.length 1 es) (hb2 : BootTerms C.length 1 L)
    (habs : logAbs C C.length 1 es = logAbs C C.length 1 L)
    (hw1 : PlogWf base0 es) (hw2 : PlogWf base0 L) (hl1 : es.length < 2 ^ 63) :
    logRecs (GF := GF) γ base0 es ∗ logRecs γ base0 L ⊢ ⌜es = L⌝ := by
  have hlen : es.length = L.length := by
    have := congrArg List.length habs; simpa [logAbs_length] using this
  have hl : L.length < 2 ^ 63 := by omega
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
    (hlog : (σ.s ma.dest).log = logAbs C C.length 1 L) (hbL : BootTerms C.length 1 L) (hwL : PlogWf base0 L) :
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
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
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
      icases log_eq_of_abs γ C es L hbt hbL (hlg.symm.trans hlog) hwe hwL hln $$ [$Hrec $HL] with %HeL
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
  obtain ⟨hsrcS, hcS⟩ := hsi.reqCommitC ma hmmem hty
  have hsi' : TraceSpecInv.SpecInv W := by
    rw [hW, ← heq]
    exact TraceSpecInv.specInv_handleAppendEntriesRequest hsi (by rw [hdst, hsrv, mem_confAbs]; exact hiC) hmem rfl
      hty (by rw [hsub]; decide) hpv hcq (handleAER_hb σ ma hf hterm hsub hprev hents hc1) _ (List.mem_singleton_self _)
  icases allFacts_logInv γ C W (by rw [hWsrv, hsrv]) $$ Hal1 with %HlogInv
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %Hco
  -- `QuorumLogInv`'s fact (amendment A5): the receiver's raised committed prefix is a prefix of the
  -- sender's, whose witness it takes (`committedL_raise_prefix`)
  have hcmp := HlogInv ma.dest (by rw [hWsrv, hdst, hsrv, mem_confAbs]; exact hiC) ma.source
    (by rw [hWsrv]; exact hsrcS)
  have hPW : ∀ k ∈ σ.server, ∃ k' ∈ σ.server, committedL W k <+: committedL σ k' := by
    intro k hk
    by_cases hkd : k = ma.dest
    · subst hkd
      rcases committedL_raise_prefix (σ := σ) (W := W) (src := ma.source) (c := ma.commitIndex)
          (hF _).1 (by rw [(hF _).2.2.2.2, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
          (fun k hk => by unfold committedL; rw [(hF k).1, (hF k).2.2.2.2, ite_eq_right_of_eq_false _ _ (eq_false hk)])
          hcS (Hco ma.source hsrcS).2 hcmp with h | h
      · exact ⟨_, hk, h⟩
      · exact ⟨ma.source, hsrcS, h⟩
    · exact ⟨k, hk, by unfold committedL; rw [(hF k).1, (hF k).2.2.2.2, ite_eq_right_of_eq_false _ _ (eq_false hkd)]; exact List.prefix_refl _⟩
  -- uniqueness and shape: after the discard, the response sent
  have hxq : (hbResp (σ.s ma.dest) ma.dest ma.source).type ≠ .appendEntriesRequest := by simp [hbResp]
  have hx0 : canonMsg (hbResp (σ.s ma.dest) ma.dest ma.source) = hbResp (σ.s ma.dest) ma.dest ma.source := by
    unfold hbResp canonMsg; simp
  have hud : MsgsUniq (σ.discard ma) := msgsUniq_mono (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx) hu
  have hshd : MsgsShape (σ.discard ma) := msgsShape_of (σ := σ) rfl (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx) (fun _ => rfl) hsh
  -- (amendment A6, Q23) the response's ends, the heartbeat's reversed
  have hme := (hsh.1 ma (List.mem_append_left _ hmem)).2
  obtain ⟨hu', hsh'⟩ := msgsUniq_send_canon (σ.discard ma) _ hud hshd hx0
    ⟨by unfold hbResp; exact hme.2, by unfold hbResp; exact hme.1⟩
    (fun y _ => ContentLogged.pinned (fun h => absurd h hxq) y)
  iunfold simFx
  iframe Hal1
  isplitl
  · imodintro
    iintro %x %hx
    rcases hsub' x hx with hx | rfl
    · iapply Hmf; ipureintro; exact hx
    · iapply msgFacts_plain γ C _ hxq rfl
  isplitl
  · iapply quorumLogF_mono γ C σ W hWsrv hPW ?_ ?_ ?_
      (fun k T m => ackHist_congr γ C σ W k T m (hF k).1 (by rw [(hF k).2.1]; exact Int.le_refl _)) $$ Hq
    · intro P t h
      exact keptFrom_congr hWsrv (fun k => (hF k).1) (fun k => by rw [(hF k).2.1]; exact Int.le_refl _) h
    · intro x hx hxa
      rcases hsub' x hx with hx | rfl
      · exact hx
      · exact absurd hxa.2.2.2 (by simp [hbResp])
    · rw [hW]
      exact withNode_leaders σ ma.dest _ _ _ (fun hl => absurd hl (by simp [hbSrv, hf]; decide))
  ipureintro
  refine ⟨hsi', by rw [hW]; exact hu', by rw [hW]; exact msgsShape_of (σ := (σ.discard ma).send (hbResp (σ.s ma.dest) ma.dest ma.source)) rfl (fun x hx => hx) (fun j => by show Etcdraft.Server.votesResponded (if j = _ then _ else _) = _; split <;> (try subst_vars) <;> rfl) hsh', ?_⟩
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
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC, -, -⟩ e he
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
    (hbL : BootTerms C0.length 1 L) (hwL : PlogWf base0 L)
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
    (by rw [hσd]; exact hle) hsub hprev hents (by rw [hσd]; exact hcm1) hmem (by rw [hσd]; exact hlog) hbL hwL
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

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A heartbeat is none of the other types a gate guards on. -/
theorem hb_ne {t : w32} (h : t = MsgHeartbeat) :
    t ≠ MsgApp ∧ t ≠ MsgVote ∧ t ≠ MsgProp ∧ t ≠ MsgReadIndex ∧ t ≠ MsgTransferLeader ∧
    t ≠ MsgTimeoutNow ∧ t ≠ MsgBeat ∧ t ≠ MsgCheckQuorum ∧ t ≠ MsgPreVoteResp ∧ t ≠ MsgVoteResp ∧
    t ≠ MsgHeartbeatResp ∧ t ≠ MsgAppResp ∧ t ≠ MsgPreVote ∧ t ≠ MsgHup ∧ t ≠ MsgSnap := by
  subst h
  simp [MsgAppResp, MsgHeartbeatResp, MsgVoteResp, MsgApp, MsgHeartbeat, MsgProp, MsgReadIndex,
    MsgTransferLeader, MsgTimeoutNow, MsgBeat, MsgCheckQuorum, MsgPreVoteResp, MsgVote, MsgPreVote, MsgHup,
    MsgSnap]

/-- **A heartbeat of the node's term at a follower.** -/
def FolHb (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgHeartbeat ∧ m.Term' = s.term ∧ s.role = .follower

/-- **`raft.Step`'s traced bundle on a heartbeat of the node's term at a follower**: the receive line
(the specification's heartbeat handling, the commit raised with the certificates the heartbeat's raft
facts give, `ownRaftGhost_hbFacts`), then the response's send line, which the specification skips; the
end state is `heartbeatResult`'s (`hbEnd_simIdle`). The resources are `voteR`'s (one pinned phase after
the receive line). -/
theorem stepBundle_traced_folHb : stepBundle_traced.on (GF := GF) (hG := hG) FolHb := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole⟩ := hp
  have hmty : mtypeOf m.Type' = some .heartbeat := by rw [hTy]; rfl
  have htrd : MsgType.traced .heartbeat = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .heartbeat m ents hmty htrd hsh
  have hto' : m.To' = id := hto .heartbeat hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2.1 (.inr (.inr hTy)) (by rw [hto', h])
  have hents : ents = [] := hsh.1 hTy
  have hb0 : γ.reBoot ≠ [] := hboot (.inl hTy)
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hnl : s.role ≠ .leader := by rw [hrole]; nofun
  obtain ⟨hnA, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := hb_ne hTy
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
  imodintro
  iexists voteR bfl γ md c r id s γd tn cs0 (toC (confAbs tn.voters) (hbSrv a0 (idAbs m.From') ma.commitIndex)) P0
    (P0 ++ [hbResp a0 (idAbs id) (idAbs m.From')]) Λ k ma
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
      have hps := phaseStepR_hb id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole hents hc1 hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .heartbeat m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .heartbeat evt bfl k ma (fun _ => False)
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · iapply fxPresR_hb γ id ma _ s tn.voters cs0 _ P0 _ (toPState s).log (uint.Z s.logst.committed)
          (uint.Z s.term) hidC hmd hmty' hmsub hmprev hments hbL hwB
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          refine ⟨?_, ?_, ?_, ?_, ?_, hRa.2.2.2.2.2.2.1, hRa.1, hRa.2.2.2.2.2.1⟩
          · rw [hms]
            have h1 : a0.commitIndex = a.commitIndex := congrArg ServerC.commitIndex hcx
            simp only [toC, hbSrv] at hcx ⊢
            injection hcx with h1' h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
            rw [h1]
            congr 1
          · rw [hms]
            have h1 : a0.currentTerm = a.currentTerm := congrArg ServerC.currentTerm hcx
            unfold hbResp; rw [h1]
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
      · iintro %_
        iunfold followerGates
        isplitr
        · iguard_false [hnA]
        isplitr
        · -- the response's send line, skipped by the specification
          iintro %_ ⟨Hgh, Hc⟩
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
          iapply skipGate_hbresp γd γ r id c _ { Msg.plain .heartbeatResp id m.From' s.term false with ctx := ctx }
            tn.voters _ _ (ownStepGhost γ md c id s) rfl (by simp only [Msg.plain]; exact hne)
            (fun e ⟨mm, hmm, he⟩ => by
              simp only [List.mem_singleton] at hmm; subst hmm
              exact sendEvOf_ok _ id _ c _ e _ he (by decide) (by word) hcm Hb.1 hn (Nat.le_refl _))
          iframe Hgh Hc
        repeat (isplitr; · iguard_false [hnP, hnRI, hnTL, hnTN])
        iguard_false [hnTN]
      isplit
      · iintro %h; exfalso; rw [hrole] at h; rcases h with h | h <;> cases h
      · iintro %h; exfalso; rw [hrole] at h; cases h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's heartbeat handling, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend %_ Hout
    have hse : s' = heartbeatResult id { s with lead := m.From' } m ctx := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.1 hrole
      unfold FollowerStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [hTy] at hf
      simp [MsgVoteResp, MsgProp, MsgApp, MsgHeartbeat] at hf
      exact hf.2
    subst hse
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) (hbSrv a0 (idAbs m.From') ma.commitIndex))
        (P0 ++ [hbResp a0 (idAbs id) (idAbs m.From')]) C cs P →
        SimIdle C (heartbeatResult id { s with lead := m.From' } m ctx) cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hnb := (hok .heartbeat hmty hre htrd).1
      have hmc63 : uint.Z m.Commit' < 2 ^ 63 := (numsBelow_63 hnb).2.2.2.2
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0']
      exact hbEnd_simIdle tn.voters id s m ents ctx a0 ma hR0 hs0 bt bc bl hrole hmc63 hma
    have hout : OutTrStep s (heartbeatResult id { s with lead := m.From' } m ctx) := by
      intro _ x hx
      simp only [heartbeatResult, sendMsgs, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact .inl hx
      · exact .inr (Msg.trOk_of_nums_hbresp rfl rfl (fun _ => hbresp_nums id s m ctx hT))
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
      · ipureintro; exact hout

end paths

end EtcdGrove
end Perennial
