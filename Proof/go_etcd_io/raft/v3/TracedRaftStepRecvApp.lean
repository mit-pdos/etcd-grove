/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a follower's `MsgApp` of its term**
(2026-11-10, trace-check Q8 stage 1 slice 20b, `notes/decisions.md`, "Q8 stage 1 (slice 20b)").

Raft's `handleAppendEntries` has three exits (`HandleAppResult`), decided by the node's state and the
message: below the commit index (*stale*: the commit index acknowledged, the log not read), a
matching previous entry (*accepted*: `maybeAppend`), or not (*rejected*). The specification's receive
line takes the same one (`lineEffect_staleRecv`, `lineEffect_appRecv`, `lineEffect_rejectRecv`), and
the response's send line is skipped by the specification (`phaseStepB_skip`).

This file: the stale exit. The specification's `AppendEntriesAlreadyDone` needs the log to match at the
request's previous entry (`hmt0`), which raft does not check: it holds by log matching below the commit
index (`ownRaftGhost_appStaleMatch`: the follower's commit certificate, the leader's full log reaching
the commit index, `commitIn_ackInF`, and `commit_in_leader`, with the vote table of raft's commit
invariant).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvCand

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **Log matching below the commit index, for a stale append request**: a follower's log, at the
request's term, has the request's previous entry when it is below its commit index (raft's
`appStale` does not look; the leader's full log reaches the follower's commit index, `commitIn_ackInF`,
and agrees with the follower's log up to it, `commit_in_leader`). The ghost state is unchanged. -/
theorem ownRaftGhost_appStaleMatch (γ : RaftNames) (id : w64) (s : PState) (m : Msg) {md : Bool} :
    m.ty = .app → uint.Z s.term ≤ uint.Z m.term → s.base = base0 → PlogWf base0 s.log →
    uint.Z m.index < uint.Z s.commit →
    ⊢ isMessage (GF := GF) γ m -∗ ownRaftGhost γ id s md ={⊤}=∗
      ownRaftGhost γ id s md ∗ ⌜plogTermAt base0 s.log m.index = some m.logterm⌝ := by
  intro Hty Hle Hbase Hw Hlt
  iintro #Hm Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  ihave #HcI := ownLogGhost_commitIn γ id s kl (virt V πc) $$ Hlg
  icases HcI with ⟨%fpw, %Hfo, #Hfr, #Hr, #Hcom⟩
  obtain ⟨Hfull, Hlok⟩ := Hfo
  have hfp : fpw = [] := by
    have h := Hfull.1; rw [Hbase, base0_index] at h
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hfp
  have Hcl : uint.Z s.commit ≤ s.log.length := by
    have h := Hlok.2.2; rw [Hbase] at h; unfold plogLastIndexZ at h; rw [base0_index] at h; simpa using h
  ihave #Hinv := ownLogGhost_inv γ id s kl (virt V πc) $$ Hlg
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  icases isMessage_app_inv γ m Hty $$ Hm with ⟨-, -, ⟨%bL, %l, %fpL, #HlpL, %HlL, #HlfL, -, -, -⟩, -⟩
  ihave #HlfL0 := HlfL
  iunfold lpfull at HlfL0
  icases HlfL0 with ⟨%F0, -, -, %HfL⟩
  have HfullL : plogTermAt base0 (fpL ++ l) m.index = some m.logterm := by
    have hr := plogTermAt_some_range _ _ _ _ HlL.1
    rw [full_term_at _ _ _ _ HfL.1 hr.1]; exact HlL.1
  simp only [List.nil_append]
  rw [Hbase]
  unfold raftLogInv raftLogInvBody
  iinv Hli with ⟨%P, HP, Hjust, >Htbl, Hwt, Hpo⟩ Hclose
  icases commitIn_ackInF γ m.src m.term bL l fpL s.log s.commit s.term Hle
    $$ Htbl HlpL HlfL Hcom with ⟨Htbl, #HackInF⟩
  iunfold ackInF at HackInF
  have hnn := uint_Z_nonneg m.index
  icases HackInF with (%H0 | ⟨%X, #HX, %HXl⟩)
  · exfalso; omega
  have HXlen : plogLastIndexZ base0 X = X.length := by unfold plogLastIndexZ; rw [base0_index]; simp
  icases persistent_entails_right (commit_in_leader γ s.log X s.commit s.term m.term Hw Hcl Hle
      (fun _ => by rw [← HXlen]; exact HXl)) $$ [$Htbl $Hr $Hcom $HX] with ⟨%Hag, Htbl, -⟩
  imod Hclose $$ [HP Hjust Htbl Hpo Hwt] with -
  · inext
    iexists P
    iframe
  ihave #HLm : leadFull γ m.term (fpL ++ l) $$ []
  · iunfold leadFull; iexists m.src, bL, l, fpL; iframe HlpL HlfL; ipureintro; rfl
  ihave %HXL := leadFull_agree γ m.term X (fpL ++ l) m.index
    (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact hnn, by omega⟩) (by rw [HfullL]; rfl) $$ HX HLm
  imodintro
  isplitl
  · iunfold ownRaftGhost
    iexists γs, V, πc, kl
    iframe Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd
    ipureintro; exact ⟨Hsname, Hfresh, Hidnz, Hhist, Hlead_ok, Hfollower_votes, Hrole_ok, Hmode⟩
  ipureintro
  rw [← Hag m.index (by omega), HXL, HfullL]

end ghost

section pure
variable [GooseExts]

/-- `toC` of a server with its leader set, from `toC` of the server. -/
theorem toC_lead (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (j : Etcdraft.ID) (h : toC S x = toC S y) :
    toC S { x with lead := j } = toC S { y with lead := j } := by
  simp only [toC] at h ⊢
  injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12]

/-- A stale append request's response reads the receiver's term and commit index only. -/
theorem stResp_toC (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (i j : Etcdraft.ID) (sub : String)
    (h : toC S x = toC S y) : stResp x i j sub = stResp y i j sub := by
  have h1 : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  have h2 : x.commitIndex = y.commitIndex := congrArg ServerC.commitIndex h
  unfold stResp; rw [h1, h2]

/-- A rejected append request's response reads the receiver's term only. -/
theorem rjResp_toC (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (i j : Etcdraft.ID)
    (h : toC S x = toC S y) : rjResp x i j = rjResp y i j := by
  have h1 : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  unfold rjResp; rw [h1]

theorem staleRecvSt_eq (σ : Etcdraft.State) (ma : Etcdraft.Msg) (hsub : ma.subtype = "app") :
    staleRecvSt σ ma = withNode σ ma.dest { σ.s ma.dest with lead := ma.source } (fun b => b.without ma)
      (fun b => b.with (stResp (σ.s ma.dest) ma.dest ma.source "app")) := by
  unfold staleRecvSt
  rw [hsub]
  exact withLead_reply σ ma.dest ma.source (stResp (σ.s ma.dest) ma.dest ma.source "app") ma

/-- The specification's handling of a stale append request at a follower of its term
(`receive_appStale`'s). -/
theorem handleAER_stale (σ : Etcdraft.State) (ma : Etcdraft.Msg) (hf : (σ.s ma.dest).state = Etcdraft.follower)
    (hterm : ma.term = (σ.s ma.dest).currentTerm) (hsub : ma.subtype = "app")
    (hidx : ma.prevLogIndex + 1 ≤ (σ.s ma.dest).commitIndex) (hlok : LogOkL ma (σ.s ma.dest).log = true) :
    σ.handleAppendEntriesRequest ma.dest ma.source ma = .ok [staleRecvSt σ ma] := by
  apply handleAER_accept σ ma.dest ma.source ma _ hf hterm (by unfold LogOkL at hlok; exact hlok)
    (by rw [hsub]; decide) none none
  · unfold Etcdraft.State.conflictAppendEntriesRequest
    have : ¬ (ma.prevLogIndex + 1 > (σ.s ma.dest).commitIndex) := by omega
    simp [this, Pure.pure, Except.pure]
  · unfold Etcdraft.State.noConflictAppendEntriesRequest
    have : ¬ (ma.prevLogIndex + 1 > (σ.s ma.dest).commitIndex) := by omega
    simp [this, Pure.pure, Except.pure]
  · rw [alreadyDone_stale σ ma.dest ma.source ma _ hidx (by rw [hsub]; decide)]
    rfl

/-- One message queued: the state and the message are determined. -/
theorem sendMsgs_one_inj {s1 s0 : NState} {a b : Msg} (h : sendMsgs s1 [a] = sendMsgs s0 [b]) :
    s1 = s0 ∧ a = b := by
  have ho := congrArg NState.outbox h
  simp only [sendMsgs] at ho
  obtain ⟨h1, h2⟩ := List.append_inj' ho rfl
  refine ⟨?_, by simpa using h2⟩
  have e1 : s1 = { sendMsgs s1 [a] with outbox := s1.outbox } := rfl
  have e0 : s0 = { sendMsgs s0 [b] with outbox := s0.outbox } := rfl
  rw [e1, e0, h, h1]

end pure

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A receipt that adopts the leader and replies keeps the facts** (the stale and the rejected
append request's handling): the receiver's leader set, the request consumed, a canonical reply that is
not an append request sent; `SpecInv` the handler's (`hsi'`). -/
theorem simFx_leadReply (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (ma r : Etcdraft.Msg)
    (i j : Etcdraft.ID)
    (hsi' : TraceSpecInv.SpecInv σ → TraceSpecInv.SpecInv
      (withNode σ i { σ.s i with lead := j } (fun b => b.without ma) (fun b => b.with r)))
    (hrq : r.type ≠ .appendEntriesRequest) (hre : r.entries = []) (hr0 : canonMsg r = r) :
    simFx (GF := GF) γ C σ ⊢
      simFx γ C (withNode σ i { σ.s i with lead := j } (fun b => b.without ma) (fun b => b.with r)) := by
  obtain ⟨W, hW⟩ : ∃ W, W = withNode σ i { σ.s i with lead := j } (fun b => b.without ma)
      (fun b => b.with r) := ⟨_, rfl⟩
  rw [← hW]; rw [← hW] at hsi'
  have hWs : ∀ k, W.s k = if k = i then { σ.s i with lead := j } else σ.s k := by intro k; rw [hW]; rfl
  have hF : ∀ k, (W.s k).log = (σ.s k).log ∧ (W.s k).currentTerm = (σ.s k).currentTerm ∧
      (W.s k).state = (σ.s k).state ∧ (W.s k).config = (σ.s k).config ∧
      (W.s k).commitIndex = (σ.s k).commitIndex := by
    intro k; rw [hWs]; split
    · rename_i hk; subst hk; simp
    · simp
  have hsub' : ∀ x ∈ W.messages.domain ++ W.pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain ∨ x = r := by
    intro x hx
    have hx' : x ∈ ((σ.discard ma).send r).messages.domain ++
        ((σ.discard ma).send r).pendingMessages.domain := by
      rw [hW] at hx; exact hx
    rcases TraceSpecInv.mem_msgs_send _ _ x hx' with hx | rfl
    · left
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
      · exact List.mem_append_right _ hx
    · right; rfl
  have hWsrv : W.server = σ.server := by rw [hW]; rfl
  iintro Hfx
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hq, hu, hsh, has⟩ := Hp
  have hud : MsgsUniq (σ.discard ma) := msgsUniq_mono (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx) hu
  have hshd : MsgsShape (σ.discard ma) := fun x hx => hsh x (by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx)
  obtain ⟨hu', hsh'⟩ := msgsUniq_send_canon (σ.discard ma) _ hud hshd hr0
    (fun y _ => ContentLogged.pinned (fun h => absurd h hrq) y)
  iunfold simFx
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %k %hk
    iapply srvFacts_congr γ C k _ _ (hF _).1 (hF _).2.2.2.2 (hF _).2.1 (hF _).2.2.1
    iapply Hal $$ %k %hk
  isplitl
  · imodintro
    iintro %x %hx
    rcases hsub' x hx with hx | rfl
    · iapply Hmf; ipureintro; exact hx
    · iapply msgFacts_plain γ C _ hrq hre
  ipureintro
  refine ⟨hsi' hsi, quorumLogF_congr σ W hWsrv (fun k => (hF k).1) (fun k => (hF k).2.2.2.2)
    (fun k => (hF k).2.2.2.1) hq, by rw [hW]; exact hu', by rw [hW]; exact hsh', ?_⟩
  intro m hm hty' k hk hlk htk hs k' e he
  have hk' : k ∈ σ.server := by rw [hWsrv] at hk; exact hk
  rcases hsub' m hm with hm | rfl
  · rw [(hF k).1]
    rw [(hF k).2.2.1] at hlk; rw [(hF k).2.1] at htk
    exact has m hm hty' k hk' hlk htk hs k' e he
  · exact absurd hty' hrq

/-- **The facts of a receive line that adopts the leader and replies** (`FxPresR` at `recvPhantoms m`,
none: the message not of a lower term), from `simFx_leadReply` at the pinned phases. -/
theorem fxPresR_leadReply (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg)
    (R : Etcdraft.Server → Etcdraft.Msg) (hdst : ma.dest = idAbs id)
    (hrq : ∀ a, (R a).type ≠ .appendEntriesRequest) (hre : ∀ a, (R a).entries = [])
    (hr0 : ∀ a, canonMsg (R a) = R a)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      cs1 = toC (confAbs C0) { a with lead := ma.source } ∧ r1 = R a ∧ ¬ ma.term < a.currentTerm)
    (hspec : ∀ σ : Etcdraft.State, σ.server = confAbs C0 → σ.preVote = false → σ.checkQuorum = false →
      ma ∈ σ.messages.domain → toC (confAbs C0) (σ.s ma.dest) = cs0 → TraceSpecInv.SpecInv σ →
      TraceSpecInv.SpecInv (withNode σ ma.dest { σ.s ma.dest with lead := ma.source } (fun b => b.without ma)
        (fun b => b.with (R (σ.s ma.dest))))) :
    ⊢ FxPresR (GF := GF) γ id ma E (fun _ => False) (recvPhantoms ma) (IdlePin s C0 cs0 P0)
        (VPin C0 cs1 (P0 ++ [r1])) := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hc1, hr1, hnl⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a hnl
  have hσd : σ.s ma.dest = a := by rw [hdst]; exact hσa
  ihave #H1 := simFx_leadReply γ C σ ma (R (σ.s ma.dest)) ma.dest ma.source
    (hspec σ hsrv hpv hcq hmem (by rw [hσd]; exact hcs)) (hrq _) (hre _) (hr0 _) $$ Hfx
  iframe Htbl
  isplitl
  · iapply simFx_congr γ C (withNode σ ma.dest { σ.s ma.dest with lead := ma.source } (fun b => b.without ma)
        (fun b => b.with (R (σ.s ma.dest))))
      (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
      rfl rfl (by rw [hph, hr1, hσd]; rfl)
    · intro k
      show toC σ.server (if k = idAbs id then a' else σ.s k) =
        toC σ.server (if k = ma.dest then { σ.s ma.dest with lead := ma.source } else σ.s k)
      rw [hdst]
      split
      · rw [hsrv, hcs', hc1, ← hdst, hσd]
      · rfl
    iexact H1
  · iintro %v %hv
    exact hv.elim

/-- **A stale append request's receive line's phase step, at a follower of its term** (raft's
`appStale`: the specification's `AppendEntriesAlreadyDone`, the log matching at the previous entry,
`hmt0`): the leader adopted, the response `stResp` (the commit index) added. -/
theorem phaseStepR_appStale (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .app m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .follower)
    (hst : uint.Z m.Index' < uint.Z (toPState s).commit)
    (hmt0 : PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))))
    (hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0)
    (hb : (absMsg .app m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .app m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .app m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) { a0 with lead := idAbs m.From' })
        (P0 ++ [stResp a0 (idAbs id) (idAbs m.From') "app"])) := by
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
  refine ⟨{ a with lead := idAbs m.From' }, [stResp a (idAbs id) (idAbs m.From') "app"],
    ⟨rfl, toC_lead _ _ _ _ hcx, by rw [stResp_toC _ _ _ _ _ _ hcx]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have := lineEffect_staleRecv C e s c _ a ma (fun _ => False) rfl he' hin hout hC' hR hs hrole hterm hst
    hmt0 hlt0 bt bc bl bmc bi blt bk hma
  rw [hsrc] at this
  exact this

/-- The send line of an append response, skipped by the specification (`skipGate_hbresp`'s
counterpart). -/
theorem skipGate_appresp (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s1 : NState) (x : Msg)
    (C0 : List w64) (cs1 : ServerC) (P1 : List Etcdraft.Msg) (X : IProp GF)
    (hty : x.ty = .appResp) (hne : x.src ≠ x.dst)
    (hOk : ∀ e, (∃ mm ∈ [x], SendEvOf (W64 11) id s1 c mm e) → TraceEv.Ok (elements c.incoming).length e) :
    (X ∗ trCapB (some γd) γ r id c true (VPin C0 cs1 P1) (fun o => o.isSome = true) : IProp GF) ⊢
      HookGateOpt (some γd) r (sendOutGate id s1 c MsgAppResp [x])
        iprop(X ∗ (trCapB (some γd) γ r id c true (VPin C0 cs1 P1) (fun o => o.isSome = true) ∗ emp)) := by
  have hg : sendOutGate id s1 c MsgAppResp [x] =
      some (fun e => ∃ mm ∈ [x], SendEvOf (W64 11) id s1 c mm e) := rfl
  rw [hg]
  iintro ⟨HX, Hc⟩
  iapply hookGateOpt_frame
  iframe HX
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  iapply hookGate_opt
  iapply trCapB_hookGate (some γd) γ r id c tl _ true _ _ _ _ iprop(emp)
    (phaseStepB_skip id c s1 (W64 11) x C0 cs1 P1 (.inl rfl) hne (.inl hty))
    (fun h => by cases h) (fun _ _ => rfl) (fun _ => hOk) (fun h => by cases h)
  iframe Htl Hc
  simp only [FxPresUT]
  iapply fxPres_upd
  iapply fxPres_skip

/-- A stale append request's response's numbers (the node's term and commit index). -/
theorem appResp_nums (id : w64) (s : NState) (dst idx : w64) (hT : uint.Z s.term + 1 < traceNumBound)
    (hidx : uint.nat idx < traceNumBound) :
    (appResp id s dst false idx (W64 0) (W64 0)).NumsBelow traceNumBound := by
  have hb : traceNumBound = 2 ^ 61 := rfl
  rw [hb] at hT hidx
  unfold appResp Msg.NumsBelow
  dsimp only
  rw [hb]
  refine ⟨by word, by simp, by simp, hidx, by simp, by simp⟩

/-- **The idle relation after a stale append request at a follower of its term**: raft's end state
(the leader adopted, the commit index acknowledged) is related to the specification's. -/
theorem staleEnd_simIdle (C : List w64) (id : w64) (s : NState) (m : MessageM) (a0 : Etcdraft.Server)
    (hR : SimServerR C C.length (toPState s) a0) (hs : LogShapeOk C.length (toPState s))
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (hrole : s.role = .follower) :
    SimIdle C (sendMsgs { s with lead := m.From' }
        [appResp id { s with lead := m.From' } m.From' false s.logst.committed (W64 0) (W64 0)])
      (toC (confAbs C) { a0 with lead := idAbs m.From' })
      (pendAbs C s.outbox ++ [stResp a0 (idAbs id) (idAbs m.From') "app"]) := by
  obtain ⟨hT, hSt, hV, hL, hB, hLog, hCm, hCfg, hPc, -, -⟩ := hR
  refine ⟨_, rfl, ?_, hs, ?_, bt, bc, bl⟩
  · refine ⟨hT, ?_, hV, ?_, hB, hLog, hCm, hCfg, hPc, ?_, ?_⟩
    · rw [hSt]; simp [toPState, sendMsgs, hrole]
    · simp [toPState, sendMsgs, hrole]
    · intro h; simp [toPState, sendMsgs, hrole, proleRole] at h
    · intro h; simp [toPState, sendMsgs, hrole, proleRole] at h
  · show _ = pendAbs C (s.outbox ++ _)
    rw [pendAbs_append]
    simp [pendAbs, TraceSim.msgAbs, appResp, stResp, hT, hCm, toPState]

end fx

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- An append request is none of the other types a gate guards on. -/
theorem app_ne {t : w32} (h : t = MsgApp) :
    t ≠ MsgHeartbeat ∧ t ≠ MsgVote ∧ t ≠ MsgProp ∧ t ≠ MsgReadIndex ∧ t ≠ MsgTransferLeader ∧
    t ≠ MsgTimeoutNow ∧ t ≠ MsgBeat ∧ t ≠ MsgCheckQuorum ∧ t ≠ MsgPreVoteResp ∧ t ≠ MsgVoteResp ∧
    t ≠ MsgHeartbeatResp ∧ t ≠ MsgAppResp ∧ t ≠ MsgPreVote ∧ t ≠ MsgHup ∧ t ≠ MsgSnap := by
  subst h
  simp [MsgAppResp, MsgHeartbeatResp, MsgVoteResp, MsgApp, MsgHeartbeat, MsgProp, MsgReadIndex,
    MsgTransferLeader, MsgTimeoutNow, MsgBeat, MsgCheckQuorum, MsgPreVoteResp, MsgVote, MsgPreVote, MsgHup,
    MsgSnap]

/-- **A stale append request of the node's term at a follower** (its index below the commit index). -/
def FolAppStale (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgApp ∧ m.Term' = s.term ∧ s.role = .follower ∧ uint.Z m.Index' < uint.Z s.logst.committed

/-- **`raft.Step`'s traced bundle on a stale append request of the node's term at a follower**: the
receive line (the specification's `AppendEntriesAlreadyDone`, the log matching below the commit index,
`ownRaftGhost_appStaleMatch`), then the response's send line, which the specification skips. The
resources are `voteR`'s. -/
theorem stepBundle_traced_folAppStale : stepBundle_traced.on (GF := GF) (hG := hG) FolAppStale := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hstl⟩ := hp
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
  imodintro
  iexists voteR bfl γ md c r id s γd tn cs0 (toC (confAbs tn.voters) { a0 with lead := idAbs m.From' }) P0
    (P0 ++ [stResp a0 (idAbs id) (idAbs m.From') "app"]) Λ k ma
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
      imod ownRaftGhost_appStaleMatch γ id (toPState s) (absMsg .app m ents ctx) rfl
        (by show uint.Z s.term ≤ uint.Z m.Term'; rw [hterm]; exact Int.le_refl _) hs0.1 hwB hstl $$ Hm Hg with ⟨Hg, %Hmt0⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .app m ents).NumsBelow traceNumBound := hok .app hmty hreT htrd
      have hmt0 : PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log
          (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))) := by
        unfold PlogMatches
        have : W64 (uint.nat m.Index') = m.Index' := by word
        rw [this]; exact Hmt0
      have hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0 := by
        intro h0
        have h0' : m.Index' = W64 0 := by word
        have := Hmt0; rw [show (absMsg .app m ents ctx).index = m.Index' from rfl, h0'] at this
        unfold plogTermAt at this
        simp [base0_index] at this
        exact this.symm
      have hps := phaseStepR_appStale id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole hstl
        hmt0 hlt0 hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .app m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .app evt bfl k ma (fun _ => False)
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      isplitl [Hg Hr]
      · iunfold ownStepGhost; iframe Hg Hr
      iframe Hc
      isplitr
      · iapply fxPresR_leadReply γ id ma _ s tn.voters cs0 _ P0 _ (fun a => stResp a (idAbs id) ma.source "app")
          hmd (fun _ => by simp [stResp]) (fun _ => rfl) (fun _ => by simp [stResp, canonMsg])
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          refine ⟨by rw [hms]; exact toC_lead _ _ _ _ hcx, by rw [hms]; exact stResp_toC _ _ _ _ _ _ hcx, ?_⟩
          rw [hmterm, hRa.1, hterm]; exact Int.lt_irrefl _
        · intro σ hsrv hpv' hcq' hmem hcs hsi
          have hσR : SimServerR tn.voters tn.voters.length (toPState s) (σ.s ma.dest) :=
            simServerR_toC (ha0.trans hcs.symm) hR0
          have hf : (σ.s ma.dest).state = Etcdraft.follower := by
            rw [hσR.2.1]; simp [toPState, hrole, proleRole, roleAbs]
          have hT' : ma.term = (σ.s ma.dest).currentTerm := by rw [hmterm, hσR.1, hterm]; rfl
          have hidxZ : ((uint.nat m.Index' : Nat) : Int) = uint.Z m.Index' := by word
          have hidx : ma.prevLogIndex + 1 ≤ (σ.s ma.dest).commitIndex := by
            rw [hmprev, hidxZ, hσR.2.2.2.2.2.2.1]; exact hstl
          have hlok : LogOkL ma (σ.s ma.dest).log = true := by
            rw [hσR.2.2.2.2.2.1, logOkL_abs _ _ ma _ (uint.nat m.Index') m.LogTerm' hmprev hmpt
              (fun k x hk hx => hs0.2.2 k x (by omega) hx) hlt0 (by word), decide_eq_true_iff]
            exact hmt0
          have hstep := handleAER_stale σ ma hf hT' hmsub hidx hlok
          have := TraceSpecInv.specInv_handleAppendEntriesRequest hsi
            (by rw [hsrv, hmd, mem_confAbs]; exact hidC) hmem rfl hmty' (by rw [hmsub]; decide) hpv' hcq'
            hstep _ (List.mem_singleton_self _)
          rw [staleRecvSt_eq σ ma hmsub] at this
          have e1 : stResp (σ.s ma.dest) ma.dest ma.source "app" = stResp (σ.s ma.dest) (idAbs id) ma.source "app" := by
            rw [hmd]
          rw [e1] at this
          exact this
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
        · -- the response's send line, skipped by the specification
          iintro %_ %s1 %mm %hres ⟨Hgh, Hc⟩
          have hx : s1 = { s with lead := m.From' } ∧
              mm = appResp id { s with lead := m.From' } m.From' false s.logst.committed (W64 0) (W64 0) := by
            unfold HandleAppResult at hres
            try simp only at hres
            rcases hres with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
            · exact sendMsgs_one_inj h
            · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; omega)
            · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; omega)
          obtain ⟨rfl, rfl⟩ := hx
          rw [htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
          imodintro
          have hn := appResp_nums id { s with lead := m.From' } m.From' s.logst.committed hT Hb.2
          have ht2 : uint.nat s.term < traceNumBound := by word
          have hOkR : ∀ e, (∃ mm ∈ [appResp id { s with lead := m.From' } m.From' false s.logst.committed
                (W64 0) (W64 0)], SendEvOf (W64 11) id { s with lead := m.From' } c mm e) →
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
  · -- the closing wand: raft's stale handling, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    have hse : s' = sendMsgs { s with lead := m.From' }
        [appResp id { s with lead := m.From' } m.From' false s.logst.committed (W64 0) (W64 0)] := by
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
      rcases hf with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; omega)
      · exact absurd h (by show ¬ uint.Z s.logst.committed ≤ uint.Z m.Index'; omega)
    subst hse
    have hmono : γ.reTrace.isSome → ∀ C cs P, VPin tn.voters
        (toC (confAbs tn.voters) { a0 with lead := idAbs m.From' })
        (P0 ++ [stResp a0 (idAbs id) (idAbs m.From') "app"]) C cs P →
        SimIdle C (sendMsgs { s with lead := m.From' }
          [appResp id { s with lead := m.From' } m.From' false s.logst.committed (W64 0) (W64 0)]) cs P := by
      intro hre
      rintro C cs P ⟨rfl, rfl, rfl⟩
      have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
      rw [hP0']
      exact staleEnd_simIdle tn.voters id s m a0 hR0 hs0 bt bc bl hrole
    unfold stepOut
    dsimp only [voteR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | ⟨Hgh, Hc, -⟩ | %h | ⟨%b, %N, %h⟩)
    rotate_right 2
    · exact h.elim
    · exact h.elim
    all_goals
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
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
        · exact .inr (fun _ => appResp_nums id _ m.From' s.logst.committed hT Hb.2)

end paths

end EtcdGrove
end Perennial
