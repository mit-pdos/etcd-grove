/-
Lean-first (no Rocq counterpart). **The higher-term receives' common pieces** (2026-11-10, trace-check Q8
stage 1 slice 20b, `notes/decisions.md`, "Q8 stage 1 (slice 20b)").

A message of a higher term than the node's: raft's `Step` steps down in its term preamble
(`becomeFollower(m.Term, lead)`, logging a `BecomeFollower` line), then handles the message as a follower
of the new term. The specification's receive line does both in two rounds: `UpdateTerm` (to `utSrv`,
`firstRound_ut`), then the handler at the new term (a `RecvAt`): `lineEffect_ut`. The `BecomeFollower`
line is skipped by `bfCond`'s `UpdateTerm` case, which reads the receive line as the node's previous
one (`bfCond_ut`, `phaseStepBF_ut`). The receive line's facts at the intermediate state (`simFx_ut`):
`SpecInv` by `specInv_becomeFollowerOfTerm` with leader completeness (`LeaderComplete`, from the facts
and raft's vote table, `leaderComplete_of`), the receiver's `srvFacts` at the new term from raft's own
facts of its log (its records, committed prefix and commit certificate, moved to the higher term by
`commitIn_agree`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvAppRej

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **A receive event's line**: its parse is the message line, a receive line, matching the message's
specification counterpart (`recvLine_pred` with the parse and the name). -/
theorem recvLine_full (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (mabs : Etcdraft.Msg) (hty : RecvEvTy m evt) (hev : SendEvOf evt m.dst s cfg m e)
    (hout : cfg.outgoing = ∅)
    (bmt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63)
    (bk : m.entries.length < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hmabs : TraceSim.msgAbs C C.length m = some mabs) :
    Etcdraft.parseLine 0 (evConv e) = .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) ∧
    Etcdraft.isReceiveName (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name = true ∧
    recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  rcases hty with ⟨hty, rfl⟩ | ⟨hty, hents, rfl⟩ | ⟨hty, rfl⟩ | hresp
  · obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
    refine ⟨aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inl hty),
      by simp only [msgLine, evConv]; rw [hname']; rfl, ?_⟩
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty bmt bmc bi blt bk
    simp only [hmabs, Option.get_some] at this; exact this
  · obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
    refine ⟨aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inr hty),
      by simp only [msgLine, evConv]; rw [hname']; rfl, ?_⟩
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_heartbeat C C.length e m.dst s.vote xs m tm hmsg hm hty hents bmt bmc
    simp only [hmabs, Option.get_some] at this; exact this
  · have hname' := (recvName_of _ e hname).2.2.1 rfl
    refine ⟨?_, by simp only [msgLine, evConv]; rw [hname']; rfl, ?_⟩
    · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
      exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
        (by rw [hm.1, hty]; rfl) (by rw [hname']; decide)
    · rw [recvPred_rvreq _ _ (by rw [msgLine_name, hname'])]
      have := isRVReq_vote C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty bmt bi blt
      simp only [hmabs, Option.get_some] at this; exact this
  · obtain ⟨nm, hname', hrn, htyp, -, -, -, hpred⟩ :=
      respLine C e s cfg m evt hresp hname tm hmsg hm bmt bi mabs hmabs
    refine ⟨?_, by simp only [msgLine, evConv]; rw [hname']; exact hrn, hpred⟩
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1]; exact htyp)
      (by rw [hname']; intro h; rw [h] at hrn; exact absurd hrn (by decide))

/-- **A higher-term message's receive line's effect**: `UpdateTerm` (the first round, to `utSrv`),
then the handler at the new term (`h2`, a one-round receipt at `utSrv`). -/
theorem lineEffect_ut (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (a a' : Etcdraft.Server) (mabs : Etcdraft.Msg) (fM fP : Etcdraft.Bag → Etcdraft.Bag)
    (hty : RecvEvTy m evt) (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C)
    (hout : cfg.outgoing = ∅) (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a)
    (hs : LogShapeOk C.length (toPState s)) (hpre : s.role ≠ .preCandidate)
    (hgt : uint.Z s.term < uint.Z m.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (bmt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63)
    (bk : m.entries.length < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hmabs : TraceSim.msgAbs C C.length m = some mabs)
    (h2 : RecvAt C (idAbs m.dst) (utSrv a mabs.term) a' mabs fM fP) :
    LineEffect C false e (idAbs m.dst) a a' (some mabs) fM fP (· = utSrv a mabs.term) := by
  obtain ⟨hparse, hrecv, hpred⟩ := recvLine_full C e s cfg m evt mabs hty hev hout bmt bi blt bk bmc hmabs
  obtain ⟨hmt, hmd, -, hq, hv, hr, hvr⟩ := msgAbs_recvTy hty hmabs
  have hC' : idAbs m.dst ∈ confAbs C := by rw [mem_confAbs]; exact hC
  have hty' : mabs.type = .requestVoteRequest ∨ mabs.type = .requestVoteResponse ∨
      mabs.type = .appendEntriesRequest ∨ mabs.type = .appendEntriesResponse := by
    rcases hty with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩)
    · exact .inr (.inr (.inl (hq (.inl h))))
    · exact .inr (.inr (.inl (hq (.inr h))))
    · exact .inl (hv h)
    · exact .inr (.inr (.inr (hr (.inl h))))
    · exact .inr (.inl (hvr h))
    · exact .inr (.inr (.inr (hr (.inr h))))
  have hlt : a.currentTerm < mabs.term := by rw [hR.1, hmt]; exact hgt
  obtain ⟨hkey, hfr⟩ := firstRound_ut C (idAbs m.dst) a mabs hmd hC' hty' hlt
  have hev' := hev
  obtain ⟨-, -, hterm', -, hcommit', hrl, hlog, ⟨xs, ys, hxs, -, -⟩, -⟩ := hev'
  apply lineEffect_recvU C e (idAbs m.dst) a (utSrv a mabs.term) a' mabs fM fP _ hparse rfl hrecv hpred hmd
    hkey _ h2
  intro σ hsrv hσi _ _
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem]; exact hC'
  refine ⟨?_, hfr σ hsrv hσi⟩
  rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
  have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs
    hpre hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
  unfold Etcdraft.Line.stateMatches at hsm ⊢
  simpa [msgLine, nodeLine] using hsm

/-- **`bfCond` after a higher-term message's receive line**: its `UpdateTerm` case (the receive event
of a message of a term above the node's, then a `BecomeFollower` event at the message's term). -/
theorem bfCond_ut (evt : w64) (id : w64) (s s1 : NState) (c : CfgM) (m : Msg) (e0 e : TraceEv)
    (hname : ∃ nm, gsStr e0.name = nm ∧ Etcdraft.isReceiveName nm = true)
    (h0 : SendEvOf evt id s c m e0) (h1 : NodeEvOf (W64 2) id s1 c e)
    (hgt : uint.Z s.term < uint.Z m.term) (hterm1 : s1.term = m.term) (bmt : uint.Z m.term < 2 ^ 63) :
    bfCond (evConv e0) (evConv e) = true := by
  obtain ⟨-, -, ht0, -, -, -, -, -, ⟨tm, hmsg, hm⟩, -⟩ := h0
  obtain ⟨-, -, ht1, -⟩ := h1
  obtain ⟨nm, hnm, hrn⟩ := hname
  have hs1 : sint.Z s.term = uint.Z s.term := by word
  have hs2 : sint.Z m.term = uint.Z m.term := by word
  unfold bfCond evConv
  simp only [hmsg, Option.map_some]
  rw [ht0, ht1, hterm1, hm.2.1, hnm, hrn]
  simp only [gInt, hs1, hs2, Bool.true_and, decide_eq_true_eq, beq_self_eq_true, Bool.and_true, Bool.true_or]
  rw [Bool.or_eq_true]; exact .inl (decide_eq_true hgt)

/-- **A `BecomeFollower` line after a higher-term message's receive line**: the skip, the share
unchanged. -/
theorem phaseStepBF_ut (id : w64) (c : CfgM) (s s1 : NState) (evt : w64) (mm : Msg) (C0 : List w64)
    (cs1 : ServerC) (P1 : List Etcdraft.Msg) (hname : ∀ e0, SendEvOf evt id s c mm e0 →
      ∃ nm, gsStr e0.name = nm ∧ Etcdraft.isReceiveName nm = true)
    (hgt : uint.Z s.term < uint.Z mm.term) (hterm1 : s1.term = mm.term) (bmt : uint.Z mm.term < 2 ^ 63) :
    PhaseStepBF id c s1 (VPin C0 cs1 P1) (VPin C0 cs1 P1) (RecvLast evt id s c mm) := by
  intro C cs P o hΦ hΛ _ e e0 he ho
  obtain ⟨e0', rfl, he0⟩ := hΛ
  obtain rfl : e0' = e0 := Option.some.inj ho
  refine ⟨fun _ => hΦ, fun hf => ?_⟩
  have := bfCond_ut evt id s s1 c mm e0' e (hname e0' he0) he0 he hgt hterm1 bmt
  rw [hf] at this; cases this

/-- A receive event's name is a receive name. -/
theorem recvEv_name (evt : w64) (id : w64) (s : NState) (c : CfgM) (m : Msg) (hty : RecvEvTy m evt) :
    ∀ e0, SendEvOf evt id s c m e0 → ∃ nm, gsStr e0.name = nm ∧ Etcdraft.isReceiveName nm = true := by
  intro e0 he0
  have hn := recvName_of evt e0 he0.1
  rcases hty with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩ | (⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, rfl⟩)
  · exact ⟨_, hn.1 rfl, by decide⟩
  · exact ⟨_, hn.1 rfl, by decide⟩
  · exact ⟨_, hn.2.2.1 rfl, by decide⟩
  · exact ⟨_, hn.2.1 rfl, by decide⟩
  · exact ⟨_, hn.2.2.2 rfl, by decide⟩
  · exact ⟨_, hn.2.1 rfl, by decide⟩

/-- `toC` of `UpdateTerm`'s server, from `toC` of the server. -/
theorem toC_utSrv (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (T : Int) (h : toC S x = toC S y) :
    toC S (utSrv x T) = toC S (utSrv y T) := by
  simp only [toC, utSrv] at h ⊢
  injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, h3, h5, h6, h7, h8, h9, h10, h11, h12]

end pure

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Leader completeness at a server entering a later term**, from the facts and raft's vote table
(`allFacts_commitOk`, `allFacts_leaderCompleteness`); the table given back. -/
theorem leaderComplete_of (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : Etcdraft.ID) (T : Int)
    (hsrv : σ.server = confAbs C) (hi : i ∈ σ.server) (hT : (σ.s i).currentTerm < T)
    (hcw : CommitWithinLeader σ) :
    votesTbl (GF := GF) γ ∗ allFacts γ C σ ⊢ votesTbl γ ∗ ⌜TraceSpecInv.LeaderComplete σ i T⌝ := by
  iintro ⟨Htbl, #Hal⟩
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %Hco
  icases persistent_entails_right (allFacts_leaderCompleteness γ C σ hsrv hcw) $$ [$Htbl $Hal]
    with ⟨%Hlc, Htbl, -⟩
  iframe Htbl
  ipureintro
  refine ⟨(Hco i hi).2, ?_⟩
  intro l hl hll hlt idx0 hidx hgt
  have hlm : l ∈ σ.currentLeaders := by
    unfold Etcdraft.State.currentLeaders; exact List.mem_filter.2 ⟨hl, by simp [hll]⟩
  exact Hlc i hi idx0 hidx l hlm hgt (by rw [hlt]; exact Int.le_of_lt hT)

/-- **`UpdateTerm` keeps the facts** (`BecomeFollowerOfTerm(i, T)` at a later term `T`): `SpecInv` with
leader completeness (`leaderComplete_of`); the receiver's `srvFacts` at `T` from raft's facts of its
log `L` (its records, committed prefix and commit certificate at its term, moved up by
`commitIn_agree`); the logs, commit indices, configurations and bags unchanged; the receiver no longer
leads. -/
theorem simFx_ut (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (k : w64) (T : Int) (L : List EntryM)
    (hsrv : σ.server = confAbs C) (hkC : k ∈ C) (hT : (σ.s (idAbs k)).currentTerm < T) (hT63 : T < 2 ^ 63)
    (hlog : (σ.s (idAbs k)).log = logAbs C C.length 1 L) (hbL : BootTerms C.length 1 L)
    (hwr : PlogWfR (entryID.mk (W64 0) (W64 0)) L) (c t : Int) (hc : (σ.s (idAbs k)).commitIndex = c)
    (ht : (σ.s (idAbs k)).currentTerm = t) :
    votesTbl (GF := GF) γ ∗ simFx γ C σ ∗ logRecs γ base0 L ∗
      isCommitted γ (L.take c.toNat) ∗ commitIn γ L (W64 c) (W64 t) ⊢
      votesTbl γ ∗ simFx γ C (withNode σ (idAbs k) (utSrv (σ.s (idAbs k)) T) _root_.id _root_.id) := by
  rw [← hc, ← ht]
  have hi : idAbs k ∈ σ.server := by rw [hsrv, mem_confAbs]; exact hkC
  obtain ⟨W, hW⟩ : ∃ W, W = withNode σ (idAbs k) (utSrv (σ.s (idAbs k)) T) _root_.id _root_.id := ⟨_, rfl⟩
  rw [← hW]
  have hWs : ∀ j, W.s j = if j = idAbs k then utSrv (σ.s (idAbs k)) T else σ.s j := by intro j; rw [hW]; rfl
  have hF : ∀ j, (W.s j).log = (σ.s j).log ∧ (W.s j).commitIndex = (σ.s j).commitIndex ∧
      (W.s j).config = (σ.s j).config := by
    intro j; rw [hWs]; split
    · rename_i hj; subst hj; simp [utSrv]
    · simp
  have hfl : Etcdraft.follower ≠ Etcdraft.leader := by decide
  iintro ⟨Htbl, Hfx, #HL, #Hcm, #Hci⟩
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hq, hu, hsh, has⟩ := Hp
  icases leaderComplete_of γ C σ (idAbs k) T hsrv hi hT hsi.commitWithinLeader $$ [$Htbl $Hal]
    with ⟨Htbl, %Hlc⟩
  have hsi' : TraceSpecInv.SpecInv W := by
    rw [hW]
    exact TraceSpecInv.specInv_becomeFollowerOfTerm hsi (Int.le_of_lt hT)
      (fun l hl _ hll hlt => TraceSpecInv.commitInDurable_of_complete hsi hi hT Hlc l hl hll hlt)
  -- the receiver's facts at the new term
  ihave #Hal' := Hal
  iunfold allFacts at Hal'
  ihave #Hk := Hal' $$ %k %hkC
  iunfold srvFacts at Hk
  icases Hk with ⟨%es, %pend, %Hpk, -, -, -, -⟩
  obtain ⟨hlg, -, -, hln, hc0, hcl, ht0, -, -, -⟩ := Hpk
  have hlen : L.length = (es ++ pend).length := by
    have := congrArg List.length (hlg.symm.trans hlog); simpa [logAbs_length] using this.symm
  iframe Htbl
  iunfold simFx
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %j %hj
    rw [hWs]
    by_cases hjk : idAbs j = idAbs k
    · simp only [hjk, ↓reduceIte]
      iunfold srvFacts
      iexists L, []
      simp only [List.append_nil, utSrv]
      have hst : ¬ (Etcdraft.follower = Etcdraft.leader) := hfl
      simp only [hst, ↓reduceIte]
      isplitr
      · ipureintro
        refine ⟨hlog, hbL, hwr, by rw [hlen]; exact hln, hc0, ?_, by omega, hT63, fun _ => trivial,
          fun e he => by simp at he⟩
        rw [List.length_append] at hlen; omega
      iframe HL Hcm
      isplitr
      · ipureintro; trivial
      iapply commitIn_agree γ L L _ _ _ (by
        have h1 : uint.Z (W64 (σ.s (idAbs k)).currentTerm) = (σ.s (idAbs k)).currentTerm := by word
        have h2 : uint.Z (W64 T) = T := by word
        rw [h1, h2]; exact Int.le_of_lt hT) rfl rfl $$ Hci
    · simp only [hjk, ↓reduceIte]
      iapply Hal $$ %j %hj
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf; ipureintro; rw [hW] at hx; exact hx
  ipureintro
  refine ⟨hsi', quorumLogF_congr σ W (by rw [hW]; rfl) (fun j => (hF j).1) (fun j => (hF j).2.1)
    (fun j => (hF j).2.2) hq, by rw [hW]; exact hu, by rw [hW]; exact hsh, ?_⟩
  intro m hm hty j hj hlj htj hs j' e he
  have hm' : m ∈ σ.messages.domain ++ σ.pendingMessages.domain := by rw [hW] at hm; exact hm
  have hj' : j ∈ σ.server := by rw [hW] at hj; exact hj
  rw [hWs] at hlj htj ⊢
  split at hlj
  · simp [utSrv] at hlj; exact absurd hlj hfl
  · rename_i hjk
    simp only [hjk, ↓reduceIte] at htj ⊢
    exact has m hm' hty j hj' hlj htj hs j' e he

end fx

end EtcdGrove
end Perennial
