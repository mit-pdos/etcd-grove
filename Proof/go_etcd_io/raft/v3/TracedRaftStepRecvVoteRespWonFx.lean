/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's won election: the
facts its node-event lines keep** (2026-11-11, trace-check Q8 stage 1 slice 27b, `notes/decisions.md`,
"Q8 stage 1 (slice 27b)").

- **The new leader's server facts** (`srvFacts_newLeader`): from raft's own facts of its log (its
  records, committed prefix and commit certificate, `ownRaftGhost_logFacts`), its registration
  (`isLeader`, its campaign log, which is its log) and its term's full log (`leadFull`, at its log,
  which the registration's wand gives), with its pending entries (none at the `BecomeLeader` line, the
  empty entry at its `Replicate` line): not from the facts the specification's state held of the
  candidate, whose recorded log is not determined by the server's (`logAbs` forgets the entries' data).
- **The `BecomeLeader` line's facts** (`simFx_becomeLeaderW`, `fxPresU_becomeLeader`): the
  specification's `BecomeLeader` keeps `SpecInv` (`specInv_becomeLeader`, its premises
  `becomeLeader_hyps`'s, from the registration's outputs and the facts), `QuorumLogF` (no log or commit
  index moves, `quorumKept_mono`; amendment A6's `ackHists_becomeLeader`), the bags, `MsgsShape` (no
  tally moves) and `AppSlices` (a new leader's clause vacuous, `appSlices_becomeLeader`); the term log
  is allocated inside the line's update (the registration's wand), after its freshness is read.
- **The empty entry's `Replicate` line's facts** (`simFx_replicate_of`, `fxPres_replicateW`): slice
  24a's `simFx_replicate` with the new leader's facts given (`srvFacts_newLeader` with the entry
  pending) instead of derived from its last entry's term.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteRespWonPhase
public import Proof.go_etcd_io.raft.v3.TraceSimLeader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A new leader's server facts** (see the header): its recorded log raft's `L`, its pending entries
`pd` of its term. -/
theorem srvFacts_newLeader (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server)
    (L pd : List EntryM) (hl : v.state = Etcdraft.leader) (hlog : v.log = logAbs C C.length 1 (L ++ pd))
    (hbt : BootTerms C.length 1 (L ++ pd)) (hwf : PlogWfR (entryID.mk (W64 0) (W64 0)) (L ++ pd))
    (hlen : (L ++ pd).length < 2 ^ 63) (hc0 : 0 ≤ v.commitIndex) (hcl : v.commitIndex ≤ L.length)
    (ht0 : 0 ≤ v.currentTerm) (ht63 : v.currentTerm < 2 ^ 63)
    (hpt : ∀ e ∈ pd, e.Term' = W64 v.currentTerm) :
    (logRecs γ base0 L ∗ isCommitted γ (L.take v.commitIndex.toNat) ∗
      commitIn γ L (W64 v.commitIndex) (W64 v.currentTerm) ∗ isLeader γ j (W64 v.currentTerm) ∗
      leadFull γ (W64 v.currentTerm) L ∗ isCamp γ j (W64 v.currentTerm) L : IProp GF) ⊢
      srvFacts γ C j v := by
  unfold srvFacts
  simp only [hl, ↓reduceIte]
  iintro ⟨#Hr, #Hc, #Hci, #Hl, #Hf, #Hcp⟩
  iexists L, pd
  isplitr
  · ipureintro; exact ⟨hlog, hbt, hwf, hlen, hc0, hcl, ht0, ht63, fun h => absurd rfl h, hpt⟩
  isplitr
  · iexact Hr
  isplitr
  · iexact Hc
  isplitr
  · isplitr
    · iexact Hl
    isplitr
    · iexact Hf
    iright
    iexists L
    iframe Hcp
    ipureintro; exact ⟨List.prefix_refl _, .inl rfl⟩
  · iexact Hci

/-- **The specification's `BecomeLeader` keeps the facts** (see the header), at node `id`'s server `a`, a
candidate whose granted voters are a quorum, its log raft's `L`; the term log allocated inside (the
wand `Hw`, the registration's), its full log returned with the wand's `R`. -/
theorem simFx_becomeLeaderW (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (id : w64)
    (a : Etcdraft.Server) (L : List EntryM)
    (hsrv : σ.server = confAbs C) (hidC : id ∈ C) (hσa : σ.s (idAbs id) = a)
    (hcand : a.state = Etcdraft.candidate) (hcfg : a.config.incoming = confAbs C)
    (hq : Etcdraft.isQuorum a.votesGranted (confAbs C) = true)
    (hlog : a.log = logAbs C C.length 1 L) (hbt : BootTerms C.length 1 L)
    (hwf : PlogWfR (entryID.mk (W64 0) (W64 0)) L) (hlen : L.length < 2 ^ 63)
    (hc0 : 0 ≤ a.commitIndex) (hcl : a.commitIndex ≤ L.length)
    (ht0 : 0 ≤ a.currentTerm) (ht63 : a.currentTerm < 2 ^ 63)
    (hboot : γ.reBoot ≠ []) (γm : GName) (terms : GMap w64 TermRec)
    (hγm : γ.reTerms !! id = some γm) (hfree : terms !! W64 a.currentTerm = none) (R : IProp GF) :
    (votesTbl γ ∗ simFx γ C σ ∗ isLeader γ id (W64 a.currentTerm) ∗ isCamp γ id (W64 a.currentTerm) L ∗
      logRecs γ base0 L ∗ isCommitted γ (L.take a.commitIndex.toNat) ∗
      commitIn γ L (W64 a.commitIndex) (W64 a.currentTerm) ∗ ghostMapAuth γm 1 terms ∗
      (ghostMapAuth γm 1 terms ==∗ leadFull γ (W64 a.currentTerm) L ∗ R) : IProp GF) ⊢
      |==> (votesTbl γ ∗ simFx γ C (σ.upd (idAbs id) (leaderOf (idAbs id))) ∗
        leadFull γ (W64 a.currentTerm) L ∗ R) := by
  iintro ⟨Htbl, #Hfx, #Hl, #Hcp, #Hr, #Hcm, #Hci, Ha, Hw⟩
  ihave #Hfx0 := Hfx
  iunfold simFx at Hfx0
  icases Hfx0 with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  have hcσ : (σ.s (idAbs id)).state = Etcdraft.candidate := by rw [hσa]; exact hcand
  have hF0 : (σ.s (idAbs id)).log.length = L.length := by rw [hσa, hlog, logAbs_length]
  have hfree' : terms !! W64 (σ.s (idAbs id)).currentTerm = none := by rw [hσa]; exact hfree
  -- `specInv_becomeLeader`'s premises, the table and the authority kept
  have HH := becomeLeader_hyps (GF := GF) γ C σ id L γm terms hsrv hidC hcσ hsi hF0 hγm hfree' hboot
  have HH' : (votesTbl γ ∗ ghostMapAuth γm 1 terms ∗ (allFacts γ C σ ∗
      (□ ∀ m, ⌜m ∈ σ.messages.domain ++ σ.pendingMessages.domain⌝ → msgFacts γ C m) ∗
      isLeader γ id (W64 (σ.s (idAbs id)).currentTerm) ∗ isCamp γ id (W64 (σ.s (idAbs id)).currentTerm) L ∗
      logRecs γ base0 L) : IProp GF) ⊢
      ⌜(∀ j ∈ σ.server, ∀ e ∈ (σ.s j).log, e.term ≠ (σ.s (idAbs id)).currentTerm) ∧
        (∀ m ∈ TraceSpecInv.msgs σ, ∀ e ∈ m.entries, e.term ≠ (σ.s (idAbs id)).currentTerm) ∧
        (∀ m ∈ TraceSpecInv.msgs σ, m.type = .appendEntriesRequest →
          m.term ≠ (σ.s (idAbs id)).currentTerm) ∧
        (∀ k ∈ σ.server, (σ.s k).currentTerm = (σ.s (idAbs id)).currentTerm →
          (σ.s k).commitIndex ≤ (σ.s (idAbs id)).log.length)⌝ := by
    iintro ⟨Ht, Ha, #Hal, #Hmf, #Hl, #Hc, #Hr⟩
    iapply HH $$ Ht Hal Hmf Hl Hc Hr Ha
  rw [hσa] at HH'
  ihave H := persistent_entails_right HH' $$ [Htbl Ha]
  · iframe Htbl Ha Hal Hmf Hl Hcp Hr
  icases H with ⟨%Hh, Htbl, Ha, -⟩
  rw [← hσa] at Hh
  obtain ⟨h1, h2, h3, h4⟩ := Hh
  -- the term log
  imod Hw $$ Ha with ⟨#Hf, HR⟩
  -- the specification's step
  have hstep : σ.becomeLeader (idAbs id) = some (σ.upd (idAbs id) (leaderOf (idAbs id))) := by
    unfold Etcdraft.State.becomeLeader Etcdraft.State.getConfig
    rw [hσa]; simp only [hcand, hcfg, hq, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl
  have hsi' := TraceSpecInv.specInv_becomeLeader hsi hi h1 h2 h3 h4 hstep
  have hs : ∀ k, (σ.upd (idAbs id) (leaderOf (idAbs id))).s k =
      if k = idAbs id then leaderOf (idAbs id) a else σ.s k := by
    intro k; by_cases hk : k = idAbs id
    · subst hk; rw [TraceSpecInv.upd_s_self, hσa, if_pos rfl]
    · rw [TraceSpecInv.upd_s_ne _ _ _ _ hk, if_neg hk]
  have hL : ∀ k, ((σ.upd (idAbs id) (leaderOf (idAbs id))).s k).log = (σ.s k).log := by
    intro k; rw [hs]; split
    · rename_i h; subst h; rw [hσa]; rfl
    · rfl
  have hC : ∀ k, ((σ.upd (idAbs id) (leaderOf (idAbs id))).s k).commitIndex = (σ.s k).commitIndex := by
    intro k; rw [hs]; split
    · rename_i h; subst h; rw [hσa]; rfl
    · rfl
  have hT : ∀ k, ((σ.upd (idAbs id) (leaderOf (idAbs id))).s k).currentTerm = (σ.s k).currentTerm := by
    intro k; rw [hs]; split
    · rename_i h; subst h; rw [hσa]; rfl
    · rfl
  imodintro
  iframe Htbl HR Hf
  iunfold simFx
  isplitl
  · -- every voter's facts: the new leader's from raft's
    iunfold allFacts
    iunfold allFacts at Hal
    imodintro
    iintro %j %hj
    rw [hs]
    by_cases hji : idAbs j = idAbs id
    · rw [if_pos hji]
      have := TraceSim.idAbs_inj.1 hji
      subst this
      iapply srvFacts_newLeader γ C j (leaderOf (idAbs j) a) L [] rfl (by rw [List.append_nil]; exact hlog)
        (by rw [List.append_nil]; exact hbt) (by rw [List.append_nil]; exact hwf)
        (by rw [List.append_nil]; exact hlen) hc0 hcl ht0 ht63 (fun e he => by cases he)
      simp only [leaderOf]
      iframe Hr Hcm Hci Hl Hf Hcp
    · rw [if_neg hji]
      iapply Hal $$ %j %hj
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf; ipureintro; exact hx
  isplitl
  · -- `QuorumLogF`: no log, commit index or term moves; no acknowledgement held yet
    iunfold QuorumLogF at Hq
    icases Hq with ⟨#Hk, #Hah⟩
    iunfold QuorumLogF
    isplitl
    · iapply quorumKept_mono γ C σ (σ.upd (idAbs id) (leaderOf (idAbs id))) rfl
        (fun i hi => ⟨i, hi, by unfold committedL; rw [hL, hC]; exact List.prefix_refl _⟩)
        (fun _ _ h => keptFrom_congr (σ := σ) (σ' := σ.upd (idAbs id) (leaderOf (idAbs id))) rfl hL
          (fun k => by rw [hT]; exact Int.le_refl _) h) $$ Hk
    · iapply ackHists_becomeLeader γ C σ _ (idAbs id) hstep $$ Hah
  ipureintro
  refine ⟨hsi', msgsUniq_mono (fun x hx => hx) hu,
    msgsShape_of (σ := σ) rfl (fun x hx => hx) (fun j => by
      rw [hs]; split
      · rename_i h; subst h; rw [hσa]; rfl
      · rfl) hsh, ?_⟩
  refine appSlices_mono σ _ has rfl (fun m hm => hm) ?_
  intro j hj hl
  by_cases hji : j = idAbs id
  · subst hji
    right
    rw [hT]
    exact appSlices_becomeLeader σ hsi.2.2.2.1 _ hj hcσ
  · rw [hs, if_neg hji] at hl
    left
    rw [hs, if_neg hji]
    exact ⟨hl, rfl, List.prefix_refl _⟩

/-- **The `BecomeLeader` line's facts, with the term log's allocation** (`FxPresU`): from the receive
line's result phase (the tally's idle server, a quorum) to the leader's (`phaseStepB_becomeLeader`),
`simFx_becomeLeaderW` at the server the phase pins, then `simFx_congr` to the line's result. Raft's
facts of the candidate's log `(toPState s).log` (uncompacted), its registration and the lent
authority with its wand (the registration's, giving `R`) are the caller's. -/
theorem fxPresU_becomeLeader (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (s : NState) (m : MessageM)
    (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) (hidC : id ∈ C0) (hrole : s.role = .candidate)
    (hcl : uint.Z s.logst.committed ≤ (toPState s).log.length)
    (hboot : γ.reBoot ≠ []) (γm : GName) (terms : GMap w64 TermRec)
    (hγm : γ.reTerms !! id = some γm) (hfree : terms !! s.term = none) (R : IProp GF) :
    (isLeader γ id s.term ∗ isCamp γ id s.term (toPState s).log ∗ logRecs γ base0 (toPState s).log ∗
      isCommitted γ ((toPState s).log.take (uint.Z s.logst.committed).toNat) ∗
      commitIn γ (toPState s).log s.logst.committed s.term ∗ ghostMapAuth γm 1 terms ∗
      (ghostMapAuth γm 1 terms ==∗ leadFull γ s.term (toPState s).log ∗ R) : IProp GF) ⊢
      FxPresU γ id E (WonRecvPin (votedState s m) C0 cs1 P0)
        (PinAt (wonL id s m) C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 s.outbox)
        iprop(leadFull γ s.term (toPState s).log ∗ R) := by
  iintro ⟨#Hl, #Hcp, #Hr, #Hcm, #Hci, Ha, Hw⟩
  iunfold FxPresU
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨⟨rfl, rfl, rfl, hI⟩, hq⟩, -, hcs, ⟨-, hcs', hP', -⟩, -, hsrv, hσa, -, -, -⟩ := hpre
  have hP0 : P' = [] := by
    have := congrArg List.length hP'; rw [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hP0
  obtain ⟨a1, ha1, hR1, hs1, -, bt, bc, bl⟩ := hI
  have hR : SimServerR C C.length (toPState (votedState s m)) a := simServerR_toC (ha1.trans hcs.symm) hR1
  have hpre' : s.role ≠ .preCandidate := by rw [hrole]; decide
  have hcand : a.state = Etcdraft.candidate := by
    rw [hR.2.1]; simp [toPState, hrole, proleRole, roleAbs]
  have hcfg : a.config.incoming = confAbs C := by rw [hR.2.2.2.2.2.2.2.1]
  have hq' : Etcdraft.isQuorum a.votesGranted (confAbs C) = true := by
    have : (toC (confAbs C) a).votesGranted = a.votesGranted := rfl
    rw [← this, hcs]; exact hq
  have hlog : a.log = logAbs C C.length 1 (toPState s).log := hR.2.2.2.2.2.1
  have hbt : BootTerms C.length 1 (toPState s).log :=
    fun k e hk he => hs1.2.2 k e (by omega) he
  have hwf : PlogWfR (entryID.mk (W64 0) (W64 0)) (toPState s).log := by
    have h := PlogWf_wfR _ _ hs1.2.1
    rw [hs1.1] at h; exact h
  have hlen : (toPState s).log.length < 2 ^ 63 := by
    have h1 := plastIndex_length _ _ hs1
    have h3 : (toPState (votedState s m)).log = (toPState s).log := rfl
    rw [h3] at h1
    have : uint.Z (plastIndex (toPState (votedState s m))) < 2 ^ 63 := bl
    omega
  have hT : a.currentTerm = uint.Z s.term := hR.1
  have hCm : a.commitIndex = uint.Z s.logst.committed := hR.2.2.2.2.2.2.1
  have hWT : W64 a.currentTerm = s.term := by rw [hT]; simp
  have hWC : W64 a.commitIndex = s.logst.committed := by rw [hCm]; simp
  have hc0 : 0 ≤ a.commitIndex := by rw [hCm]; exact uint_Z_nonneg _
  have ht0 : 0 ≤ a.currentTerm := by rw [hT]; exact uint_Z_nonneg _
  have ht63 : a.currentTerm < 2 ^ 63 := by rw [hT]; exact bt
  ihave Hu := simFx_becomeLeaderW γ C σ id a (toPState s).log hsrv hidC hσa hcand hcfg hq' hlog hbt hwf hlen
    hc0 (by rw [hCm]; exact hcl) ht0 ht63 hboot γm terms hγm (by rw [hWT]; exact hfree) R $$ [Htbl Ha Hw]
  · rw [hWT, hWC, hCm]
    iframe Htbl Hfx Hl Hcp Hr Hcm Hci Ha Hw
  imod Hu with ⟨Htbl, #H1, Hf, HR⟩
  rw [hWT]
  have hs : ∀ j, toC (σ.upd (idAbs id) (leaderOf (idAbs id))).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.upd (idAbs id) (leaderOf (idAbs id))).server ((σ.upd (idAbs id) (leaderOf (idAbs id))).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) =
      toC σ.server (if j = idAbs id then leaderOf (idAbs id) (σ.s (idAbs id)) else σ.s j)
    split
    · rw [hσa, hsrv, toC_leaderOf, hcs, hcs']
    · rfl
  ihave #H3 := simFx_congr γ C (σ.upd (idAbs id) (leaderOf (idAbs id)))
    (withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H1
  imodintro
  iframe Htbl H3 Hf HR

/-- **A `Replicate` line's facts, the leader's server facts given** (`simFx_replicate` with the
leader's `srvFacts` after the line a premise instead of derived from its last entry's term). -/
theorem simFx_replicate_of (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (id : w64)
    (a : Etcdraft.Server) (hsrv : σ.server = confAbs C) (hidC : id ∈ C) (hσa : σ.s (idAbs id) = a)
    (hl : a.state = Etcdraft.leader) :
    (simFx (GF := GF) γ C σ ∗ srvFacts γ C id (repSrv a)) ⊢
      simFx γ C (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id) := by
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  have hs' : ∀ j, (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s j =
      if j = idAbs id then repSrv a else σ.s j := fun _ => rfl
  iintro ⟨#Hfx, #Hnew⟩
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  icases allFacts_oneLeader γ C σ hsrv $$ Hal with %h1
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %hco
  iunfold simFx
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %j %hj
    rw [hs']
    by_cases hji : idAbs j = idAbs id
    · rw [if_pos hji]
      have := TraceSim.idAbs_inj.1 hji
      subst this
      iexact Hnew
    · rw [if_neg hji]
      iapply Hal $$ %j %hj
  isplitl
  · have hm : (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).messages = σ.messages := rfl
    have hp : (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).pendingMessages = σ.pendingMessages := rfl
    rw [hm, hp]
    imodintro; iexact Hmf
  have hL : ∀ k, (σ.s k).log <+: ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s k).log := by
    intro k; rw [hs']; split
    · rename_i h; subst h; rw [hσa]; exact List.prefix_append _ _
    · exact List.prefix_refl _
  have hC : ∀ k, ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s k).commitIndex = (σ.s k).commitIndex := by
    intro k; rw [hs']; split
    · rename_i h; subst h; rw [hσa]; rfl
    · rfl
  have hT : ∀ k, (σ.s k).currentTerm ≤ ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s k).currentTerm := by
    intro k; rw [hs']; split
    · rename_i h; subst h; rw [hσa]; exact Int.le_refl _
    · exact Int.le_refl _
  isplitl
  · iapply quorumLogF_grow γ C σ (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id) rfl hL hC hT hco
      (fun x hx _ => hx)
      (fun k hk => by
        rw [hs'] at hk ⊢
        by_cases h : k = idAbs id
        · rw [if_pos h] at hk ⊢; subst h; rw [hσa]; exact ⟨hk, rfl, fun _ _ => rfl⟩
        · rw [if_neg h] at hk ⊢; exact ⟨hk, rfl, fun _ _ => rfl⟩)
    iexact Hq
  ipureintro
  have hcr : σ.clientRequest (idAbs id) 0 = some (σ.replicate (idAbs id) (.val 0) .value) := by
    unfold Etcdraft.State.clientRequest; simp [hσa, hl]
  have hrep : σ.replicate (idAbs id) (.val 0) .value = withNode σ (idAbs id) (repSrv a) _root_.id _root_.id := by
    rw [Etcdraft.State.replicate, upd_eq_withNode, hσa]; rfl
  rw [hrep] at hcr
  refine ⟨TraceSpecInv.specInv_clientRequest hsi hi h1 hcr, hu,
    msgsShape_of (σ := σ) rfl (fun x hx => hx) (fun j => by
      show Etcdraft.Server.votesResponded (if j = _ then _ else _) = _
      split
      · rename_i h; subst h; rw [hσa]; rfl
      · rfl) hsh, ?_⟩
  exact appSlices_extend σ has (idAbs id) (repSrv a) (by rw [hσa]; rfl) (by rw [hσa]; rfl)
    (by rw [hσa]; exact List.prefix_append _ _)

/-- **The empty entry's `Replicate` line's facts** (`FxPres` at the leader's pinned phases): the leader's
server facts after the line from raft's (`srvFacts_newLeader`, the entry pending, a value entry of its
term past the bootstrap entries, `hbl0`), then `simFx_replicate_of` and `simFx_congr` to the line's
result. -/
theorem fxPres_replicateW (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (s : NState) (m : MessageM)
    (o : List Msg) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (hidC : id ∈ C0)
    (hbl0 : C0.length ≤ (toPState s).log.length)
    (hcl : uint.Z s.logst.committed ≤ (toPState s).log.length)
    (hbnd : (toPState s).log.length + 1 < 2 ^ 63) :
    (leadFull γ s.term (toPState s).log ∗ isLeader γ id s.term ∗ isCamp γ id s.term (toPState s).log ∗
      logRecs γ base0 (toPState s).log ∗
      isCommitted γ ((toPState s).log.take (uint.Z s.logst.committed).toNat) ∗
      commitIn γ (toPState s).log s.logst.committed s.term : IProp GF) ⊢
      FxPres γ id E (RepPin (wonL id s m) [zero_val EntryM] o C0 cs0 P0 0)
        (RepPin (wonL id s m) [zero_val EntryM] o C0 cs0 P0 1) := by
  iintro ⟨#Hf, #Hl, #Hcp, #Hr, #Hcm, #Hci⟩
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, hcs, rfl, hI, -⟩, -, hca, ⟨-, hcs', hP', -⟩, -, hsrv, hσa, -, -, -⟩ := hpre
  have hP0 : P' = [] := by
    have := congrArg List.length hP'; rw [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hP0
  rw [← hca] at hI
  obtain ⟨a0, ha0, hR0, hs0, bt, bc, bl⟩ := hI
  have hR : SimServerR C C.length (toPState (propK (wonL id s m) [zero_val EntryM] 0)) a := simServerR_toC ha0 hR0
  have hL0 : (toPState (propK (wonL id s m) [zero_val EntryM] 0)).log = (toPState s).log := by
    simp [propK, propAppended, toPState, logAppend, becomeLeaderPre, resetTo, resetTo0]
  have hl : a.state = Etcdraft.leader := by
    rw [hR.2.1]; simp [toPState, propK, propAppended, becomeLeaderPre, proleRole, roleAbs]
  have hlog : a.log = logAbs C C.length 1 (toPState s).log := by rw [hR.2.2.2.2.2.1, hL0]
  have hT : a.currentTerm = uint.Z s.term := hR.1
  have hCm : a.commitIndex = uint.Z s.logst.committed := hR.2.2.2.2.2.2.1
  have hlen0 : (toPState s).log.length < 2 ^ 63 := by
    have h1 := plastIndex_length _ _ hs0
    rw [hL0] at h1
    have : uint.Z (plastIndex (toPState (propK (wonL id s m) [zero_val EntryM] 0))) < 2 ^ 63 := bl
    omega
  -- the leader's facts after the line, from raft's: the empty entry pending
  let x : EntryM := { (zero_val EntryM) with Term' := W64 a.currentTerm, Index' := W64 ((toPState s).log.length + 1 : Nat) }
  have hn : ¬ (1 + (toPState s).log.length ≤ C.length) := by omega
  have hlog' : (repSrv a).log = logAbs C C.length 1 ((toPState s).log ++ [x]) := by
    show a.log ++ _ = _
    rw [logAbs_snoc, ← hlog]
    have hw : uint.Z (W64 a.currentTerm : w64) = a.currentTerm := by rw [hT]; simp
    simp only [entAbs, if_neg hn, x, hw]
  have hbt' : BootTerms C.length 1 ((toPState s).log ++ [x]) := by
    intro k e hk he
    rcases Nat.lt_or_ge k (toPState s).log.length with hk' | hk'
    · rw [List.getElem?_append_left hk'] at he; exact hs0.2.2 k e (by omega) (by rw [hL0]; exact he)
    · omega
  have hwf0 : PlogWfR (entryID.mk (W64 0) (W64 0)) (toPState s).log := by
    have h := PlogWf_wfR _ _ hs0.2.1
    rw [hs0.1, hL0] at h; exact h
  have hwf' : PlogWfR (entryID.mk (W64 0) (W64 0)) ((toPState s).log ++ [x]) := by
    intro k e he hk64
    rcases Nat.lt_or_ge k (toPState s).log.length with hk' | hk'
    · rw [List.getElem?_append_left hk'] at he; exact hwf0 k e he hk64
    · rw [List.getElem?_append_right hk'] at he
      have hk0 : k - (toPState s).log.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 he).1
        simp only [List.length_singleton] at this; omega
      rw [hk0] at he
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      have hk1 : k = (toPState s).log.length := by omega
      subst hk1
      simp only [x]
      have : uint.Z (entryID.mk (W64 0) (W64 0)).index' = 0 := rfl
      rw [this] at hk64 ⊢
      word
  have hWT : W64 (repSrv a).currentTerm = s.term := by
    show W64 a.currentTerm = s.term; rw [hT]; simp
  have hWC : W64 (repSrv a).commitIndex = s.logst.committed := by
    show W64 a.commitIndex = s.logst.committed; rw [hCm]; simp
  ihave #Hnew := srvFacts_newLeader γ C id (repSrv a) (toPState s).log [x] hl hlog' hbt' hwf'
    (by rw [List.length_append]; simp only [List.length_singleton]; omega)
    (by show 0 ≤ a.commitIndex; rw [hCm]; exact uint_Z_nonneg _)
    (by show a.commitIndex ≤ _; rw [hCm]; exact hcl)
    (by show 0 ≤ a.currentTerm; rw [hT]; exact uint_Z_nonneg _)
    (by show a.currentTerm < _; rw [hT]; exact bt)
    (fun e he => by rw [List.mem_singleton] at he; subst he; rfl) $$ []
  · rw [hWT, hWC, show (repSrv a).commitIndex = uint.Z s.logst.committed from hCm]
    iframe Hr Hcm Hci Hl Hf Hcp
  ihave #H2 := simFx_replicate_of γ C σ id a hsrv hidC hσa hl $$ [$Hfx $Hnew]
  have hs : ∀ j, toC (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b)).s j) =
      toC (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).server
        ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (if j = idAbs id then repSrv a else σ.s j)
    split
    · rw [hsrv, hcs', toC_repSrv_eq, hca, hcs]; rfl
    · rfl
  ihave #H3 := simFx_congr γ C (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id)
    (withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H2
  iframe Htbl
  iexact H3

end facts

end EtcdGrove
end Perennial
