/-
Lean-first (no Rocq counterpart). **A leader's accepted `MsgAppResp` of its term: the `Commit` line**
(2026-11-11, trace-check Q8 stage 1 slice 29c, `notes/decisions.md`, "Q8 stage 1 (slice 29c)").

- **The bridge from `maybeCommitOut` to `AdvancesTo`** (`advancesTo_of_out`): raft's quorum index `N`
  (`JCommittedIdx` with no outgoing half: `MajIdx ∅` is the top, so `N` is `IsQuorumIndex` of the voters,
  `isQuorumIndex_of_out`) is the specification's `AdvanceCommitIndex`'s: when `maybeCommit` commits, its
  `IsQuorum (listToSet C) (ackedBy …)` and maximality (`advanceCommitIndex_eq`); when it does not, a
  no-op (`advanceCommitIndex_noop`), which needs every `Match` within the log (`hm`: raft's `PrvalsOk`
  and the response's index, the caller's).
- **The line's pinned phases** (`CommitSrc`, `CommitTgt`, `phaseStepB_commitPin`): `phaseStepB_commit` with
  the share's server named, so that the facts (`fxPres_commit`) know the line's result up to `toC`.
- **The line's facts** (`fxPres_commit`): the specification's `AdvanceCommitIndex` at the leader
  (`AdvancesTo`), `quorumLogF_commit` (amendment A6) with the leader's server facts at the new commit
  index rebuilt from raft's ghost state after the commit (`srvFacts_leaderOf`: its log's records, the
  committed prefix and the commit certificate, its leadership and its term's full log, no pending entry),
  `specInv_advanceCommitIndex`, the bags and the logs unchanged; `simFx_congr` to the line's result.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadAccGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [GoSemanticsFunctions]

/-- A set whose elements are a permutation of `C` is `C`'s. -/
theorem gset_eq_listToSet {S : GSet w64} {C : List w64} (h : (GMap.elements S).Perm C) :
    S = GMap.listToSet C := by
  rw [← GMap.listToSet_elements S]
  apply GMap.set_eq
  intro x
  rw [GMap.elem_of_list_to_set, GMap.elem_of_list_to_set]
  exact h.mem_iff

theorem listToSet_ne_empty' {C : List w64} (h : C ≠ []) : GMap.listToSet C ≠ ∅ := by
  intro he
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil C h
  have h1 : x ∈ GMap.listToSet C := (GMap.elem_of_list_to_set _ _).2 hx
  rw [he] at h1
  exact (GMap.elem_of_empty x).1 h1

/-- **`Committed()` with no outgoing half** is the incoming half's quorum index. -/
theorem isQuorumIndex_of_out {c : CfgM} {Y : NState} {b : Bool} {N : w64}
    (h : maybeCommitOut c Y b N) (hout : c.outgoing = ∅) (hne : c.incoming ≠ ∅) :
    IsQuorumIndex c.incoming (pvsMatchAt Y.prvals) N := by
  obtain ⟨⟨N0, N1, H0, H1, HN⟩, -⟩ := h
  have hN1 : N1 = W64 (2 ^ 64 - 1) := H1.1 hout
  have hq := H0.2 hne
  have hN : N = N0 := by
    rw [HN]
    by_cases hlt : uint.Z N0 < uint.Z N1
    · simp only [hlt, ↓reduceIte]
    · simp only [hlt, ↓reduceIte]; rw [hN1]
      rw [hN1] at hlt
      have h1 : uint.Z (W64 (2 ^ 64 - 1)) = 2 ^ 64 - 1 := by word
      have h2 := uint_Z_lt N0
      have h3 : uint.Z N0 = 2 ^ 64 - 1 := by omega
      word
  rw [hN]; exact hq

/-- A quorum of the voters acknowledging `M` (`ackedBy`'s shape over the `Match` map) is a quorum of
the voters whose `Match` is at least `M` (`IsQuorumIndex`'s shape). -/
theorem isQuorum_filter_of_acked (S : GSet w64) (pvs : GMap w64 Progress) (M : w64)
    (H : IsQuorum S (domSet (GMap.filter (fun _ x => decide (uint.Z M ≤ uint.Z x)) (prvalsMatch pvs)))) :
    IsQuorum S (GMap.filter (fun v _ => decide (uint.Z M ≤ uint.Z (pvsMatchAt pvs v))) S) := by
  unfold IsQuorum at H ⊢
  have Hsub : domSet (GMap.filter (fun _ x => decide (uint.Z M ≤ uint.Z x)) (prvalsMatch pvs)) ∩ S ⊆
      GMap.filter (fun v _ => decide (uint.Z M ≤ uint.Z (pvsMatchAt pvs v))) S ∩ S := by
    rw [GMap.elem_of_subseteq]
    intro v Hv
    rw [GMap.elem_of_intersection] at Hv ⊢
    refine ⟨?_, Hv.2⟩
    have Hv1 := Hv.1
    rw [GMap.elem_of_dom] at Hv1
    obtain ⟨x, Hx⟩ := Hv1
    simp only [prvalsMatch, GMap.lookup_filter] at Hx
    change Option.filter _ ((pvs !! v).map Progress.matched) = _ at Hx
    cases E : pvs !! v with
    | none => rw [E] at Hx; simp at Hx
    | some p =>
      rw [E] at Hx
      simp only [Option.map_some, Option.filter] at Hx
      split at Hx
      · rename_i hle
        have hle' : uint.Z M ≤ uint.Z p.matched := of_decide_eq_true hle
        have Hv2 := Hv.2
        rw [GMap.mem_iff, GMap.lookup_filter]
        cases Hc : S !! v with
        | none => rw [GMap.mem_iff, Hc] at Hv2; simp at Hv2
        | some u =>
          simp only [Option.filter]
          have : pvsMatchAt pvs v = p.matched := by
            unfold pvsMatchAt pvsAcked
            change ((pvs !! v).map Progress.matched).getD (W64 0) = p.matched
            rw [E]; rfl
          rw [this]
          simp [hle']
      · simp at Hx
  have := GMap.subseteq_size Hsub
  omega

/-- `ackedBy` at a leader is over its `Progress` map's `Match` values. -/
theorem ackedBy_toPState (Y : NState) (hl : Y.role = .leader) (M : w64) :
    ackedBy (toPState Y) M =
      domSet (GMap.filter (fun _ x => decide (uint.Z M ≤ uint.Z x)) (prvalsMatch Y.prvals)) := by
  simp [ackedBy, toPState, hl]

/-- **The bridge from `maybeCommitOut` to `AdvancesTo`** (see the header): at a leader `Y` related to its
server `a`, with no outgoing half and every `Match` within the log, the specification's
`AdvanceCommitIndex` commits to the commit index after `maybeCommit`'s outcome. -/
theorem advancesTo_of_out (C : List w64) (hnd : C.Nodup) (c : CfgM) (Y : NState) (a : Etcdraft.Server)
    (b : Bool) (N : w64)
    (hR : SimServerR C C.length (toPState Y) a) (hl : Y.role = .leader) (hs : LogShapeOk C.length (toPState Y))
    (hin : c.incoming = GMap.listToSet C) (hout : c.outgoing = ∅) (hne : C ≠ [])
    (hT0 : Y.term ≠ W64 0)
    (hm : ∀ v x, prvalsMatch Y.prvals !! v = some x → uint.Z x ≤ (toPState Y).log.length)
    (h : maybeCommitOut c Y b N) :
    AdvancesTo a (uint.Z (commitAt Y b N).logst.committed) := by
  intro st i hsi
  rw [← hsi] at hR
  have hlp : (toPState Y).role = .leader := by rw [toPState_role, hl]; rfl
  have hq0 : IsQuorumIndex (GMap.listToSet C) (pvsMatchAt Y.prvals) N := by
    rw [← hin]; exact isQuorumIndex_of_out h hout (by rw [hin]; exact listToSet_ne_empty' hne)
  have hlen64 : (toPState Y).log.length < 2 ^ 64 := by
    have := lastIndex_plogLast C.length (toPState Y) hs
    have := uint_Z_lt (plogLast (toPState Y).base (toPState Y).log).index'
    omega
  have hmax : ∀ k : Nat, uint.Z N < k → k ≤ (toPState Y).log.length →
      ¬ IsQuorum (GMap.listToSet C) (ackedBy (toPState Y) (W64 k)) := by
    intro k hk hkl hQ
    rw [ackedBy_toPState Y hl] at hQ
    have hkz : uint.Z (W64 k) = k := by word
    exact hq0.2.2 (W64 k) (by rw [hkz]; exact hk) (isQuorum_filter_of_acked _ Y.prvals (W64 k) hQ)
  have hqN : 0 < uint.Z N → IsQuorum (GMap.listToSet C) (ackedBy (toPState Y) N) := by
    intro hpos
    rw [ackedBy_toPState Y hl, ← hin]
    rw [← hin] at hq0
    exact isQuorumIndex_acked' c.incoming Y.prvals N N hpos (Int.le_refl _) hq0
  have hb := h.2
  cases b with
  | true =>
    obtain ⟨-, hc, ht⟩ := hb.1 rfl
    have hrange := (plogTermAt_some_range _ _ _ _ ht).2
    have hn : uint.Z N ≤ (toPState Y).log.length := by
      have hb0 : uint.Z (toPState Y).base.index' = 0 := by rw [hs.1]; rfl
      simp only [plogLastIndexZ, toPState] at hrange hb0 ⊢
      omega
    have hpos : 0 < uint.Z N := by have := uint_Z_nonneg Y.logst.committed; omega
    exact advanceCommitIndex_eq st i C hnd C.length (toPState Y) hR hlp hs N hc hn ht (hqN hpos) hmax
  | false =>
    have hno : ¬ (uint.Z (toPState Y).commit < uint.Z N ∧
        plogTermAt (toPState Y).base (toPState Y).log N = some (toPState Y).term) := by
      rintro ⟨h1, h2⟩
      exact absurd (hb.2 ⟨hT0, h1, h2⟩) (by decide)
    have hN : uint.Z N ≤ (toPState Y).log.length := by
      obtain ⟨⟨v, -, hv⟩, -⟩ := hq0
      rw [← hv]
      unfold pvsMatchAt pvsAcked
      change uint.Z (((Y.prvals !! v).map Progress.matched).getD (W64 0)) ≤ _
      cases E : Y.prvals !! v with
      | none =>
        show uint.Z (W64 0) ≤ _
        have : uint.Z (W64 0) = 0 := rfl
        omega
      | some p =>
        show uint.Z p.matched ≤ _
        apply hm v p.matched
        simp only [prvalsMatch, GMap.fmap_eq, GMap.lookup_fmap]
        change (Y.prvals !! v).map Progress.matched = _
        rw [E]; rfl
    have H := advanceCommitIndex_noop st i C hnd C.length (toPState Y) hR hlp hs N hN hqN hmax hno
    rw [H, hR.2.2.2.2.2.2.1]
    rfl

end pure

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The `Commit` line's source phase, pinned**: the voters, the share's server `cs1` and the list named;
a leader's server whose `AdvanceCommitIndex` commits to `n`, so committed idle-related to `X`. -/
abbrev CommitSrc (X : NState) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) (n : Int) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = cs1 ∧ P = P0 ∧ ∃ a : Etcdraft.Server, toC (confAbs C) a = cs ∧
    a.state = Etcdraft.leader ∧ AdvancesTo a n ∧
    SimIdle C X (toC (confAbs C) { a with commitIndex := max a.commitIndex n }) P

/-- **The `Commit` line's target phase, pinned**: the share's server committed to `n`, idle at `X`. -/
abbrev CommitTgt (X : NState) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) (n : Int) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = { cs1 with commitIndex := max cs1.commitIndex n } ∧ P = P0 ∧ SimIdle C X cs P

/-- **The `Commit` line's phase step, pinned** (`phaseStepB_commit` with the share's server named). -/
theorem phaseStepB_commitPin (id : w64) (c : CfgM) (X : NState) (C0 : List w64) (cs1 : ServerC)
    (P0 : List Etcdraft.Msg) (n : Int) :
    PhaseStepB id c (NodeEvOf rsmCommit id X c) (CommitSrc X C0 cs1 P0 n) (CommitTgt X C0 cs1 P0 n) := by
  intro C cs P hΦ hc e he
  obtain ⟨hC0, hcs1, hP0, a0, hcs, hlead, hadv, a'', ha'', hR, hs, hP, bt, bc, bl⟩ := hΦ
  obtain ⟨hin, hout, hC⟩ := hc
  refine ⟨he.2.1, by rw [nodeEvOf_name_commit he]; decide, ?_⟩
  intro a ha
  have heq : toC (confAbs C) a0 = toC (confAbs C) a := hcs.trans ha.symm
  have hci : a0.commitIndex = a.commitIndex := congrArg ServerC.commitIndex heq
  have hc' : toC (confAbs C) { a0 with commitIndex := max a0.commitIndex n } =
      toC (confAbs C) { a with commitIndex := max a.commitIndex n } := by
    rw [toC_commitIndex, toC_commitIndex, heq, hci]
    try rfl
  have hcf : a''.config = a0.config := congrArg ServerC.config ha''
  have hcfg : a0.config.incoming = confAbs C := by rw [← hcf, hR.2.2.2.2.2.2.2.1]
  have hR' : SimServerR C C.length (toPState X) { a with commitIndex := max a.commitIndex n } :=
    simServerR_toC (ha''.trans hc') hR
  have hlead' : a.state = Etcdraft.leader := (congrArg ServerC.state heq).symm.trans hlead
  have hrole : X.role = .leader := by
    have h2 := hR'.2.1
    simp only at h2
    rw [hlead'] at h2
    cases hr : X.role <;> simp [toPState, proleRole, roleAbs, hr] at h2 <;> first | rfl | exact absurd h2 (by decide)
  have hac : a.commitIndex = cs.commitIndex := congrArg ServerC.commitIndex ha
  refine ⟨{ a with commitIndex := max a.commitIndex n }, [], ⟨hC0, ?_, by rw [List.append_nil]; exact hP0, ?_⟩,
    by simp, ?_⟩
  · rw [toC_commitIndex, hac, ha, hcs1]
  · rw [List.append_nil, ← hc']
    exact ⟨a'', ha'', hR, hs, hP, bt, bc, bl⟩
  · exact lineEffect_commit C e id X c a n _ he hin hout hC hlead' (advancesTo_toC heq hcfg hadv)
      hR' hs hrole bt bc bl

/-- **A leader's server facts from raft's ghost state** (`srvFacts_newLeader` with no pending entry): its
recorded log raft's `L`, its records, committed prefix and commit certificate, its leadership and its
term's full log. -/
theorem srvFacts_leaderOf (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) (L : List EntryM)
    (hl : v.state = Etcdraft.leader) (hlog : v.log = logAbs C C.length 1 L) (hbt : BootTerms C.length 1 L)
    (hwf : PlogWfR (entryID.mk (W64 0) (W64 0)) L) (hlen : L.length < 2 ^ 63) (hc0 : 0 ≤ v.commitIndex)
    (hcl : v.commitIndex ≤ L.length) (ht0 : 0 ≤ v.currentTerm) (ht63 : v.currentTerm < 2 ^ 63) :
    (logRecs γ base0 L ∗ isCommitted γ (L.take v.commitIndex.toNat) ∗
      commitIn γ L (W64 v.commitIndex) (W64 v.currentTerm) ∗ isLeader γ j (W64 v.currentTerm) ∗
      leadFull γ (W64 v.currentTerm) L : IProp GF) ⊢ srvFacts γ C j v := by
  unfold srvFacts
  simp only [hl, ↓reduceIte]
  iintro ⟨#Hr, #Hc, #Hci, #Hl, #Hf⟩
  iexists L, []
  isplitr
  · ipureintro
    simp only [List.append_nil]
    exact ⟨hlog, hbt, hwf, hlen, hc0, hcl, ht0, ht63, fun _ => trivial, fun e he => by cases he⟩
  isplitr
  · iexact Hr
  isplitr
  · iexact Hc
  isplitr
  · isplitr
    · iexact Hl
    isplitr
    · iexact Hf
    ileft; ipureintro; rfl
  · iexact Hci

/-- **The `Commit` line's facts** (see the header), at the pinned phases: raft's facts of the leader's log
at `X` (the state after the commit) are the caller's. -/
theorem fxPres_commit (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (X : NState) (C0 : List w64)
    (cs1 : ServerC) (P0 : List Etcdraft.Msg) (n : Int) (hidC : id ∈ C0) (hl : X.role = .leader)
    (hcl : uint.Z X.logst.committed ≤ (toPState X).log.length) :
    (logRecs γ base0 (toPState X).log ∗
      isCommitted γ ((toPState X).log.take (uint.Z X.logst.committed).toNat) ∗
      commitIn γ (toPState X).log X.logst.committed X.term ∗ isLeader γ id X.term ∗
      leadFull γ X.term (toPState X).log : IProp GF) ⊢
      FxPres γ id E (CommitSrc X C0 cs1 P0 n) (CommitTgt X C0 cs1 P0 n) := by
  iintro ⟨#Hr, #Hcm, #Hci, #Hl, #Hf⟩
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, a0, hcs0, -, hadv0, hI⟩, -, hca, ⟨-, hcs', hP', -⟩, -, hsrv, hσa, -, -, -⟩ := hpre
  have hP0 : P' = [] := by
    have := congrArg List.length hP'; rw [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hP0
  obtain ⟨a1, ha1, hR1, hs1, -, bt, bc, bl⟩ := hI
  have heq : toC (confAbs C) a0 = toC (confAbs C) a := hcs0.trans hca.symm
  have hci : a0.commitIndex = a.commitIndex := congrArg ServerC.commitIndex heq
  have hcf : a1.config = a0.config := congrArg ServerC.config ha1
  have hcfg : a0.config.incoming = confAbs C := by rw [← hcf, hR1.2.2.2.2.2.2.2.1]
  have hadv : AdvancesTo a n := advancesTo_toC heq hcfg hadv0
  have hstep : σ.advanceCommitIndex (idAbs id) = some (σ.commitTo (idAbs id) n) := hadv σ (idAbs id) hσa
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  -- the new server, related to `X`
  have hv : toC (confAbs C) a1 = toC (confAbs C) { a with commitIndex := max a.commitIndex n } := by
    rw [ha1, toC_commitIndex, toC_commitIndex, heq, hci]
    try rfl
  have hRv : SimServerR C C.length (toPState X) { a with commitIndex := max a.commitIndex n } :=
    simServerR_toC hv hR1
  have hs' : ∀ k, (σ.commitTo (idAbs id) n).s k =
      if k = idAbs id then { a with commitIndex := max a.commitIndex n } else σ.s k := by
    intro k; rw [← hσa]; rfl
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  icases allFacts_oneLeader γ C σ hsrv $$ Hal with %hone
  -- every voter's facts after the commit: the leader's from raft's
  ihave #Hal' : allFacts γ C (σ.commitTo (idAbs id) n) $$ []
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %j %hj
    rw [hs']
    by_cases hji : idAbs j = idAbs id
    · rw [if_pos hji]
      have := idAbs_inj hji
      subst this
      have hT : ({ a with commitIndex := max a.commitIndex n } : Etcdraft.Server).currentTerm = uint.Z X.term :=
        hRv.1
      have hC : ({ a with commitIndex := max a.commitIndex n } : Etcdraft.Server).commitIndex =
          uint.Z X.logst.committed := hRv.2.2.2.2.2.2.1
      have hlen : (toPState X).log.length < 2 ^ 63 := by
        have h1 := plastIndex_length _ _ hs1
        omega
      iapply srvFacts_leaderOf γ C j _ (toPState X).log
        (by rw [hRv.2.1]; simp [toPState, hl, proleRole, roleAbs]) hRv.2.2.2.2.2.1
        (fun k e hk he => hs1.2.2 k e (by omega) he)
        (by have h := PlogWf_wfR _ _ hs1.2.1; rw [hs1.1] at h; exact h) hlen
        (by rw [hC]; exact uint_Z_nonneg _) (by rw [hC]; exact hcl)
        (by rw [hT]; exact uint_Z_nonneg _) (by rw [hT]; exact bt)
      have hWT : W64 ({ a with commitIndex := max a.commitIndex n } : Etcdraft.Server).currentTerm = X.term := by
        rw [hT]; simp
      have hWC : W64 ({ a with commitIndex := max a.commitIndex n } : Etcdraft.Server).commitIndex =
          X.logst.committed := by
        rw [hC]; simp
      rw [hWT, hWC, hC]
      iframe Hr Hcm Hci Hl Hf
    · rw [if_neg hji]
      iapply Hal $$ %j %hj
  icases quorumLogF_commit γ C σ (σ.commitTo (idAbs id) n) (idAbs id) hsrv hi hsi hstep $$ [$Htbl $Hal' $Hq]
    with ⟨Htbl, #Hq'⟩
  have hsi' := TraceSpecInv.specInv_advanceCommitIndex hsi hi hone hstep
  ihave #H1 : simFx γ C (σ.commitTo (idAbs id) n) $$ []
  · iunfold simFx
    iframe Hal' Hq'
    isplitl
    · imodintro
      iintro %x %hx
      iapply Hmf
      ipureintro; exact hx
    ipureintro
    refine ⟨hsi', msgsUniq_mono (fun x hx => hx) hu,
      msgsShape_of (σ := σ) rfl (fun x hx => hx) (fun j => by
        rw [hs']; split
        · rename_i h; subst h; rw [hσa]
        · rfl) hsh, ?_⟩
    refine appSlices_mono σ _ has rfl (fun m hm => hm) ?_
    intro j hj hlj
    left
    rw [hs'] at hlj ⊢
    split
    · rename_i h; subst h; rw [hσa]; rw [if_pos rfl] at hlj
      exact ⟨hlj, rfl, List.prefix_refl _⟩
    · rename_i h; rw [if_neg h] at hlj
      exact ⟨hlj, rfl, List.prefix_refl _⟩
  have hs : ∀ j, toC (σ.commitTo (idAbs id) n).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.commitTo (idAbs id) n).server ((σ.commitTo (idAbs id) n).s j) := by
    intro j
    rw [hs']
    show toC σ.server (if j = idAbs id then a' else σ.s j) =
      toC σ.server (if j = idAbs id then { a with commitIndex := max a.commitIndex n } else σ.s j)
    split
    · rw [hsrv, hcs', toC_commitIndex, ← hca]; rfl
    · rfl
  ihave #H3 := simFx_congr γ C (σ.commitTo (idAbs id) n)
    (withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H1
  iframe Htbl
  iexact H3

end facts

end EtcdGrove
end Perennial
