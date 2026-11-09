/-
Lean-first (no Rocq counterpart). Trace-check's S5 (2026-11-09, review round 4's D2,
`notes/trace-validation-reviews/s5-r4.md`): the sources of `specInv_becomeLeader`'s hypotheses
(`TraceSimSpecInv.lean`) at the `BecomeLeader` line, from what raft's `becomeLeader` can hold at its
hook (`traceBecomeLeader`, raft.go: after `reset` and the state change, before the empty entry's
append) together with the simulation's facts (`simFx`, `TracedHooksDraft.lean`).

What the new leader `i` of term `T` holds there (`becomeLeader_hyps`'s premises):
- `isLeader γ i T` and `isCamp γ i T F0`, its campaign log `F0` as long as its log in the
  specification's state, with `logRecs γ base0 F0`;
- its term map's authority `ghostMapAuth γm 1 terms` with no term log of `T`
  (`terms !! T = none`): no entry of `T` exists yet;
- the vote table `votesTbl γ`; the static `γ.reBoot ≠ []` (a bootstrapped cluster).

**Not what raft's ghost has today** (the report of D2): raft's ghost takes the win in one step,
`ownRaftGhost_step_win` (`Protocol/Refinement.lean`), after `stepCandidate` returns (`raft__Step/
MsgVoteResp.lean`): at the hook its ghost is still the candidate's, with `terms !! T = none`
(`TermsOk`) but no `isLeader γ i T`; after the step it has `isLeader` but also the term log, holding
the empty entry. Both halves are needed at once: the first half of the step (freezing the quorum in
`reWins`, `win_register`) must be taken before the hook, the second (the term log with the entry) at
the append, with `WinsOk` relaxed for a candidate whose win is registered.

And `hents`, which no fact of the simulation gives (`specInv_becomeLeader`'s `hfreshMsg` needs it):
a message carrying entries is an append request with its entries' indices below `2 ^ 64`. Neither
`msgFacts` (`True` for every other type; an append request's records only in range) nor `SpecInv`
says so; raft has it of every message it sends (`msgAbs`: only `MsgApp` carries entries; their
indices are `w64`s), so it belongs in `msgFacts`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksDraft

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section facts
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- An in-range entry of a log with records has a record. -/
theorem logRecs_isEntry (γ : RaftNames) (b : entryID) (es : List EntryM) (k : Nat) (e : EntryM)
    (Hk : es[k]? = some e) (Hr : uint.Z b.index' + (k : Int) + 1 < 2 ^ 64) :
    logRecs (GF := GF) γ b es ⊢ ∃ pt, isEntryR γ e pt := by
  unfold logRecs
  refine (BigSepL.bigSepL_lookup Hk).trans ?_
  simp only [Hr, ite_true]
  iintro ⟨%pt, -, #H⟩
  iexists pt; iexact H

/-- **No entry of a registered leader's term before its term log**: with `isLeader γ i T` and `i`'s
term map without `T`, no record is of an entry of `T` (a leader's entry names its leader's term log;
a boot entry is of term `1`, and a leader is of a term `≥ 2`, `isLeader_boot`). -/
theorem isEntryR_term_ne (γ : RaftNames) (i T : w64) (γm : GName) (terms : GMap w64 TermRec)
    (hγm : γ.reTerms !! i = some γm) (hfree : terms !! T = none) (e : EntryM) (pt : w64) :
    ⊢ isLeader (GF := GF) γ i T -∗ ghostMapAuth γm 1 terms -∗ isEntryR γ e pt -∗ ⌜e.Term' ≠ T⌝ := by
  iintro #Hl Ha #He
  unfold isEntryR
  icases He with (⟨%ldr, %γt, %b, %l0, %F0, #Hl', #Htl, -⟩ | ⟨%Hb, -⟩)
  · by_cases ht : e.Term' = T
    · rw [ht]
      icases isLeader_unique γ i ldr T $$ Hl Hl' with %Hid
      subst Hid
      unfold isTermLog
      icases Htl with ⟨%γm', %Hγm', #Hf⟩
      rw [hγm] at Hγm'
      cases Hγm'
      icases ghost_map_lookup $$ Ha Hf with %Hlk
      exfalso
      rw [hfree] at Hlk
      cases Hlk
    · ipureintro; exact ht
  · obtain ⟨-, h2, h3, -⟩ := Hb
    have hne : γ.reBoot ≠ [] := by intro h; rw [h] at h2; simp at h2
    icases isLeader_boot γ i T $$ Hl with %H2
    have := H2 hne
    ipureintro
    rw [h3]; intro h; rw [← h] at this; revert this; decide

/-- **A commit index within a new leader's campaign log** (the campaign form of
`commit_in_leader_cert`, for a leader without a term log yet, so without `leadFull`): a commit
certificate of a term `tm ≤ T` is within the campaign log `F0` of `T`'s leader `i` when `i` has no
term log of `T` (bootstrap: `F0` starts with the bootstrap log; a commit fact of `T`: its log has an
entry of `T`, which has a record, `isEntryR_term_ne`; an earlier term: `lc_core`). -/
theorem commit_le_camp (γ : RaftNames) (es F0 : List EntryM) (c tm T i : w64) (γm : GName)
    (terms : GMap w64 TermRec) (hγm : γ.reTerms !! i = some γm) (hfree : terms !! T = none)
    (htm : uint.Z tm ≤ uint.Z T) :
    ⊢ votesTbl (GF := GF) γ -∗ commitIn γ es c tm -∗ isLeader γ i T -∗ isCamp γ i T F0 -∗
      logRecs γ base0 F0 -∗ ghostMapAuth γm 1 terms -∗ ⌜uint.Z c ≤ F0.length⌝ := by
  iintro Htbl #Hci #Hl #Hc #HrF Ha
  icases isCamp_ok γ i T F0 $$ Hc with %Hcok
  have HlenF : plogLastIndexZ base0 F0 = (F0.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  ihave #Hcj := commitIn_j γ es c tm $$ Hci
  unfold commitJ
  icases Hcj with (%Hb0 | ⟨%t, %n, %G, #Hq, %Hcn⟩)
  · icases isCamp_boot γ i T F0 $$ Hc with %Hb
    have := Hb.1.length_le
    ipureintro; omega
  obtain ⟨Hcn, Htt, -⟩ := Hcn
  by_cases hn0 : uint.Z n = 0
  · ipureintro; omega
  by_cases hT : t = T
  · -- a commit fact of `T`: an entry of `T` with a record
    subst hT
    icases cq_base γ t n G $$ Hq with ⟨%HGn, #HGl⟩
    icases leadFull_wf γ t G $$ HGl with ⟨%HwG, #HrG⟩
    have hn1 : 0 < uint.Z n := by have := uint_Z_nonneg n; omega
    rw [show base0 = entryID.mk (W64 0) (W64 0) from rfl, plogTermAt_base0 G n hn1] at HGn
    obtain ⟨x, hx, hxt⟩ : ∃ x, G[uint.nat n - 1]? = some x ∧ x.Term' = t := by
      cases h : G[uint.nat n - 1]? with
      | none => rw [h] at HGn; cases HGn
      | some x => rw [h] at HGn; exact ⟨x, rfl, Option.some.inj HGn⟩
    have hk : uint.nat n - 1 < G.length := (List.getElem?_eq_some_iff.mp hx).1
    icases logRecs_isEntry γ base0 G _ x hx (by
        rw [base0_index]
        have h1 := uint_Z_lt n
        have h2 : ((uint.nat n : Nat) : Int) = uint.Z n := by word
        omega)
      $$ HrG with ⟨%pt, #He⟩
    icases isEntryR_term_ne γ i t γm terms hγm hfree x pt $$ Hl Ha He with %Hne
    exact absurd hxt Hne
  · -- an earlier term: `lc_core` puts its index within `F0`
    have Hlt : uint.Z t < uint.Z T := by
      have : uint.Z t ≠ uint.Z T := fun h => hT (uint_Z_inj.mp h)
      omega
    have Hcl := camp_last T F0 Hcok
    icases lc_core γ ((uint.Z T).toNat + 1) T t n G i F0 F0
        (by have := uint_Z_nonneg T; omega) Hlt Hcok.1 Hcl
        $$ Htbl Hq Hl Hc HrF with %HnF
    have := (plogTermAt_some_range _ _ _ _ HnF).2
    ipureintro; omega

end facts

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`specInv_becomeLeader`'s hypotheses at the `BecomeLeader` line** (review round 4's D2), `σ` the
specification's state before the line, `i` its candidate of term `T` (the new leader):
- `hfreshLog`: a log's entry is recorded (its record names `T`'s leader `i`'s term log, which does not
  exist, `isEntryR_term_ne`) or a leader's pending one, of that leader's term (`srvFacts`): a leader
  of `T` is `i` (`isLeader_unique`), a candidate in `σ`;
- `hfreshMsg`: a message's entry is an append request's (`hents`) with a record (`msgFacts`, in range
  by `hents`), not of `T` (`isEntryR_term_ne`), or at a bootstrap position, of term `1`, below a
  leader's term (`isLeader_boot`, with `hboot`);
- `hfreshReq`: an append request of `T` is from `T`'s leader (`msgFacts`), `i`, which as a candidate
  has none of its term out (`CandS`);
- `hcw`: a server of `T` has its commit index within `F0` (`commit_le_camp`), as long as `i`'s log
  (`hF0`). -/
theorem becomeLeader_hyps (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : w64)
    (F0 : List EntryM) (γm : GName) (terms : GMap w64 TermRec)
    (hsrv : σ.server = confAbs C) (hiC : i ∈ C)
    (hcand : (σ.s (idAbs i)).state = Etcdraft.candidate) (hspec : TraceSpecInv.SpecInv σ)
    (hF0 : (σ.s (idAbs i)).log.length = F0.length)
    (hγm : γ.reTerms !! i = some γm) (hfree : terms !! W64 (σ.s (idAbs i)).currentTerm = none)
    (hboot : γ.reBoot ≠ [])
    (hents : ∀ m ∈ TraceSpecInv.msgs σ, m.entries ≠ [] →
      m.type = .appendEntriesRequest ∧ m.prevLogIndex + m.entries.length < 2 ^ 64) :
    ⊢ votesTbl (GF := GF) γ -∗ allFacts γ C σ -∗
      (□ ∀ m, ⌜m ∈ σ.messages.domain ++ σ.pendingMessages.domain⌝ → msgFacts γ C m) -∗
      isLeader γ i (W64 (σ.s (idAbs i)).currentTerm) -∗
      isCamp γ i (W64 (σ.s (idAbs i)).currentTerm) F0 -∗ logRecs γ base0 F0 -∗
      ghostMapAuth γm 1 terms -∗
      ⌜(∀ j ∈ σ.server, ∀ e ∈ (σ.s j).log, e.term ≠ (σ.s (idAbs i)).currentTerm) ∧
        (∀ m ∈ TraceSpecInv.msgs σ, ∀ e ∈ m.entries, e.term ≠ (σ.s (idAbs i)).currentTerm) ∧
        (∀ m ∈ TraceSpecInv.msgs σ, m.type = .appendEntriesRequest →
          m.term ≠ (σ.s (idAbs i)).currentTerm) ∧
        (∀ k ∈ σ.server, (σ.s k).currentTerm = (σ.s (idAbs i)).currentTerm →
          (σ.s k).commitIndex ≤ (σ.s (idAbs i)).log.length)⌝ := by
  iintro Htbl #Hal #Hmf #Hl #Hc #HrF Ha
  generalize hT : (σ.s (idAbs i)).currentTerm = T at hfree ⊢
  iunfold allFacts at Hal
  -- `T`'s range, from `i`'s facts
  ihave Hfi := Hal $$ %i %hiC
  iunfold srvFacts at Hfi
  icases Hfi with ⟨%esi, %pdi, %Hpi, -⟩
  obtain ⟨-, -, -, -, -, -, hT0, hT1, -⟩ := Hpi
  rw [hT] at hT0 hT1
  have hTZ : uint.Z (W64 T) = T := by word
  have hiS : idAbs i ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C i).2 hiC
  -- `T ≥ 2`: a leader's term, with a bootstrap log
  icases isLeader_boot γ i (W64 T) $$ Hl with %HT2
  have hT2 : 2 ≤ T := by have := HT2 hboot; omega
  -- (1) `hfreshLog`
  ihave %h1 : ⌜∀ j ∈ σ.server, ∀ e ∈ (σ.s j).log, e.term ≠ T⌝ $$ [Ha]
  · by_cases hc : ∀ j ∈ σ.server, ∀ e ∈ (σ.s j).log, e.term ≠ T
    · ipureintro; exact hc
    simp only [Classical.not_forall, Classical.not_not, ne_eq] at hc
    obtain ⟨x, hx, e, he, het⟩ := hc
    rw [hsrv] at hx
    obtain ⟨j, hj, rfl⟩ := mem_confAbs_inv C x hx
    ihave Hfj := Hal $$ %j %hj
    iunfold srvFacts at Hfj
    icases Hfj with ⟨%es, %pd, %Hp, #Hr, -, #Hld, -⟩
    obtain ⟨hlog, hbt, -, hlen, -, -, hTj0, hTj1, hpl, hpt⟩ := Hp
    obtain ⟨k, hk⟩ := List.getElem?_of_mem he
    rw [hlog, logAbs_getElem?] at hk
    obtain ⟨y, hy, rfl⟩ : ∃ y, (es ++ pd)[k]? = some y ∧ entAbs C C.length (1 + k) y = e := by
      cases h : (es ++ pd)[k]? with
      | none => rw [h] at hk; cases hk
      | some y => rw [h] at hk; exact ⟨y, rfl, Option.some.inj hk⟩
    rw [entAbs_term C C.length (1 + k) y (fun h => hbt k y h hy)] at het
    have hyT : y.Term' = W64 T := by rw [← het]; word
    have hkl : k < (es ++ pd).length := (List.getElem?_eq_some_iff.mp hy).1
    rw [List.length_append] at hkl hlen
    by_cases hke : k < es.length
    · -- recorded: its record names `T`'s term log
      rw [List.getElem?_append_left hke] at hy
      icases logRecs_isEntry γ base0 es k y hy (by rw [base0_index]; omega) $$ Hr with ⟨%pt, #He⟩
      icases isEntryR_term_ne γ i (W64 T) γm terms hγm hfree y pt $$ Hl Ha He with %Hne
      exact absurd hyT Hne
    · -- pending: `j` leads `T`
      have hpd : pd ≠ [] := by intro h; rw [h] at hkl; simp at hkl; omega
      have hjl : (σ.s (idAbs j)).state = Etcdraft.leader := Classical.byContradiction fun h => hpd (hpl h)
      rw [List.getElem?_append_right (by omega)] at hy
      have hyj := hpt y (List.mem_of_getElem? hy)
      rw [hyT] at hyj
      have hTj : T = (σ.s (idAbs j)).currentTerm := w64_of_int_inj _ _ hT0 hT1 hTj0 hTj1 hyj
      simp only [hjl, ite_true]
      icases Hld with ⟨#HLj, -⟩
      rw [← hTj]
      icases isLeader_unique γ i j (W64 T) $$ Hl HLj with %Hij
      subst Hij
      rw [hcand] at hjl; exact absurd hjl TraceSpecInv.candidate_ne_leader
  -- (2) `hfreshReq`
  ihave %h3 : ⌜∀ m ∈ TraceSpecInv.msgs σ, m.type = .appendEntriesRequest → m.term ≠ T⌝ $$ []
  · by_cases hc : ∀ m ∈ TraceSpecInv.msgs σ, m.type = .appendEntriesRequest → m.term ≠ T
    · ipureintro; exact hc
    simp only [Classical.not_forall, Classical.not_not, ne_eq] at hc
    obtain ⟨m, hm, hty, hmt⟩ := hc
    ihave Hm := Hmf $$ %m %hm
    iunfold msgFacts at Hm
    simp only [hty, ↓reduceIte]
    icases Hm with ⟨%src, %es, %hpm, #HLs, -⟩
    have hsrc := hpm.1
    rw [hmt]
    icases isLeader_unique γ i src (W64 T) $$ Hl HLs with %Hij
    subst Hij
    have := (hspec.2.2.2.1 (idAbs i) hiS hcand).1 m hm hsrc hty
    rw [hT, hmt] at this
    exact absurd this (Int.lt_irrefl _)
  -- (3) `hfreshMsg`
  ihave %h2 : ⌜∀ m ∈ TraceSpecInv.msgs σ, ∀ e ∈ m.entries, e.term ≠ T⌝ $$ [Ha]
  · by_cases hc : ∀ m ∈ TraceSpecInv.msgs σ, ∀ e ∈ m.entries, e.term ≠ T
    · ipureintro; exact hc
    simp only [Classical.not_forall, Classical.not_not, ne_eq] at hc
    obtain ⟨m, hm, e, he, het⟩ := hc
    have hne : m.entries ≠ [] := List.ne_nil_of_mem he
    obtain ⟨hty, hrng⟩ := hents m hm hne
    have hprev : 0 ≤ m.prevLogIndex := hspec.2.2.2.2.1 m hm hne
    ihave Hm := Hmf $$ %m %hm
    iunfold msgFacts at Hm
    simp only [hty, ↓reduceIte]
    icases Hm with ⟨%src, %es, %hpm, -, #Hr⟩
    have hme := hpm.2
    obtain ⟨k, hk⟩ := List.getElem?_of_mem he
    have hkm : k < m.entries.length := (List.getElem?_eq_some_iff.mp hk).1
    rw [hme, logAbs_getElem?] at hk
    obtain ⟨y, hy, rfl⟩ : ∃ y, es[k]? = some y ∧
        entAbs C C.length (m.prevLogIndex.toNat + 1 + k) y = e := by
      cases h : es[k]? with
      | none => rw [h] at hk; cases hk
      | some y => rw [h] at hk; exact ⟨y, rfl, Option.some.inj hk⟩
    unfold entAbs at het
    split at het
    · -- a bootstrap position: term `1`
      exfalso; simp only at het; omega
    · simp only at het
      have hyT : y.Term' = W64 T := by rw [← het]; word
      have hpz : uint.Z (W64 m.prevLogIndex) = m.prevLogIndex := by word
      icases logRecs_isEntry γ _ es k y hy (by simp only; rw [hpz]; omega) $$ Hr with ⟨%pt, #He⟩
      icases isEntryR_term_ne γ i (W64 T) γm terms hγm hfree y pt $$ Hl Ha He with %Hne
      exact absurd hyT Hne
  -- (4) `hcw`
  ihave %h4 : ⌜∀ k ∈ σ.server, (σ.s k).currentTerm = T → (σ.s k).commitIndex ≤ (σ.s (idAbs i)).log.length⌝
      $$ [Htbl Ha]
  · by_cases hc : ∀ k ∈ σ.server, (σ.s k).currentTerm = T →
        (σ.s k).commitIndex ≤ (σ.s (idAbs i)).log.length
    · ipureintro; exact hc
    simp only [Classical.not_forall] at hc
    obtain ⟨x, hx, hxT, hlt⟩ := hc
    rw [hsrv] at hx
    obtain ⟨k, hk, rfl⟩ := mem_confAbs_inv C x hx
    ihave Hfk := Hal $$ %k %hk
    iunfold srvFacts at Hfk
    icases Hfk with ⟨%es, %pd, %Hp, -, -, -, #Hci⟩
    obtain ⟨-, -, -, hlen, hc0, hc1, -, -, -⟩ := Hp
    rw [hxT]
    icases commit_le_camp γ es F0 (W64 (σ.s (idAbs k)).commitIndex) (W64 T) (W64 T) i γm terms hγm
        hfree (Int.le_refl _) $$ Htbl Hci Hl Hc HrF Ha with %Hle
    rw [List.length_append] at hlen
    have hcZ : uint.Z (W64 (σ.s (idAbs k)).commitIndex) = (σ.s (idAbs k)).commitIndex := by word
    exfalso; apply hlt; rw [hF0]; omega
  ipureintro
  exact ⟨h1, h2, h3, h4⟩

end ghost

end EtcdGrove
end Perennial
