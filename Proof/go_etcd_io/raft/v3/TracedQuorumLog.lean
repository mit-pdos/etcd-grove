/-
Lean-first (no Rocq counterpart). **Amendment A5 (Q21): `QuorumLogF`'s sufficiency** (2026-11-11,
trace-check, `notes/decisions.md`, "Amendment A5 (Q21)"). Raft-internal (not on `etc/api/raft.txt`).
Sufficiency at the level of lemmas: no path proof calls them yet (the accepted `MsgApp`'s path waits on
slice 22b's other pieces).

The amended clause (`TracedCap.lean`): every server's committed prefix `P` is kept from a term `t` on
(`KeptFrom`: the servers holding `P` at a term `≥ t` are a quorum), `t` a term `P` was committed at or
after (`CommitCert`: raft's `commitJ` at `t`).

**An accepted append request's receive line keeps it** (task 3 of Q8 stage 1's slice 22b, the blocker
of Q21), round by round of the specification's `AcceptAppendEntriesRequest` at a server of the
request's term:
- a truncation (`ConflictAppendEntriesRequest`, the last entry dropped while the request conflicts:
  together the rounds are raft's `maybeAppend` truncating at `findConflict`'s first conflict),
  `quorumLogF_conflict`. A receiver at a term `≥ t` holding `P` keeps it: the request, of its term, agrees
  with `P` (`commitCert_app`: the receiver's raft facts of the request, `isMessage`'s `leadPrefix` and
  `lpfull`, make its entries a slice of its leader's full log of its term, which raft's leader completeness,
  `lc_core`, puts the certificate's commit quorum's log in: `commitJ_leadFull`), so its conflict is past
  `P` (`keptFrom_conflict`). A receiver below `t` is not counted. The vote table, which `lc_core` needs and
  which is not persistent, is used once per server (`votesTbl_forall_list`);
- the append (`NoConflictAppendEntriesRequest`), `quorumLogF_noConflict`;
- the reply with the raised commit index (`AppendEntriesAlreadyDone`), `quorumLogF_alreadyDone`: the
  receiver's new committed prefix is a prefix of the sender's, whose witness it takes.

Besides, a leader's log growing (`Replicate`, `ClientRequest`): `quorumLogF_grow`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksGlobal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **A conflict past the previous entry**: `HasNoConflict` false at an index within the log's end
names an entry of the request and a position of the log, their terms different. -/
theorem conflict_pos {σ : Etcdraft.State} {r : Etcdraft.ID} {p : Int} {ents : List Etcdraft.Entry}
    (hp0 : 0 ≤ p) (hple : p ≤ (σ.s r).log.length)
    (h : σ.hasNoConflict r (p + 1) ents = false) :
    ∃ k e, ents[k]? = some e ∧ p.toNat + k < (σ.s r).log.length ∧
      ((σ.s r).log[p.toNat + k]?).map Etcdraft.Entry.term ≠ some e.term := by
  unfold Etcdraft.State.hasNoConflict at h
  dsimp only at h
  have h1 : decide (p + 1 ≤ ((σ.s r).log.length : Int) + 1) = true := by simp; omega
  rw [h1, Bool.true_and, List.all_eq_false] at h
  obtain ⟨k, hk, hf⟩ := h
  rw [List.mem_range] at hk
  rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hf
  obtain ⟨hle, hne⟩ := hf
  simp only [Bool.not_eq_false', decide_eq_true_eq] at hle
  simp only [beq_eq_false_iff_ne] at hne
  have hidx : (p + 1 + (k : Int) - 1).toNat = p.toNat + k := by omega
  rw [hidx, List.getElem?_eq_getElem hk] at hne
  exact ⟨k, _, List.getElem?_eq_getElem hk, by omega, by simpa using hne⟩

/-- **`ConflictAppendEntriesRequest`'s round** (the specification's truncation): the request conflicts
past the commit index, and the receiver's last entry is dropped. -/
theorem conflictRound_eq {σ σ' : Etcdraft.State} {r : Etcdraft.ID} {index : Int} {m : Etcdraft.Msg}
    (h : σ.conflictAppendEntriesRequest r index m = .ok (some σ')) :
    index > (σ.s r).commitIndex ∧ σ.hasNoConflict r index m.entries = false ∧
      σ' = σ.upd r (fun v => { v with log := (σ.s r).log.take ((σ.s r).log.length - 1) }) := by
  unfold Etcdraft.State.conflictAppendEntriesRequest at h
  by_cases hc : (!m.entries.isEmpty && decide (index > (σ.s r).commitIndex) &&
      !σ.hasNoConflict r index m.entries) = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    have hs := subSeqM_init (σ.s r).log
    simp only [bind, Except.bind, hs, Pure.pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    exact ⟨hc.1.2, hc.2, h.symm⟩
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.not_false, ↓reduceIte, Pure.pure, Except.pure, Except.ok.injEq] at h
    cases h

/-- (Amendment A5) An append request **agrees with `P`** at every position both have an entry (its
`k`-th entry at index `prevLogIndex + k + 1`). -/
def AppAgrees (P : List Etcdraft.Entry) (m : Etcdraft.Msg) : Prop :=
  ∀ (k : Nat) (e : Etcdraft.Entry), m.entries[k]? = some e → m.prevLogIndex.toNat + k < P.length →
    P[m.prevLogIndex.toNat + k]? = some e

/-- **A truncation keeps `KeptFrom`** (amendment A5's point): at a server `r` of the request's term,
the request's previous entry within `r`'s log, a server holding `P` at a term `≥ t` — `r` among them —
keeps it, given that a request of a term `≥ t` agrees with `P` (`hag`; the receiver's raft facts of the
request give it, `commitCert_app`): the conflict is then past `P`, and so is the dropped last entry. A
server below `t` (the truncating receiver of `notes/decisions.md`, "Q8 stage 1 (slice 22b)", holding `P`
by coincidence) is not counted. The other servers are unchanged. -/
theorem keptFrom_conflict {σ σ' : Etcdraft.State} {r : Etcdraft.ID} {m : Etcdraft.Msg}
    {P : List Etcdraft.Entry} {t : Int} (hterm : m.term = (σ.s r).currentTerm)
    (hp0 : 0 ≤ m.prevLogIndex) (hple : m.prevLogIndex ≤ (σ.s r).log.length)
    (hstep : σ.conflictAppendEntriesRequest r (m.prevLogIndex + 1) m = .ok (some σ'))
    (hag : t ≤ m.term → AppAgrees P m) (h : KeptFrom σ P t) : KeptFrom σ' P t := by
  obtain ⟨-, hnc, rfl⟩ := conflictRound_eq hstep
  obtain ⟨k, e, he, hkl, hne⟩ := conflict_pos hp0 hple hnc
  have hs : ∀ j, (σ.upd r (fun v => { v with log := (σ.s r).log.take ((σ.s r).log.length - 1) })).s j =
      if j = r then { σ.s r with log := (σ.s r).log.take ((σ.s r).log.length - 1) } else σ.s j := by
    intro j; unfold Etcdraft.State.upd; rfl
  refine keptFrom_of (σ := σ) rfl ?_ h
  intro j _ hpj htj
  rw [hs]
  by_cases hj : j = r
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hj)]
    rw [hj] at hpj htj
    refine ⟨?_, htj⟩
    -- the conflict is past `P`: the request agrees with `P` where both have an entry
    have hag' := hag (by rw [hterm]; exact htj)
    have hPk : P.length ≤ m.prevLogIndex.toNat + k := by
      apply Nat.le_of_not_lt; intro hlt
      have h1 := hag' k e he hlt
      rw [← prefix_getElem?_of_lt hpj hlt, h1] at hne
      exact hne rfl
    show P <+: (σ.s r).log.take ((σ.s r).log.length - 1)
    have hP : P = (σ.s r).log.take P.length := List.prefix_iff_eq_take.mp hpj
    have := List.take_prefix P.length ((σ.s r).log.take ((σ.s r).log.length - 1))
    rw [List.take_take, Nat.min_eq_left (by omega), ← hP] at this
    exact this
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]; exact ⟨hpj, htj⟩

/-- A truncation keeps every committed prefix: the conflict is past the commit index. -/
theorem committedL_conflict {σ σ' : Etcdraft.State} {r : Etcdraft.ID} {m : Etcdraft.Msg}
    (hp0 : 0 ≤ m.prevLogIndex) (hple : m.prevLogIndex ≤ (σ.s r).log.length)
    (hstep : σ.conflictAppendEntriesRequest r (m.prevLogIndex + 1) m = .ok (some σ')) (k : Etcdraft.ID) :
    committedL σ' k = committedL σ k := by
  obtain ⟨hgt, hnc, rfl⟩ := conflictRound_eq hstep
  obtain ⟨j, e, -, hkl, -⟩ := conflict_pos hp0 hple hnc
  unfold committedL Etcdraft.State.upd
  simp only
  split
  · rename_i hk; subst hk
    simp only
    rw [List.take_take]
    congr 1; omega
  · rfl

/-- **`NoConflictAppendEntriesRequest`'s round** (the append): the request does not conflict, reaches
past the log, and its entries past the log are appended. -/
theorem noConflictRound_eq {σ σ' : Etcdraft.State} {r : Etcdraft.ID} {index : Int} {m : Etcdraft.Msg}
    (h : σ.noConflictAppendEntriesRequest r index m = .ok (some σ')) :
    index > (σ.s r).commitIndex ∧ σ.hasNoConflict r index m.entries = true ∧
      ∃ suffix, σ' = σ.upd r (fun v => { v with log := (σ.s r).log ++ suffix }) := by
  unfold Etcdraft.State.noConflictAppendEntriesRequest at h
  by_cases hc : (!m.entries.isEmpty && decide (index > (σ.s r).commitIndex) &&
      σ.hasNoConflict r index m.entries &&
      decide (m.prevLogIndex + (m.entries.length : Int) > ((σ.s r).log.length : Int))) = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨hc.1.1.2, hc.1.2, ?_⟩
    cases hs : Etcdraft.subSeqM m.entries (((σ.s r).log.length : Int) - index + 2) (m.entries.length : Int) with
    | error err => simp [hs, bind, Except.bind] at h
    | ok suffix =>
      simp only [hs, bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      exact ⟨suffix, h.symm⟩
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.not_false, ↓reduceIte, Pure.pure, Except.pure, Except.ok.injEq] at h
    cases h

/-- **An append keeps `KeptFrom`**: the receiver's log only grows; nothing else changes. -/
theorem keptFrom_noConflict {σ σ' : Etcdraft.State} {r : Etcdraft.ID} {index : Int} {m : Etcdraft.Msg}
    {P : List Etcdraft.Entry} {t : Int}
    (hstep : σ.noConflictAppendEntriesRequest r index m = .ok (some σ'))
    (h : KeptFrom σ P t) : KeptFrom σ' P t := by
  obtain ⟨-, -, suffix, rfl⟩ := noConflictRound_eq hstep
  have hs : ∀ j, (σ.upd r (fun v => { v with log := (σ.s r).log ++ suffix })).s j =
      if j = r then { σ.s r with log := (σ.s r).log ++ suffix } else σ.s j := by
    intro j; unfold Etcdraft.State.upd; rfl
  refine keptFrom_of (σ := σ) rfl ?_ h
  intro j _ hpj htj
  rw [hs]; split
  · rename_i hj; subst hj; exact ⟨hpj.trans (List.prefix_append _ _), htj⟩
  · exact ⟨hpj, htj⟩

/-- An append keeps every committed prefix: the commit index is below the request's index, at most
one past the log's end. -/
theorem committedL_noConflict {σ σ' : Etcdraft.State} {r : Etcdraft.ID} {index : Int} {m : Etcdraft.Msg}
    (hstep : σ.noConflictAppendEntriesRequest r index m = .ok (some σ')) (k : Etcdraft.ID) :
    committedL σ' k = committedL σ k := by
  obtain ⟨hgt, hnc, suffix, rfl⟩ := noConflictRound_eq hstep
  have hil : index ≤ ((σ.s r).log.length : Int) + 1 := by
    unfold Etcdraft.State.hasNoConflict at hnc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hnc
    exact hnc.1
  unfold committedL Etcdraft.State.upd
  simp only
  split
  · rename_i hk; subst hk
    simp only
    rw [List.take_append_of_le_length (by omega)]
  · rfl


/-- **An append request agrees with a committed prefix** when its entries are a slice, from its
previous index on, of a log `G'` whose raft terms agree with the prefix's log `es` up to the commit
index `c` wherever `G'` reaches. -/
theorem appAgrees_of_terms (C : List w64) (P : List Etcdraft.Entry) (es G' ents : List EntryM) (c idx : Nat)
    (hP : P <+: logAbs C C.length 1 (es.take c)) (hc : c ≤ es.length)
    (hsl : ents <+: G'.drop idx)
    (hT : ∀ q, q < c → q < G'.length → G'[q]?.map EntryM.Term' = es[q]?.map EntryM.Term')
    (m : Etcdraft.Msg) (hidx : m.prevLogIndex = idx) (hents : m.entries = logAbs C C.length (idx + 1) ents) :
    AppAgrees P m := by
  intro k e he hq
  have hpn : m.prevLogIndex.toNat = idx := by rw [hidx]; simp
  rw [hpn] at hq ⊢
  rw [hents, logAbs_getElem?] at he
  obtain ⟨y, hy, rfl⟩ : ∃ y, ents[k]? = some y ∧ entAbs C C.length (idx + 1 + k) y = e := by
    cases h : ents[k]? with
    | none => rw [h] at he; cases he
    | some y => rw [h] at he; exact ⟨y, rfl, Option.some.inj he⟩
  have hyG : G'[idx + k]? = some y := by
    have hk : k < ents.length := (List.getElem?_eq_some_iff.mp hy).1
    rw [← List.getElem?_drop, ← prefix_getElem?_of_lt hsl hk]; exact hy
  have hPl : P.length ≤ c := by
    have := hP.length_le; rw [logAbs_length, List.length_take] at this; omega
  have hqG : idx + k < G'.length := (List.getElem?_eq_some_iff.mp hyG).1
  have hqe : idx + k < es.length := by omega
  have hTq := hT (idx + k) (by omega) hqG
  rw [hyG, List.getElem?_eq_getElem hqe] at hTq
  simp only [Option.map_some, Option.some.injEq] at hTq
  rw [prefix_getElem?_of_lt hP hq, logAbs_getElem?, List.getElem?_take, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
    List.getElem?_eq_getElem hqe]
  simp only [Option.map_some, Option.some.injEq]
  rw [show 1 + (idx + k) = idx + 1 + k by omega]
  exact entAbs_eq C C.length _ _ _ hTq.symm

/-- (Amendment A6) **`AdvanceCommitIndex`'s outcome**: at a leader, the commit index raised to `c`, either
not past the old one or a positive index within the log that a quorum of the configuration's match
indices reaches (`maxAgree_spec`). -/
theorem advanceCommitIndex_cases {σ σ' : Etcdraft.State} {i : Etcdraft.ID}
    (h : σ.advanceCommitIndex i = some σ') :
    (σ.s i).state = Etcdraft.leader ∧ ∃ c : Int, σ' = σ.commitTo i c ∧
      (c ≤ (σ.s i).commitIndex ∨ (0 < c ∧ c ≤ (σ.s i).log.length ∧
        Etcdraft.isQuorum ((σ.getConfig i).filter (fun k => decide ((σ.s i).matchIndex k ≥ c)))
          (σ.getConfig i) = true)) := by
  unfold Etcdraft.State.advanceCommitIndex at h; dsimp only at h
  split at h
  · cases h
  · rename_i hl
    have hl : (σ.s i).state = Etcdraft.leader := by simpa using hl
    cases h
    refine ⟨hl, _, rfl, ?_⟩
    obtain ⟨h1, -⟩ := maxAgree_spec (fun n => Etcdraft.isQuorum ((σ.getConfig i).filter
      (fun k => decide ((σ.s i).matchIndex k ≥ ((n : Nat) : Int))))
      (σ.getConfig i)) (σ.s i).log.length
    split
    · rename_i hc
      right
      rcases h1 with h0 | ⟨ha, hb, hq⟩
      · exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact absurd hc.1 (by rw [h0]; omega)
      · exact ⟨by omega, by omega, hq⟩
    · left; exact Int.le_refl _

/-- (Amendment A6) A quorum's complement in the configuration is no quorum. -/
theorem isQuorum_filter_not {c : Etcdraft.SetIds} {p : Etcdraft.ID → Bool}
    (h : Etcdraft.isQuorum (c.filter p) c = true) : Etcdraft.isQuorum (c.filter (fun j => !p j)) c = false := by
  unfold Etcdraft.isQuorum at h ⊢
  have hs : ∀ r : Etcdraft.ID → Bool, Etcdraft.SetIds.subset (c.filter r) c = true := by
    intro r; unfold Etcdraft.SetIds.subset; rw [List.all_eq_true]
    intro x hx; simpa using (List.mem_filter.mp hx).1
  rw [hs] at h ⊢
  simp only [Bool.true_and, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  have hl := List.length_eq_countP_add_countP p (l := c)
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter] at hl
  have : (c.filter (fun a => decide ¬ p a = true)) = c.filter (fun j => !p j) := by
    apply List.filter_congr; intro x _; cases p x <;> rfl
  rw [this] at hl
  omega

/-- (Amendment A6) **A prefix from one agreeing term** (`LogMatchingInv`): server `k`'s log, read from a
raft log `Fk`, has at index `c` (past nothing, within both) the raft term the leader `i`'s recorded log
`es` has there, so it extends `i`'s log up to `c`. -/
theorem prefix_of_termAt (C : List w64) (σ : Etcdraft.State) (i k : Etcdraft.ID) (hi : i ∈ σ.server)
    (hk : k ∈ σ.server) (hlm : σ.logMatchingInv = true) (es pend Fk : List EntryM) (c : Nat)
    (hli : (σ.s i).log = logAbs C C.length 1 (es ++ pend)) (hlk : (σ.s k).log = logAbs C C.length 1 Fk)
    (hc0 : 0 < c) (hce : c ≤ es.length) (hc63 : (c : Int) < 2 ^ 63)
    (hag : plogTermAt base0 Fk (W64 (c : Int)) = plogTermAt base0 es (W64 (c : Int))) :
    (σ.s i).log.take c <+: (σ.s k).log := by
  have hc1 : ((c - 1 : Nat) : Int) + 1 = c := by omega
  have hFk := plogTermAt_succ Fk (c - 1) (by omega)
  have hes := plogTermAt_succ es (c - 1) (by omega)
  rw [hc1] at hFk hes
  rw [hFk, hes, List.getElem?_eq_getElem (by omega : c - 1 < es.length)] at hag
  obtain ⟨y, hy, hyt⟩ : ∃ y, Fk[c - 1]? = some y ∧ y.Term' = es[c - 1].Term' := by
    cases h : Fk[c - 1]? with
    | none => rw [h] at hag; cases hag
    | some y => rw [h] at hag; exact ⟨y, rfl, Option.some.inj hag⟩
  have hkl : c - 1 < (σ.s k).log.length := by
    rw [hlk, logAbs_length]; exact (List.getElem?_eq_some_iff.mp hy).1
  have hil : c - 1 < (σ.s i).log.length := by rw [hli, logAbs_length, List.length_append]; omega
  have hterm : ((σ.s i).log[c - 1]?).map Etcdraft.Entry.term = ((σ.s k).log[c - 1]?).map Etcdraft.Entry.term := by
    rw [hli, hlk, logAbs_getElem?, logAbs_getElem?, hy, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega : c - 1 < es.length)]
    simp only [Option.map_some, Option.some.injEq]
    unfold entAbs
    split
    · rfl
    · simp [hyt]
  unfold Etcdraft.State.logMatchingInv at hlm
  rw [List.all_eq_true] at hlm
  have h2 := hlm i hi
  rw [List.all_eq_true] at h2
  have h3 := h2 k hk
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h3
  rcases h3 (c - 1) (by omega) with h | h
  · exact absurd hterm h
  · rw [show c - 1 + 1 = c by omega] at h
    rw [h]; exact List.take_prefix _ _

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (Amendment A6) **An acknowledgement's history kept by a log that grows** (and a term that does not
fall): a raft log of the longer log has the shorter's as a prefix, whose history it keeps (`hist_keep`). -/
theorem ackHist_prefix (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (k : Etcdraft.ID) (T m : Int)
    (hL : (σ.s k).log <+: (σ'.s k).log) (hT : (σ.s k).currentTerm ≤ (σ'.s k).currentTerm) :
    AckHist (GF := GF) γ C σ k T m ⊢ AckHist γ C σ' k T m := by
  iintro H
  iunfold AckHist at H
  icases H with ⟨%hp, #H⟩
  iunfold AckHist
  isplitr
  · ipureintro; exact ⟨hp.1, Int.le_trans hp.2.1 hT, hp.2.2⟩
  imodintro
  iintro %F' %hF'
  obtain ⟨hl', hb'⟩ := hF'
  have hlog : (σ.s k).log = logAbs C C.length 1 (F'.take (σ.s k).log.length) := by
    rw [← logAbs_take, ← hl']
    exact (List.prefix_iff_eq_take.mp hL)
  ihave Hf : ∃ B, hist γ (F'.take (σ.s k).log.length) (W64 T) (W64 m) B $$ []
  · iapply H; ipureintro; exact ⟨hlog, hb'.take _⟩
  icases Hf with ⟨%B, #Hh⟩
  iexists B
  iapply hist_keep γ _ F' _ _ _
    (fun j _ hs => plogTermAt_prefix base0 _ F' j (List.take_prefix _ _) hs) $$ Hh

/-- (Amendment A6) **`AckHists` kept by logs that grow** (the same servers, terms that do not fall, no new
acknowledgement in flight, no new leader or match index). -/
theorem ackHists_grow (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (hsrv : σ'.server = σ.server)
    (hL : ∀ k, (σ.s k).log <+: (σ'.s k).log) (hT : ∀ k, (σ.s k).currentTerm ≤ (σ'.s k).currentTerm)
    (hM : ∀ x ∈ σ'.messages.domain ++ σ'.pendingMessages.domain, AckMsg x →
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain)
    (hLd : ∀ i, (σ'.s i).state = Etcdraft.leader → (σ.s i).state = Etcdraft.leader ∧
      (σ'.s i).currentTerm = (σ.s i).currentTerm ∧ ∀ k ∈ σ.server, (σ'.s i).matchIndex k = (σ.s i).matchIndex k) :
    AckHists (GF := GF) γ C σ ⊢ AckHists γ C σ' := by
  iintro #H
  iapply ackHists_mono γ C σ σ' iprop(True) hsrv hM hLd
    (fun k T m => by iintro ⟨-, #H⟩; iapply ackHist_prefix γ C σ σ' k T m (hL k) (hT k) $$ H)
  iframe H

/-- (Amendment A6) **The new acknowledgements' histories**: every acknowledgement in flight at `σ'` from
a server that was not in flight at `σ` has its history at `σ'` (a receive line's reply: the stale
request's, `ackHist_commit`; an accepted request's, from the receiver's raft facts of the request). -/
def NewAckHists (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) : IProp GF :=
  iprop(□ ∀ x, ⌜x ∈ σ'.messages.domain ++ σ'.pendingMessages.domain ∧ AckMsg x ∧ x.source ∈ σ'.server ∧
      x ∉ σ.messages.domain ++ σ.pendingMessages.domain⌝ → AckHist γ C σ' x.source x.term x.matchIndex)

instance newAckHists_persistent (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) :
    Persistent (NewAckHists (GF := GF) γ C σ σ') := by
  unfold NewAckHists; infer_instance

/-- (Amendment A6) **`AckHists` carried with new acknowledgements**: the same servers and logs, terms
that do not fall, no new leader or match index, and the new acknowledgements' histories given. -/
theorem ackHists_new (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (hsrv : σ'.server = σ.server)
    (hL : ∀ k, (σ'.s k).log = (σ.s k).log) (hT : ∀ k, (σ.s k).currentTerm ≤ (σ'.s k).currentTerm)
    (hLd : ∀ i, (σ'.s i).state = Etcdraft.leader → (σ.s i).state = Etcdraft.leader ∧
      (σ'.s i).currentTerm = (σ.s i).currentTerm ∧ ∀ k ∈ σ.server, (σ'.s i).matchIndex k = (σ.s i).matchIndex k) :
    AckHists (GF := GF) γ C σ ∗ NewAckHists γ C σ σ' ⊢ AckHists γ C σ' := by
  iintro ⟨#H, #Hn⟩
  iunfold AckHists at H
  icases H with ⟨#Hm, #Hl⟩
  iunfold NewAckHists at Hn
  iunfold AckHists
  isplitl
  · imodintro
    iintro %y %hy
    obtain ⟨hy1, hy2, hy3⟩ := hy
    by_cases hyo : y ∈ σ.messages.domain ++ σ.pendingMessages.domain
    · iapply ackHist_congr γ C σ σ' _ _ _ (hL _) (hT _)
      iapply Hm $$ %y
      ipureintro; exact ⟨hyo, hy2, by rw [← hsrv]; exact hy3⟩
    · iapply Hn $$ %y
      ipureintro; exact ⟨hy1, hy2, hy3, hyo⟩
  · imodintro
    iintro %i %k %h
    obtain ⟨hi, hk, hl, hki, hm⟩ := h
    obtain ⟨hl0, ht0, hm0⟩ := hLd i hl
    have hk' : k ∈ σ.server := by rw [← hsrv]; exact hk
    rw [hm0 k hk'] at hm
    rw [ht0, hm0 k hk']
    iapply ackHist_congr γ C σ σ' _ _ _ (hL _) (hT _)
    iapply Hl $$ %i %k
    ipureintro; exact ⟨by rw [← hsrv]; exact hi, hk', hl0, hki, hm⟩

/-- (Amendment A6) **`QuorumLogF` carried with new acknowledgements** (the same servers, logs and commit
indices, terms that do not fall, no new leader or match index). -/
theorem quorumLogF_new (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (hsrv : σ'.server = σ.server)
    (hL : ∀ k, (σ'.s k).log = (σ.s k).log) (hC : ∀ k, (σ'.s k).commitIndex = (σ.s k).commitIndex)
    (hT : ∀ k, (σ.s k).currentTerm ≤ (σ'.s k).currentTerm)
    (hLd : ∀ i, (σ'.s i).state = Etcdraft.leader → (σ.s i).state = Etcdraft.leader ∧
      (σ'.s i).currentTerm = (σ.s i).currentTerm ∧ ∀ k ∈ σ.server, (σ'.s i).matchIndex k = (σ.s i).matchIndex k) :
    QuorumLogF (GF := GF) γ C σ ∗ NewAckHists γ C σ σ' ⊢ QuorumLogF γ C σ' := by
  iintro ⟨#H, #Hn⟩
  iunfold QuorumLogF at H
  icases H with ⟨#Hq, #Ha⟩
  iunfold QuorumLogF
  isplitl
  · iapply quorumKept_mono γ C σ σ' hsrv
      (fun i hi => ⟨i, hi, by unfold committedL; rw [hL, hC]; exact List.prefix_refl _⟩)
      (fun _ _ h => keptFrom_congr hsrv hL hT h) $$ Hq
  · iapply ackHists_new γ C σ σ' hsrv hL hT hLd
    iframe Ha Hn

/-- (Amendment A6) **A reply's new acknowledgements**: after `W.reply x q` with `W`'s bags `σ`'s, the only
acknowledgement that may be new is the reply `x`. -/
theorem newAckHists_reply (γ : RaftNames) (C : List w64) (σ W : Etcdraft.State) (x q : Etcdraft.Msg)
    (hmW : W.messages = σ.messages) (hpW : W.pendingMessages = σ.pendingMessages) :
    □ (⌜AckMsg x ∧ x.source ∈ (W.reply x q).server⌝ → AckHist (GF := GF) γ C (W.reply x q) x.source x.term x.matchIndex) ⊢
      NewAckHists γ C σ (W.reply x q) := by
  iintro #Hx
  iunfold NewAckHists
  imodintro
  iintro %y %hy
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have hyx : y = x := by
    rcases List.mem_append.mp hy1 with h | h
    · exact absurd (List.mem_append_left _ (by rw [← hmW]; exact TraceSpecInv.mem_without _ _ _ h)) hy4
    · rcases (TraceSpecInv.mem_with _ _ _).1 h with h | h
      · exact absurd (List.mem_append_right _ (by rw [← hpW]; exact h)) hy4
      · exact h
  subst hyx
  iapply Hx; ipureintro; exact ⟨hy2, hy3⟩

/-- **An append round keeps `QuorumLogF`** (`NoConflictAppendEntriesRequest`). -/
theorem quorumLogF_noConflict (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r : Etcdraft.ID)
    (index : Int) (m : Etcdraft.Msg)
    (hstep : σ.noConflictAppendEntriesRequest r index m = .ok (some σ')) :
    QuorumLogF (GF := GF) γ C σ ⊢ QuorumLogF γ C σ' := by
  obtain ⟨-, -, suffix, hσ'⟩ := noConflictRound_eq hstep
  have hsrv : σ'.server = σ.server := by rw [hσ']; rfl
  have hs : ∀ j, σ'.s j = if j = r then { σ.s r with log := (σ.s r).log ++ suffix } else σ.s j := by
    intro j; rw [hσ']; rfl
  exact quorumLogF_mono γ C σ σ' hsrv
    (fun i hi => ⟨i, hi, by rw [committedL_noConflict hstep]; exact List.prefix_refl _⟩)
    (fun _ _ h => keptFrom_noConflict hstep h)
    (fun x hx _ => by rw [hσ'] at hx; exact hx)
    (fun i hi => by
      rw [hs] at hi ⊢
      split
      · rename_i h; subst h; rw [if_pos rfl] at hi; exact ⟨hi, rfl, fun _ _ => rfl⟩
      · rename_i h; rw [if_neg h] at hi; exact ⟨hi, rfl, fun _ _ => rfl⟩)
    (fun k T m => ackHist_prefix γ C σ σ' k T m
      (by rw [hs]; split
          · rename_i h; subst h; exact List.prefix_append _ _
          · exact List.prefix_refl _)
      (by rw [hs]; split
          · rename_i h; subst h; exact Int.le_refl _
          · exact Int.le_refl _))

/-- **A reply with the receiver's commit index raised to `c` keeps `QuorumLogF`**, `c` within the
request's sender's commit index (`ReqCommitC`) and the two committed prefixes comparable after it
(`LogInv`, `hcmp`): the receiver's new committed prefix is its old one's prefix or its sender's
(`committedL_raise_prefix`), whose witness it takes. -/
theorem quorumLogF_commitReply (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (r : Etcdraft.ID)
    (c : Int) (x q : Etcdraft.Msg) (src : Etcdraft.ID) (hsrc : src ∈ σ.server)
    (hc : c ≤ (σ.s src).commitIndex) (hsl : (σ.s src).commitIndex ≤ (σ.s src).log.length)
    (hcmp : TraceSpecInv.CommittedCmp ((σ.commitTo r c).reply x q) r src) :
    QuorumLogF (GF := GF) γ C σ ∗ NewAckHists γ C σ ((σ.commitTo r c).reply x q) ⊢
      QuorumLogF γ C ((σ.commitTo r c).reply x q) := by
  have hs : ∀ k, ((σ.commitTo r c).reply x q).s k =
      if k = r then { σ.s r with commitIndex := max (σ.s r).commitIndex c } else σ.s k := by
    intro k; rfl
  have hF : ∀ k, (((σ.commitTo r c).reply x q).s k).log = (σ.s k).log ∧
      (((σ.commitTo r c).reply x q).s k).currentTerm = (σ.s k).currentTerm ∧
      (((σ.commitTo r c).reply x q).s k).state = (σ.s k).state := by
    intro k; rw [hs]; split <;> simp_all
  iintro ⟨#H, #Hn⟩
  iunfold QuorumLogF at H
  icases H with ⟨#Hq, #Ha⟩
  iunfold QuorumLogF
  isplitl
  rotate_left
  · iapply ackHists_new γ C σ ((σ.commitTo r c).reply x q) rfl (fun k => (hF k).1)
      (fun k => by rw [(hF k).2.1]; exact Int.le_refl _)
      (fun i hi => by
        rw [hs] at hi ⊢
        split
        · rename_i h; subst h; rw [if_pos rfl] at hi; exact ⟨hi, rfl, fun _ _ => rfl⟩
        · rename_i h; rw [if_neg h] at hi; exact ⟨hi, rfl, fun _ _ => rfl⟩)
    iframe Ha Hn
  iapply quorumKept_mono γ C σ ((σ.commitTo r c).reply x q) rfl ?_ ?_ $$ Hq
  · intro k hk
    by_cases hkr : k = r
    · subst hkr
      rcases committedL_raise_prefix (σ := σ) (W := (σ.commitTo k c).reply x q) (src := src) (c := c)
          (hF k).1 (by rw [hs, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
          (fun j hj => by unfold committedL; rw [(hF j).1, hs, ite_eq_right_of_eq_false _ _ (eq_false hj)])
          hc hsl hcmp with h | h
      · exact ⟨k, hk, h⟩
      · exact ⟨src, hsrc, h⟩
    · exact ⟨k, hk, by unfold committedL; rw [hs, ite_eq_right_of_eq_false _ _ (eq_false hkr)]; exact List.prefix_refl _⟩
  · intro P t h
    exact keptFrom_congr (σ := σ) (σ' := (σ.commitTo r c).reply x q) rfl (fun k => (hF k).1)
      (fun k => by rw [(hF k).2.1]; exact Int.le_refl _) h

/-- **Logs that only grow keep `QuorumLogF`** (a leader's `Replicate` and `ClientRequest`, the same
servers, commit indices and terms that do not fall): a server holding `P` still does, and every
committed prefix is within the old log (`CommitOk`), so unchanged. -/
theorem quorumLogF_grow (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (hsrv : σ'.server = σ.server)
    (hL : ∀ k, (σ.s k).log <+: (σ'.s k).log) (hC : ∀ k, (σ'.s k).commitIndex = (σ.s k).commitIndex)
    (hT : ∀ k, (σ.s k).currentTerm ≤ (σ'.s k).currentTerm) (hco : TraceSim.CommitOk σ)
    (hM : ∀ x ∈ σ'.messages.domain ++ σ'.pendingMessages.domain, AckMsg x →
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain)
    (hLd : ∀ i, (σ'.s i).state = Etcdraft.leader → (σ.s i).state = Etcdraft.leader ∧
      (σ'.s i).currentTerm = (σ.s i).currentTerm ∧ ∀ k ∈ σ.server, (σ'.s i).matchIndex k = (σ.s i).matchIndex k) :
    QuorumLogF (GF := GF) γ C σ ⊢ QuorumLogF γ C σ' := by
  refine quorumLogF_mono γ C σ σ' hsrv (fun i hi => ⟨i, hi, ?_⟩)
    (fun _ _ h => keptFrom_of hsrv (fun j _ h1 h2 => ⟨h1.trans (hL j), Int.le_trans h2 (hT j)⟩) h) hM hLd
    (fun k T m => ackHist_prefix γ C σ σ' k T m (hL k) (hT k))
  obtain ⟨r, hr⟩ := hL i
  have hc := hco i hi
  unfold committedL
  rw [hC, ← hr, List.take_append_of_le_length (by omega)]
  exact List.prefix_refl _

/-- **The reply round keeps `QuorumLogF`** (`AppendEntriesAlreadyDone`, the receiver's commit index
raised to at most the request's, within its sender's: `ReqCommitC`; `quorumLogF_commitReply`), given
the new state's `LogInv` for the receiver and the sender (`hcmp`, from `allFacts_logInv` there). -/
theorem quorumLogF_alreadyDone (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r j : Etcdraft.ID)
    (index : Int) (m : Etcdraft.Msg) (hsi : TraceSpecInv.SpecInv σ) (hco : TraceSim.CommitOk σ)
    (hm : m ∈ σ.messages.domain) (hty : m.type = .appendEntriesRequest)
    (hstep : σ.appendEntriesAlreadyDone r j index m = some σ')
    (hcmp : TraceSpecInv.CommittedCmp σ' r m.source) :
    QuorumLogF (GF := GF) γ C σ ∗ NewAckHists γ C σ σ' ⊢ QuorumLogF γ C σ' := by
  obtain ⟨hsrc, hcs⟩ := hsi.reqCommitC m (List.mem_append_left _ hm) hty
  have hsl := (hco m.source hsrc).2
  unfold Etcdraft.State.appendEntriesAlreadyDone at hstep; dsimp only at hstep
  split at hstep
  · cases hstep
  · cases hstep
    split
    · rename_i h1; simp only [h1, ↓reduceIte] at hcmp
      split
      · rename_i h2; simp only [h2, ↓reduceIte] at hcmp
        exact quorumLogF_commitReply γ C σ r _ _ m m.source hsrc hcs hsl hcmp
      · -- no raise: the reply only
        exact quorumLogF_new γ C σ _ rfl (fun _ => rfl) (fun _ => rfl) (fun _ => Int.le_refl _)
          (fun _ hi => ⟨hi, rfl, fun _ _ => rfl⟩)
    · rename_i h1; simp only [h1, ↓reduceIte] at hcmp
      exact quorumLogF_commitReply γ C σ r _ _ m m.source hsrc
        (Int.le_trans (Int.min_le_left _ _) hcs) hsl hcmp


/-- **A commit justification within a full log of a later or equal term** (`commit_in_leader_cert`'s
three cases, for `commitJ` at a term `tm ≤ T`, without its length premise): `G'` and `es` agree on
raft's terms up to `c` wherever `G'` reaches (bootstrap: both start with the bootstrap log; a commit
quorum of `T`: two full logs of `T`, `leadFull_agree`; an earlier term: `lc_core`). -/
theorem commitJ_leadFull (γ : RaftNames) (es G' : List EntryM) (c tm T : w64)
    (hw : PlogWf base0 es) (hc : uint.Z c ≤ es.length) (htm : uint.Z tm ≤ uint.Z T) :
    votesTbl (GF := GF) γ ∗ logRecs γ base0 es ∗ commitJ γ es c tm ∗ leadFull γ T G' ⊢
      ⌜∀ j : w64, uint.Z j ≤ uint.Z c → uint.Z j ≤ G'.length →
        plogTermAt base0 G' j = plogTermAt base0 es j⌝ := by
  iintro ⟨Htbl, #Hr, #Hcj, #HL⟩
  icases leadFull_wf γ T G' $$ HL with ⟨%HwL, #HrL⟩
  have HlenL : plogLastIndexZ base0 G' = (G'.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  unfold commitJ
  icases Hcj with (%Hb0 | ⟨%t, %n, %G, #Hq, %Hcn⟩)
  · icases logRecs_boot_termAt γ es hw $$ Hr with %Hbe
    icases logRecs_boot_termAt γ G' HwL.1 $$ HrL with %HbL
    icases leadFull_boot γ T G' $$ HL with %Hbt
    have HbG := Hbt.1.length_le
    ipureintro
    intro j hj _
    rw [← HbL j (by omega) (by omega), ← Hbe j (by omega) (by omega)]
  obtain ⟨Hcn, Htt, HGe⟩ := Hcn
  icases cq_base γ t n G $$ Hq with ⟨%HGn, #HGl⟩
  icases leadFull_wf γ t G $$ HGl with ⟨%HwG, #HrG⟩
  have Hn := (plogTermAt_some_range _ _ _ _ HGn).2
  have HlenG : plogLastIndexZ base0 G = (G.length : Int) := by
    unfold plogLastIndexZ; rw [base0_index]; simp
  icases full_match γ G es c HwG.1 hw
      (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩) HGe
      $$ HrG Hr with %HGall
  by_cases hT : t = T
  · subst hT
    -- two full logs of `t` agree where both reach: up to `k = min c |G'|`
    by_cases hk0 : uint.Z c = 0 ∨ G'.length = 0
    · ipureintro
      intro j hj hjl
      have hj0 : j = W64 0 := by word
      subst hj0; rfl
    have hk : (min (uint.Z c) (G'.length : Int)) < 2 ^ 64 := by
      have := uint_Z_lt c; omega
    have hkZ : uint.Z (W64 (min (uint.Z c) (G'.length : Int))) = min (uint.Z c) (G'.length : Int) := by
      have := uint_Z_nonneg c; word
    icases leadFull_agree γ t G' G (W64 (min (uint.Z c) (G'.length : Int)))
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenL, hkZ]; omega⟩)
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenG, hkZ]; omega⟩)
        $$ HL HGl with %HLG
    icases full_match γ G' G (W64 (min (uint.Z c) (G'.length : Int))) HwL.1 HwG.1
        (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by rw [HlenL, hkZ]; omega⟩) HLG
        $$ HrL HrG with %HLGall
    ipureintro
    intro j hj hjl
    rw [HLGall j (by rw [hkZ]; omega), HGall j hj]
  · have Hlt : uint.Z t < uint.Z T := by
      have : uint.Z t ≠ uint.Z T := fun h => hT (uint_Z_inj.mp h)
      omega
    icases leadFull_camp γ T G' $$ HL with ⟨%ldr, %F0, #Hl, #Hc0, %Hpre⟩
    icases isCamp_ok γ ldr T F0 $$ Hc0 with %Hcok
    have Hcl := camp_last T F0 Hcok
    icases lc_core γ ((uint.Z T).toNat + 1) T t n G ldr F0 G'
        (by have := uint_Z_nonneg T; omega) Hlt HwL.1
        (by rw [plogTermAt_prefix _ F0 _ _ Hpre (by rw [Hcl]; rfl)]; exact Hcl)
        $$ Htbl Hq Hl Hc0 HrL with %HnL
    icases full_match γ G' G n HwL.1 HwG.1 (by rw [HnL]; rfl) (by rw [HnL, HGn])
        $$ HrL HrG with %HLG
    ipureintro
    intro j hj _
    rw [HLG j (by omega), HGall j hj]

/-- **A committed prefix and an append request of a later or equal term agree** (the receiver's facts
of the request, raft's `isMessage`: the entries a slice of its leader's log `fp ++ l` of its term `T`,
`leadPrefix` and `lpfull`): the leader's full log agrees with the certificate's log up to its commit
index wherever it reaches (`commitJ_leadFull`), and the request's entries are of it
(`appAgrees_of_terms`). -/
theorem commitCert_app (γ : RaftNames) (C : List w64) (P : List Etcdraft.Entry) (t : Int)
    (src T : w64) (bL : entryID) (l fp ents : List EntryM) (idx lt : w64) (ma : Etcdraft.Msg)
    (htT : t ≤ uint.Z T) (hin : plogTermAt bL l idx = some lt)
    (hsl : ents <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : ma.prevLogIndex = uint.Z idx) (hents : ma.entries = logAbs C C.length (uint.nat idx + 1) ents) :
    votesTbl (GF := GF) γ ∗ CommitCert γ C P t ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ⊢
      ⌜AppAgrees P ma⌝ := by
  iintro ⟨Htbl, Hcc, #Hp, #Hf⟩
  ihave #HL := leadFull_intro γ src T bL l fp $$ Hp Hf
  ihave #Hf' := Hf
  iunfold lpfull at Hf'
  icases Hf' with ⟨%F0, -, -, %Hpf⟩
  obtain ⟨hfull, -, -, -⟩ := Hpf
  iunfold CommitCert at Hcc
  icases Hcc with ⟨%es, %c, %Hp0, #Hr, #Hj⟩
  obtain ⟨hP, hw, hc, hes, ht0, ht1⟩ := Hp0
  have htW : uint.Z (W64 t) = t := by word
  icases commitJ_leadFull γ es (fp ++ l) c (W64 t) T hw hc (by rw [htW]; exact htT)
    $$ [$Htbl $Hr $Hj $HL] with %Hag
  ipureintro
  have hb := (plogTermAt_some_range _ _ _ _ hin).1
  have hfl : (fp.length : Int) = uint.Z bL.index' := hfull.1
  have hni : (uint.nat idx : Int) = uint.Z idx := by word
  have hnc : (uint.nat c : Int) = uint.Z c := by word
  have hsl' : ents <+: (fp ++ l).drop (uint.nat idx) := by
    unfold plogFrom at hsl
    have h1 : uint.Z (idx + W64 1) = uint.Z idx + 1 := by word
    rw [h1] at hsl
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    have h2 : (uint.Z idx + 1 - uint.Z bL.index' - 1).toNat = uint.nat idx - fp.length := by omega
    rw [h2] at hsl; exact hsl
  refine appAgrees_of_terms C P es (fp ++ l) ents (uint.nat c) (uint.nat idx) hP (by omega) hsl' ?_ ma
    (by omega) hents
  intro q hq hqG
  have hqW : uint.Z (W64 ((q : Int) + 1)) = (q : Int) + 1 := by
    have : (q : Int) + 1 < 2 ^ 63 := by omega
    word
  have := Hag (W64 ((q : Int) + 1)) (by rw [hqW]; omega) (by rw [hqW]; omega)
  rw [plogTermAt_succ _ _ (by omega), plogTermAt_succ _ _ (by omega)] at this
  exact this

/-- **Persistent facts for every element of a list, each drawn with the vote table** (which is not
persistent, so the facts are drawn one element at a time). -/
theorem votesTbl_forall_list (γ : RaftNames) {α : Type} (A B : α → IProp GF)
    [∀ a, Persistent (A a)] [∀ a, Persistent (B a)]
    (h : ∀ a, votesTbl γ ∗ A a ⊢ votesTbl γ ∗ B a) (l : List α) :
    votesTbl (GF := GF) γ ∗ (□ ∀ a, ⌜a ∈ l⌝ → A a) ⊢ votesTbl γ ∗ □ ∀ a, ⌜a ∈ l⌝ → B a := by
  induction l with
  | nil =>
    iintro ⟨Ht, -⟩
    iframe Ht
    imodintro
    iintro %a %ha
    cases ha
  | cons x l ih =>
    iintro ⟨Ht, #HA⟩
    ihave #Hx := HA $$ %x %(List.mem_cons_self ..)
    icases (h x) $$ [$Ht $Hx] with ⟨Ht, #Bx⟩
    ihave #HAl : □ ∀ a, ⌜a ∈ l⌝ → A a $$ []
    · imodintro
      iintro %a %ha
      iapply HA $$ %a %(List.mem_cons_of_mem _ ha)
    icases ih $$ [$Ht $HAl] with ⟨Ht, #Bl⟩
    iframe Ht
    imodintro
    iintro %a %ha
    rcases List.mem_cons.mp ha with rfl | ha
    · iexact Bx
    · iapply Bl $$ %a %ha

/-- (Amendment A6) A truncated raft log's terms (from index 1). -/
theorem plogTermAt_take_base0 (F : List EntryM) (L : Nat) (j : w64) :
    plogTermAt base0 (F.take L) j = if uint.Z j ≤ L then plogTermAt base0 F j else none := by
  by_cases hj : uint.Z j = 0
  · have : uint.Z j ≤ L := by omega
    rw [if_pos this]
    unfold plogTermAt; simp [base0_index, hj]
  have hj0 : 0 < uint.Z j := by have := uint_Z_nonneg j; omega
  rw [show (base0 : entryID) = entryID.mk (W64 0) (W64 0) from rfl, plogTermAt_base0 _ j hj0,
    plogTermAt_base0 _ j hj0, List.getElem?_take]
  have hn : (uint.nat j : Int) = uint.Z j := by word
  split <;> split <;> first | rfl | omega

/-- (Amendment A6) **A history across a truncation past a conflict** (the specification's
`ConflictAppendEntriesRequest` round, the log's last entry dropped): `F'` keeps `F` up to `L` and has
nothing past it, and `F` disagrees at `q ≤ L + 1` with a full log `Y` of a leader of a term `T` at least
the acknowledgement's. Up to `L` the old history serves; past it, the disagreement at `q` (with the
`okL` log `F` agreed with there, or an older one) does. -/
theorem hist_trunc (γ : RaftNames) (F F' Y : List EntryM) (t i T : w64) (B B' : Int) (q L : Nat)
    (hB : B ≤ B') (htT : uint.Z t ≤ uint.Z T) (hTB : uint.Z T < B')
    (hq0 : 0 < q) (hqL : q ≤ L + 1) (hq63 : (q : Int) < 2 ^ 63)
    (hlow : ∀ j : w64, uint.Z j ≤ L → plogTermAt base0 F' j = plogTermAt base0 F j)
    (hhigh : ∀ j : w64, L < uint.Z j → plogTermAt base0 F' j = none)
    (hYq : (plogTermAt base0 Y (W64 q)).isSome)
    (hdiff : plogTermAt base0 F (W64 q) ≠ plogTermAt base0 Y (W64 q)) :
    ⊢ leadFull (GF := GF) γ T Y -∗ hist γ F t i B -∗ hist γ F' t i B' := by
  iintro #HY #Hh
  ihave #HokY : (∀ j', okL (GF := GF) γ t B' j' Y) $$ []
  · iintro %j'
    unfold okL
    ileft; iexists T
    isplitr; · ipureintro; omega
    iexact HY
  have hqW : uint.Z (W64 (q : Int)) = q := by word
  unfold hist
  iintro %j %Hj
  by_cases hjL : uint.Z j ≤ L
  · icases Hh $$ %j %Hj with (⟨%X, #HX, %Hs⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
    · ileft; iexists X
      isplitr; · iapply okL_mono γ t B B' j X hB $$ HX
      ipureintro; rw [hlow j hjL]; exact Hs
    · iright; iexists j', X1, X2
      isplitr; · ipureintro; exact Hj'
      isplitr; · iapply okL_mono γ t B B' j' X1 hB $$ H1
      isplitr; · iapply okL_mono γ t B B' j' X2 hB $$ H2
      ipureintro; exact Hd
  · icases Hh $$ %(W64 (q : Int)) %(⟨by rw [hqW]; omega, by rw [hqW]; omega⟩ :
        0 < uint.Z (W64 (q : Int)) ∧ uint.Z (W64 (q : Int)) ≤ uint.Z i)
      with (⟨%X, #HX, %Hs⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
    · iright; iexists (W64 (q : Int)), X, Y
      isplitr; · ipureintro; rw [hqW]; omega
      isplitr; · iapply okL_mono γ t B B' _ X hB $$ HX
      isplitr; · iapply HokY
      ipureintro; exact ⟨Hs.1, hYq, by rw [Hs.2]; exact hdiff⟩
    · iright; iexists j', X1, X2
      isplitr; · ipureintro; rw [hqW] at Hj'; omega
      isplitr; · iapply okL_mono γ t B B' j' X1 hB $$ H1
      isplitr; · iapply okL_mono γ t B B' j' X2 hB $$ H2
      ipureintro; exact Hd

/-- (Amendment A6) **A truncation round keeps the receiver's acknowledgements' histories**: the request,
of the receiver's term `T`, at least each acknowledgement's, is a slice of its leader's full log `Y`
(`leadPrefix`, `lpfull`), and its conflict (`conflict_pos`, past the bootstrap entries, whose abstract
terms agree) is where the receiver's raft log `F0` (its facts' `es ++ pend`) disagrees with `Y`
(`hist_trunc`). -/
theorem ackHist_conflict (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r : Etcdraft.ID)
    (m : Etcdraft.Msg) (hterm : m.term = (σ.s r).currentTerm)
    (hp0 : 0 ≤ m.prevLogIndex) (hple : m.prevLogIndex ≤ (σ.s r).log.length)
    (hstep : σ.conflictAppendEntriesRequest r (m.prevLogIndex + 1) m = .ok (some σ'))
    (src T : w64) (bL : entryID) (l fp ents : List EntryM) (idx lt : w64)
    (hT : m.term = uint.Z T) (hin : plogTermAt bL l idx = some lt)
    (hsl : ents <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : m.prevLogIndex = uint.Z idx) (hents : m.entries = logAbs C C.length (uint.nat idx + 1) ents)
    (w : w64) (Tk mk : Int) :
    leadPrefix (GF := GF) γ src T bL l ∗ lpfull γ src T bL l fp ∗ srvFacts γ C w (σ.s r) ∗
      AckHist γ C σ r Tk mk ⊢ AckHist γ C σ' r Tk mk := by
  obtain ⟨-, hnc, hσ'⟩ := conflictRound_eq hstep
  obtain ⟨k, e, he, hkl, hne⟩ := conflict_pos hp0 hple hnc
  have hs' : σ'.s r = { σ.s r with log := (σ.s r).log.take ((σ.s r).log.length - 1) } := by
    rw [hσ']; unfold Etcdraft.State.upd; simp
  iintro ⟨#Hp, #Hf, #Hs, #Ha⟩
  ihave #HL := leadFull_intro γ src T bL l fp $$ Hp Hf
  ihave #Hf' := Hf
  iunfold lpfull at Hf'
  icases Hf' with ⟨%F0', -, -, %Hpf⟩
  obtain ⟨hfull, -, -, -⟩ := Hpf
  iunfold srvFacts at Hs
  icases Hs with ⟨%es, %pend, %Hsp, -⟩
  obtain ⟨hlog, hboot, hwf, hlen, -⟩ := Hsp
  iunfold AckHist at Ha
  icases Ha with ⟨%hpa, #Ha⟩
  ihave Hh : ∃ B, hist γ (es ++ pend) (W64 Tk) (W64 mk) B $$ []
  · iapply Ha; ipureintro; exact ⟨hlog, hboot⟩
  icases Hh with ⟨%B, #Hh⟩
  -- the conflict, in raft's terms
  have hb := (plogTermAt_some_range _ _ _ _ hin).1
  have hfl : (fp.length : Int) = uint.Z bL.index' := hfull.1
  have hni : (uint.nat idx : Int) = uint.Z idx := by word
  have hpn : m.prevLogIndex.toNat = uint.nat idx := by rw [hidx]; omega
  have hsl' : ents <+: (fp ++ l).drop (uint.nat idx) := by
    unfold plogFrom at hsl
    have h1 : uint.Z (idx + W64 1) = uint.Z idx + 1 := by word
    rw [h1] at hsl
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    have h2 : (uint.Z idx + 1 - uint.Z bL.index' - 1).toNat = uint.nat idx - fp.length := by omega
    rw [h2] at hsl; exact hsl
  rw [hents, logAbs_getElem?] at he
  obtain ⟨y, hy, rfl⟩ : ∃ y, ents[k]? = some y ∧ entAbs C C.length (uint.nat idx + 1 + k) y = e := by
    cases h : ents[k]? with
    | none => rw [h] at he; cases he
    | some y => rw [h] at he; exact ⟨y, rfl, Option.some.inj he⟩
  have hyY : (fp ++ l)[uint.nat idx + k]? = some y := by
    have hk : k < ents.length := (List.getElem?_eq_some_iff.mp hy).1
    rw [← List.getElem?_drop, ← prefix_getElem?_of_lt hsl' hk]; exact hy
  rw [hpn, hlog, logAbs_getElem?] at hne
  rw [hlog, logAbs_length] at hkl
  rw [hpn] at hkl
  obtain ⟨x, hx⟩ : ∃ x, (es ++ pend)[uint.nat idx + k]? = some x :=
    ⟨_, List.getElem?_eq_getElem hkl⟩
  rw [hx] at hne
  simp only [Option.map_some, ne_eq, Option.some.injEq] at hne
  have hbl : ¬ (1 + (uint.nat idx + k) ≤ C.length) := by
    intro hle
    apply hne
    unfold entAbs
    rw [if_pos hle, if_pos (by omega)]
  have hxy : x.Term' ≠ y.Term' := by
    intro hxy; apply hne
    rw [entAbs_term C C.length _ _ (fun h => absurd h hbl),
      entAbs_term C C.length _ _ (fun h => absurd (by omega) hbl), hxy]
  have hq63 : ((uint.nat idx + k : Nat) : Int) + 1 < 2 ^ 63 := by
    rw [List.length_append] at hlen hkl; omega
  have hFq := plogTermAt_succ (es ++ pend) (uint.nat idx + k) hq63
  have hYq := plogTermAt_succ (fp ++ l) (uint.nat idx + k) hq63
  rw [hx] at hFq; rw [hyY] at hYq
  simp only [Option.map_some] at hFq hYq
  have hqn : (((uint.nat idx + k + 1 : Nat) : Int)) = ((uint.nat idx + k : Nat) : Int) + 1 := by push_cast; omega
  -- the history after the truncation
  have hTk : uint.Z (W64 Tk) ≤ uint.Z T := by
    have := hpa.2.1; rw [← hterm, hT] at this
    have : uint.Z (W64 Tk) = Tk := by have := hpa.1; have := hpa.2.2.1; word
    omega
  ihave #Hh' := hist_trunc γ (es ++ pend) ((es ++ pend).take ((es ++ pend).length - 1)) (fp ++ l)
    (W64 Tk) (W64 mk) T B (max B (uint.Z T + 1)) (uint.nat idx + k + 1) ((es ++ pend).length - 1)
    (Int.le_max_left _ _) hTk (by omega) (by omega) (by omega) (by rw [hqn]; exact hq63)
    (fun j hj => by rw [plogTermAt_take_base0, if_pos hj])
    (fun j hj => by rw [plogTermAt_take_base0, if_neg (by omega)])
    (by rw [hqn, hYq]; rfl) (by rw [hqn, hFq, hYq]; simpa using hxy) $$ HL Hh
  iunfold AckHist
  isplitr
  · ipureintro; rw [hs']; exact hpa
  imodintro
  iintro %F' %hF'
  iexists (max B (uint.Z T + 1))
  have hlt : (σ'.s r).log = logAbs C C.length 1 ((es ++ pend).take ((es ++ pend).length - 1)) := by
    rw [hs', ← logAbs_take, ← hlog, hlog, logAbs_length]
  iapply hist_logAbs γ C _ F' (by rw [← hlt, hF'.1]) (hboot.take _) hF'.2 $$ Hh'

/-- **A truncation round keeps `QuorumLogF`** (amendment A5, the sufficiency of Q21): an accepted
append request's `ConflictAppendEntriesRequest` at a server of its term `T` (`keptFrom_conflict`), the
receiver holding raft's facts of the request (`isMessage`'s: its leader's `leadPrefix` and `lpfull`, the
entries `ents` a slice of the leader's log after the previous entry `idx`, which `m` abstracts) and the
vote table: each committed prefix, kept from a term `t ≤ T` with its certificate, agrees with the request
(`commitCert_app`); every committed prefix and its certificate unchanged (`committedL_conflict`). -/
theorem quorumLogF_conflict (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r : Etcdraft.ID)
    (m : Etcdraft.Msg) (hterm : m.term = (σ.s r).currentTerm)
    (hp0 : 0 ≤ m.prevLogIndex) (hple : m.prevLogIndex ≤ (σ.s r).log.length)
    (hstep : σ.conflictAppendEntriesRequest r (m.prevLogIndex + 1) m = .ok (some σ'))
    (src T : w64) (bL : entryID) (l fp ents : List EntryM) (idx lt : w64)
    (hT : m.term = uint.Z T) (hin : plogTermAt bL l idx = some lt)
    (hsl : ents <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : m.prevLogIndex = uint.Z idx) (hents : m.entries = logAbs C C.length (uint.nat idx + 1) ents)
    (hsrv0 : σ.server = confAbs C) (hr : r ∈ σ.server) :
    votesTbl (GF := GF) γ ∗ QuorumLogF γ C σ ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ∗
      allFacts γ C σ ⊢
      votesTbl γ ∗ QuorumLogF γ C σ' := by
  obtain ⟨-, -, hσ'⟩ := conflictRound_eq hstep
  have hsrv : σ'.server = σ.server := by rw [hσ']; rfl
  have hs : ∀ j, σ'.s j = if j = r then { σ.s r with log := (σ.s r).log.take ((σ.s r).log.length - 1) }
      else σ.s j := by
    intro j; rw [hσ']; rfl
  iintro ⟨Htbl, #Hq, #Hp, #Hf, #Hal⟩
  iunfold QuorumLogF at Hq
  icases Hq with ⟨#Hq, #Ha⟩
  iunfold QuorumKept at Hq
  ihave #HA : □ ∀ i, ⌜i ∈ σ.server⌝ → ((∃ t, ⌜KeptFrom σ (committedL σ i) t⌝ ∗
      CommitCert γ C (committedL σ i) t) ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp) $$ []
  · imodintro
    iintro %i %hi
    iframe Hp Hf
    iapply Hq $$ %i %hi
  icases votesTbl_forall_list γ
      (fun i => iprop((∃ t, ⌜KeptFrom σ (committedL σ i) t⌝ ∗ CommitCert γ C (committedL σ i) t) ∗
        leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp))
      (fun i => iprop(∃ t, ⌜KeptFrom σ (committedL σ i) t ∧ (t ≤ m.term → AppAgrees (committedL σ i) m)⌝ ∗
        CommitCert γ C (committedL σ i) t))
      (fun i => by
        iintro ⟨Htbl, ⟨%t, %hK, #Hc⟩, #Hp, #Hf⟩
        by_cases ht : t ≤ m.term
        · icases keep_pure (commitCert_app γ C (committedL σ i) t src T bL l fp ents idx lt m
              (by rw [← hT]; exact ht) hin hsl hidx1 hidx hents) $$ [$Htbl $Hc $Hp $Hf]
            with ⟨⟨Htbl, -⟩, %hag⟩
          iframe Htbl
          iexists t
          iframe Hc
          ipureintro
          exact ⟨hK, fun _ => hag⟩
        · iframe Htbl
          iexists t
          iframe Hc
          ipureintro
          exact ⟨hK, fun h => absurd h ht⟩)
      σ.server $$ [$Htbl $HA] with ⟨Htbl, #Hb⟩
  iframe Htbl
  iunfold QuorumLogF
  isplitl
  · iunfold QuorumKept
    imodintro
    iintro %i %hi
    rw [hsrv] at hi
    ihave Hi := Hb $$ %i %hi
    icases Hi with ⟨%t, %hK, #Hc⟩
    iexists t
    rw [committedL_conflict hp0 hple hstep]
    iframe Hc
    ipureintro
    exact keptFrom_conflict hterm hp0 hple hstep hK.2 hK.1
  · -- (amendment A6) the receiver's acknowledgements' histories across the truncation
    have hrC : r ∈ confAbs C := by rw [← hsrv0]; exact hr
    obtain ⟨w, hwC, hwr⟩ := mem_confAbs_inv C r hrC
    iunfold allFacts at Hal
    ihave #Hsw := Hal $$ %w %hwC
    iapply ackHists_mono γ C σ σ' iprop(leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ∗ srvFacts γ C w (σ.s r))
      hsrv (fun x hx _ => by rw [hσ'] at hx; exact hx)
      (fun i hi => by
        rw [hs] at hi ⊢
        split
        · rename_i h; subst h; rw [if_pos rfl] at hi; exact ⟨hi, rfl, fun _ _ => rfl⟩
        · rename_i h; rw [if_neg h] at hi; exact ⟨hi, rfl, fun _ _ => rfl⟩)
      (fun k Tk mk => by
        by_cases hkr : k = r
        · rw [hkr]
          iintro ⟨⟨#H1, #H2, #H3⟩, #H4⟩
          iapply ackHist_conflict (GF := GF) γ C σ σ' r m hterm hp0 hple hstep src T bL l fp ents idx lt hT hin
            hsl hidx1 hidx hents w Tk mk
          iframe H1 H2 H3 H4
        · iintro ⟨-, H⟩
          iapply ackHist_congr γ C σ σ' k Tk mk (by rw [hs, if_neg hkr]) (by rw [hs, if_neg hkr]; exact Int.le_refl _) $$ H)
    iframe Hp Hf Ha
    rw [hwr]
    iexact Hsw

/-! ### A leader's `Commit` line (amendment A6, Q22) -/

/-- (Amendment A6) **Every `okL` log agrees with a commit-certified leader log below the commit index**:
`es`, a full log of the leader of `T` with raft's commit justification `commitJ γ es c T`, and any log
`okL` names for acknowledgements of `T` have the same term at every index `j ≤ c` the latter reaches: a
leader's full log of a term `≥ T` (`commitJ_leadFull`), a commit quorum's log of an earlier term at an
index within its quorum index (`commitJ_leadFull` the other way, at `T`'s leader), the bootstrap log
(`logRecs_boot_termAt`). -/
theorem okL_commitAgree (γ : RaftNames) (es X : List EntryM) (c T : w64) (B : Int) (j : w64)
    (hw : PlogWf base0 es) (hc : uint.Z c ≤ es.length) (hj : uint.Z j ≤ uint.Z c)
    (hs : (plogTermAt base0 X j).isSome) :
    votesTbl (GF := GF) γ ∗ logRecs γ base0 es ∗ commitJ γ es c T ∗ leadFull γ T es ∗ okL γ T B j X ⊢
      votesTbl γ ∗ ⌜plogTermAt base0 X j = plogTermAt base0 es j⌝ := by
  have hjX : uint.Z j ≤ X.length := by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    have := (plogTermAt_some_range _ _ _ _ hx).2
    unfold plogLastIndexZ at this; rw [base0_index] at this; omega
  iintro ⟨Htbl, #Hr, #Hcj, #HL, #Hok⟩
  unfold okL
  icases Hok with (⟨%t'', %Ht, #Hf⟩ | ⟨%t'', %n'', %Ht, #Hq⟩ | %Hb)
  · icases keep_pure (commitJ_leadFull γ es X c T t'' hw hc Ht.1) $$ [$Htbl $Hr $Hcj $Hf]
      with ⟨⟨Htbl, -⟩, %hag⟩
    iframe Htbl; ipureintro; exact hag j hj hjX
  · icases cq_full γ t'' n'' X $$ Hq with ⟨%hwX, #HrX⟩
    icases cq_base γ t'' n'' X $$ Hq with ⟨%hXn, -⟩
    have hnX : uint.Z n'' ≤ X.length := by
      have := (plogTermAt_some_range _ _ _ _ hXn).2
      unfold plogLastIndexZ at this; rw [base0_index] at this; omega
    ihave #HcjX : commitJ γ X n'' t'' $$ []
    · unfold commitJ
      iright; iexists t'', n'', X
      iframe Hq
      ipureintro; exact ⟨Int.le_refl _, Int.le_refl _, rfl⟩
    icases keep_pure (commitJ_leadFull γ X es n'' t'' T hwX hnX (by omega)) $$ [$Htbl $HrX $HcjX $HL]
      with ⟨⟨Htbl, -⟩, %hag⟩
    iframe Htbl; ipureintro; exact (hag j Ht.2 (by omega)).symm
  · obtain ⟨hjb, rfl⟩ := Hb
    icases logRecs_boot_termAt γ es hw $$ Hr with %Hbe
    iframe Htbl; ipureintro; exact Hbe j hjb (by omega)

/-- (Amendment A6) **An acknowledgement's history at a commit-certified index**: a log with the history
of an acknowledgement `(T, mi)` of the leader's term, `mi ≥ c`, has at `c` the term of the leader's
commit-certified log `es` (every `okL` log does, `okL_commitAgree`, so no two disagree). -/
theorem hist_commitAgree (γ : RaftNames) (F es : List EntryM) (c T mi : w64) (B : Int)
    (hw : PlogWf base0 es) (hc : uint.Z c ≤ es.length) (hc0 : 0 < uint.Z c) (hcm : uint.Z c ≤ uint.Z mi) :
    votesTbl (GF := GF) γ ∗ logRecs γ base0 es ∗ commitJ γ es c T ∗ leadFull γ T es ∗ hist γ F T mi B ⊢
      votesTbl γ ∗ ⌜plogTermAt base0 F c = plogTermAt base0 es c⌝ := by
  iintro ⟨Htbl, #Hr, #Hcj, #HL, #Hh⟩
  unfold hist
  icases Hh $$ %c %(⟨hc0, hcm⟩ : 0 < uint.Z c ∧ uint.Z c ≤ uint.Z mi)
    with (⟨%X, #HX, %Hs⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd⟩)
  · icases okL_commitAgree γ es X c T B c hw hc (Int.le_refl _) Hs.1 $$ [$Htbl $Hr $Hcj $HL $HX]
      with ⟨Htbl, %h⟩
    iframe Htbl; ipureintro; rw [← Hs.2, h]
  · icases okL_commitAgree γ es X1 c T B j' hw hc Hj' Hd.1 $$ [$Htbl $Hr $Hcj $HL $H1] with ⟨Htbl, %h1⟩
    icases okL_commitAgree γ es X2 c T B j' hw hc Hj' Hd.2.1 $$ [$Htbl $Hr $Hcj $HL $H2] with ⟨Htbl, %h2⟩
    exact absurd (h1.trans h2.symm) Hd.2.2

/-- (Amendment A6, Q22) **A leader's `Commit` line keeps `QuorumLogF`** (the sufficiency of A6): the
specification's `AdvanceCommitIndex` at a leader `i` of term `T` (`advanceCommitIndex_cases`) raises its
commit index to `c`, agreed by a quorum `Q` of its match indices. The new committed prefix `P` (its log up
to `c`) takes the witness `T`: its certificate is raft's own after `maybeCommit` (the leader's facts at
the new state, `allFacts γ C σ'`: `commitIn` at `c` and term `T`, `CommitCert`); every member `k ≠ i` of
`Q` has its acknowledgement of `matchIndex k ≥ c` at `T` with its history over its current log
(`AckHists`), which has at `c` the leader's term there (`hist_commitAgree`), so `k` holds `P`
(`prefix_of_termAt`, `LogMatchingInv`) at a term `≥ T`; the leader holds it at `T`; so the servers
lacking it are within `Q`'s complement, no quorum (`KeptFrom`). Nothing else moves. -/
theorem quorumLogF_commit (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (i : Etcdraft.ID)
    (hsrv : σ.server = confAbs C) (hi : i ∈ σ.server) (hsi : TraceSpecInv.SpecInv σ)
    (hstep : σ.advanceCommitIndex i = some σ') :
    votesTbl (GF := GF) γ ∗ allFacts γ C σ' ∗ QuorumLogF γ C σ ⊢ votesTbl γ ∗ QuorumLogF γ C σ' := by
  obtain ⟨hl, c, rfl, hc⟩ := advanceCommitIndex_cases hstep
  have hs : ∀ k, (σ.commitTo i c).s k =
      if k = i then { σ.s i with commitIndex := max (σ.s i).commitIndex c } else σ.s k := fun k => rfl
  have hF : ∀ k, ((σ.commitTo i c).s k).log = (σ.s k).log ∧
      ((σ.commitTo i c).s k).currentTerm = (σ.s k).currentTerm ∧
      ((σ.commitTo i c).s k).state = (σ.s k).state ∧
      ((σ.commitTo i c).s k).matchIndex = (σ.s k).matchIndex := by
    intro k; rw [hs]; split
    · rename_i h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have hT : ∀ k, (σ.s k).currentTerm ≤ ((σ.commitTo i c).s k).currentTerm := fun k => by
    rw [(hF k).2.1]; exact Int.le_refl _
  have hLd : ∀ j, ((σ.commitTo i c).s j).state = Etcdraft.leader → (σ.s j).state = Etcdraft.leader ∧
      ((σ.commitTo i c).s j).currentTerm = (σ.s j).currentTerm ∧
      ∀ k ∈ σ.server, ((σ.commitTo i c).s j).matchIndex k = (σ.s j).matchIndex k :=
    fun j h => ⟨by rw [← (hF j).2.2.1]; exact h, (hF j).2.1, fun k _ => by rw [(hF j).2.2.2]⟩
  have hcf : (σ.getConfig i) = σ.server := by
    simp only [Etcdraft.State.getConfig, hsi.cfgFixed i hi]
  iintro ⟨Htbl, #Hal', #H⟩
  iunfold QuorumLogF at H
  icases H with ⟨#Hq, #Ha⟩
  ihave #Ha' : AckHists γ C (σ.commitTo i c) $$ []
  · iapply ackHists_congr γ C σ (σ.commitTo i c) rfl (fun k => (hF k).1) hT (fun x hx _ => hx) hLd $$ Ha
  -- the other servers' committed prefixes and their witnesses are unchanged
  have hKold : ∀ k, k ≠ i ∨ c ≤ (σ.s i).commitIndex → committedL (σ.commitTo i c) k = committedL σ k := by
    intro k hk
    unfold committedL; rw [hs]; split
    · rename_i h; subst h
      rcases hk with hk | hk
      · exact absurd rfl hk
      · simp only; rw [Int.max_eq_left hk]
    · rfl
  by_cases hraise : c ≤ (σ.s i).commitIndex
  · iframe Htbl
    iunfold QuorumLogF
    iframe Ha'
    iapply quorumKept_mono γ C σ (σ.commitTo i c) rfl
      (fun k hk => ⟨k, hk, by rw [hKold k (.inr hraise)]; exact List.prefix_refl _⟩)
      (fun _ _ h => keptFrom_congr (σ := σ) (σ' := σ.commitTo i c) rfl (fun k => (hF k).1) hT h) $$ Hq
  rcases hc with hc | ⟨hc0, hcl, hq⟩
  · exact absurd hc hraise
  -- the leader's facts at the new state: its recorded log `es`, the commit certificate at `c` and `T`
  have hiC : i ∈ confAbs C := by rw [← hsrv]; exact hi
  obtain ⟨wi, hwiC, hwi⟩ := mem_confAbs_inv C i hiC
  ihave #Hal'' := Hal'
  iunfold allFacts at Hal''
  ihave #Hsi : srvFacts γ C wi ((σ.commitTo i c).s i) $$ []
  · have hse : (σ.commitTo i c).s i = (σ.commitTo i c).s (idAbs wi) := by rw [← hwi]
    rw [hse]
    iapply Hal'' $$ %wi %hwiC
  iunfold srvFacts at Hsi
  icases Hsi with ⟨%es, %pend, %Hpi, #Hri, -, #Hld, #Hci⟩
  obtain ⟨hli, hbi, hwfi, hleni, hci0, hcie, hti0, hti1, -, -⟩ := Hpi
  have hst : ((σ.commitTo i c).s i).state = Etcdraft.leader := by rw [(hF i).2.2.1]; exact hl
  simp only [hst, ↓reduceIte]
  icases Hld with ⟨-, #HLi, -⟩
  have hcnew : ((σ.commitTo i c).s i).commitIndex = c := by
    rw [hs, if_pos rfl]; exact Int.max_eq_right (by omega)
  rw [hcnew] at hcie
  rw [(hF i).2.1] at hti0 hti1
  simp only [hcnew, (hF i).2.1]
  rw [(hF i).1] at hli
  rw [List.length_append] at hleni
  have hwe : PlogWf base0 es :=
    PlogWfR_wf _ _ (PlogWfR_append_left _ _ _ hwfi) (by unfold plogLastIndexZ; rw [base0_index]; simp; omega)
  ihave #Hcj := commitIn_j γ es (W64 c) (W64 (σ.s i).currentTerm) $$ Hci
  have hcW : uint.Z (W64 c) = c := by word
  have hcN : ((c.toNat : Nat) : Int) = c := by omega
  -- every member of the quorum but the leader holds the new prefix at a term at least `T`
  icases allFacts_logMatching γ C (σ.commitTo i c) hsrv $$ Hal' with %hlm
  have hlm' : σ.logMatchingInv = true := by
    have h := hlm
    unfold Etcdraft.State.logMatchingInv at h ⊢
    simp only [fun k => (hF k).1] at h
    exact h
  ihave #HA : □ ∀ w, ⌜w ∈ C⌝ →
      ((⌜idAbs w ≠ i ∧ c ≤ (σ.s i).matchIndex (idAbs w)⌝ →
          AckHist γ C σ (idAbs w) (σ.s i).currentTerm ((σ.s i).matchIndex (idAbs w))) ∗
        srvFacts γ C w ((σ.commitTo i c).s (idAbs w)) ∗ logRecs γ base0 es ∗
        commitJ γ es (W64 c) (W64 (σ.s i).currentTerm) ∗ leadFull γ (W64 (σ.s i).currentTerm) es) $$ []
  · imodintro
    iintro %w %hw
    iframe Hri Hcj HLi
    isplitl
    · iintro %h
      iunfold AckHists at Ha
      icases Ha with ⟨-, #Hl⟩
      iapply Hl $$ %i %(idAbs w)
      ipureintro
      exact ⟨hi, by rw [hsrv]; exact (mem_confAbs C w).2 hw, hl, h.1, by omega⟩
    · iapply Hal'' $$ %w %hw
  icases votesTbl_forall_list γ
      (fun w => iprop((⌜idAbs w ≠ i ∧ c ≤ (σ.s i).matchIndex (idAbs w)⌝ →
          AckHist γ C σ (idAbs w) (σ.s i).currentTerm ((σ.s i).matchIndex (idAbs w))) ∗
        srvFacts γ C w ((σ.commitTo i c).s (idAbs w)) ∗ logRecs γ base0 es ∗
        commitJ γ es (W64 c) (W64 (σ.s i).currentTerm) ∗ leadFull γ (W64 (σ.s i).currentTerm) es))
      (fun w => iprop(⌜idAbs w ∈ σ.server → idAbs w ≠ i ∧ c ≤ (σ.s i).matchIndex (idAbs w) →
        (σ.s i).log.take c.toNat <+: (σ.s (idAbs w)).log ∧ (σ.s i).currentTerm ≤ (σ.s (idAbs w)).currentTerm⌝))
      (fun w => by
        iintro ⟨Htbl, #Hak, #Hsw, #Hr, #Hcj, #HL⟩
        by_cases hcond : idAbs w ≠ i ∧ c ≤ (σ.s i).matchIndex (idAbs w)
        · ihave #Hak' : AckHist γ C σ (idAbs w) (σ.s i).currentTerm ((σ.s i).matchIndex (idAbs w)) $$ []
          · iapply Hak; ipureintro; exact hcond
          iunfold AckHist at Hak'
          icases Hak' with ⟨%hpa, #Hak'⟩
          iunfold srvFacts at Hsw
          icases Hsw with ⟨%esk, %pk, %Hpk, -⟩
          obtain ⟨hlk, hbk, -⟩ := Hpk
          rw [(hF _).1] at hlk
          ihave Hh : ∃ B, hist γ (esk ++ pk) (W64 (σ.s i).currentTerm) (W64 ((σ.s i).matchIndex (idAbs w))) B $$ []
          · iapply Hak'; ipureintro; exact ⟨hlk, hbk⟩
          icases Hh with ⟨%B, #Hh⟩
          have hmW : uint.Z (W64 ((σ.s i).matchIndex (idAbs w))) = (σ.s i).matchIndex (idAbs w) := by
            have := hpa.2.2.2; word
          icases hist_commitAgree γ (esk ++ pk) es (W64 c) (W64 (σ.s i).currentTerm)
              (W64 ((σ.s i).matchIndex (idAbs w))) B hwe (by rw [hcW]; omega) (by rw [hcW]; omega)
              (by rw [hcW, hmW]; exact hcond.2) $$ [$Htbl $Hr $Hcj $HL $Hh] with ⟨Htbl, %hag⟩
          iframe Htbl
          ipureintro
          intro hwS _
          refine ⟨?_, hpa.2.1⟩
          exact prefix_of_termAt C σ i (idAbs w) hi hwS hlm' es pend (esk ++ pk) c.toNat hli hlk
            (by omega) (by omega) (by omega) (by rw [hcN]; exact hag)
        · iframe Htbl; ipureintro; intro _ h; exact absurd h hcond)
      C $$ [$Htbl $HA] with ⟨Htbl, #Hb⟩
  ihave %hB : ⌜∀ w ∈ C, idAbs w ∈ σ.server → idAbs w ≠ i ∧ c ≤ (σ.s i).matchIndex (idAbs w) →
      (σ.s i).log.take c.toNat <+: (σ.s (idAbs w)).log ∧
        (σ.s i).currentTerm ≤ (σ.s (idAbs w)).currentTerm⌝ $$ []
  · by_cases hc' : ∀ w ∈ C, idAbs w ∈ σ.server → idAbs w ≠ i ∧ c ≤ (σ.s i).matchIndex (idAbs w) →
        (σ.s i).log.take c.toNat <+: (σ.s (idAbs w)).log ∧ (σ.s i).currentTerm ≤ (σ.s (idAbs w)).currentTerm
    · ipureintro; exact hc'
    · obtain ⟨w, hn⟩ := Classical.not_forall.mp hc'
      obtain ⟨hw, hn2⟩ := Classical.not_imp.mp hn
      ihave %hw' := Hb $$ %w %hw
      exact absurd hw' hn2
  iframe Htbl
  iunfold QuorumLogF
  iframe Ha'
  iunfold QuorumKept at Hq
  iunfold QuorumKept
  imodintro
  iintro %k %hk
  by_cases hki : k = i
  · subst hki
    iexists (σ.s k).currentTerm
    have hP : committedL (σ.commitTo k c) k = (σ.s k).log.take c.toNat := by
      unfold committedL; rw [(hF k).1, hcnew]
    rw [hP]
    isplitr
    · ipureintro
      -- the servers lacking the prefix are within the quorum's complement
      unfold KeptFrom lackingAt
      rw [hcf] at hq
      refine TraceSpecInv.isQuorum_filter_mono (fun j hj hp => ?_) (isQuorum_filter_not hq)
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, Int.not_le]
      apply Classical.byContradiction; intro hn
      have hjc : c ≤ (σ.s k).matchIndex j := by omega
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp
      by_cases hjk : j = k
      · subst hjk
        rcases hp with hp | hp
        · rw [(hF j).1, isPrefix_of_prefix _ _ (List.take_prefix _ _)] at hp; cases hp
        · rw [(hF j).2.1] at hp; omega
      · have hjS : j ∈ σ.server := hj
        have hj' : j ∈ confAbs C := by rw [← hsrv]; exact hj
        obtain ⟨w, hw, rfl⟩ := mem_confAbs_inv C j hj'
        obtain ⟨h1, h2⟩ := hB w hw hjS ⟨hjk, hjc⟩
        rcases hp with hp | hp
        · rw [(hF _).1, isPrefix_of_prefix _ _ h1] at hp; cases hp
        · rw [(hF _).2.1] at hp; omega
    · iunfold CommitCert
      iexists es, W64 c
      iframe Hri Hcj
      ipureintro
      refine ⟨?_, hwe, by rw [hcW]; omega, by omega, hti0, hti1⟩
      have hn : uint.nat (W64 c) = c.toNat := by
        have : uint.nat (W64 c) = (uint.Z (W64 c)).toNat := rfl
        rw [this, hcW]
      rw [hn, hli, logAbs_take, List.take_append_of_le_length (by omega)]
      exact List.prefix_refl _
  · ihave Hk := Hq $$ %k %hk
    icases Hk with ⟨%t, %hKt, #Hc⟩
    iexists t
    rw [hKold k (.inl hki)]
    iframe Hc
    ipureintro
    exact keptFrom_congr (σ := σ) (σ' := σ.commitTo i c) rfl (fun k => (hF k).1) hT hKt

end ghost

end EtcdGrove
end Perennial
