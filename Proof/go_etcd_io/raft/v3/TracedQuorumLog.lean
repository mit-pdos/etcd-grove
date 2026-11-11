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

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An append round keeps `QuorumLogF`** (`NoConflictAppendEntriesRequest`). -/
theorem quorumLogF_noConflict (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r : Etcdraft.ID)
    (index : Int) (m : Etcdraft.Msg)
    (hstep : σ.noConflictAppendEntriesRequest r index m = .ok (some σ')) :
    QuorumLogF (GF := GF) γ C σ ⊢ QuorumLogF γ C σ' := by
  have hsrv : σ'.server = σ.server := by
    obtain ⟨-, -, _, rfl⟩ := noConflictRound_eq hstep; rfl
  exact quorumLogF_mono γ C σ σ' hsrv
    (fun i hi => ⟨i, hi, by rw [committedL_noConflict hstep]; exact List.prefix_refl _⟩)
    (fun _ _ h => keptFrom_noConflict hstep h)

/-- **A reply with the receiver's commit index raised to `c` keeps `QuorumLogF`**, `c` within the
request's sender's commit index (`ReqCommitC`) and the two committed prefixes comparable after it
(`LogInv`, `hcmp`): the receiver's new committed prefix is its old one's prefix or its sender's
(`committedL_raise_prefix`), whose witness it takes. -/
theorem quorumLogF_commitReply (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (r : Etcdraft.ID)
    (c : Int) (x q : Etcdraft.Msg) (src : Etcdraft.ID) (hsrc : src ∈ σ.server)
    (hc : c ≤ (σ.s src).commitIndex) (hsl : (σ.s src).commitIndex ≤ (σ.s src).log.length)
    (hcmp : TraceSpecInv.CommittedCmp ((σ.commitTo r c).reply x q) r src) :
    QuorumLogF (GF := GF) γ C σ ⊢ QuorumLogF γ C ((σ.commitTo r c).reply x q) := by
  have hs : ∀ k, ((σ.commitTo r c).reply x q).s k =
      if k = r then { σ.s r with commitIndex := max (σ.s r).commitIndex c } else σ.s k := by
    intro k; rfl
  have hF : ∀ k, (((σ.commitTo r c).reply x q).s k).log = (σ.s k).log ∧
      (((σ.commitTo r c).reply x q).s k).currentTerm = (σ.s k).currentTerm ∧
      (((σ.commitTo r c).reply x q).s k).state = (σ.s k).state := by
    intro k; rw [hs]; split <;> simp_all
  refine quorumLogF_mono γ C σ _ rfl ?_ ?_
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

/-- **The reply round keeps `QuorumLogF`** (`AppendEntriesAlreadyDone`, the receiver's commit index
raised to at most the request's, within its sender's: `ReqCommitC`; `quorumLogF_commitReply`), given
the new state's `LogInv` for the receiver and the sender (`hcmp`, from `allFacts_logInv` there). -/
theorem quorumLogF_alreadyDone (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r j : Etcdraft.ID)
    (index : Int) (m : Etcdraft.Msg) (hsi : TraceSpecInv.SpecInv σ) (hco : TraceSim.CommitOk σ)
    (hm : m ∈ σ.messages.domain) (hty : m.type = .appendEntriesRequest)
    (hstep : σ.appendEntriesAlreadyDone r j index m = some σ')
    (hcmp : TraceSpecInv.CommittedCmp σ' r m.source) :
    QuorumLogF (GF := GF) γ C σ ⊢ QuorumLogF γ C σ' := by
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
        exact quorumLogF_congr γ C σ _ rfl (fun _ => rfl) (fun _ => rfl) (fun _ => Int.le_refl _)
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
    (hidx : m.prevLogIndex = uint.Z idx) (hents : m.entries = logAbs C C.length (uint.nat idx + 1) ents) :
    votesTbl (GF := GF) γ ∗ QuorumLogF γ C σ ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ⊢
      votesTbl γ ∗ QuorumLogF γ C σ' := by
  have hsrv : σ'.server = σ.server := by
    obtain ⟨-, -, rfl⟩ := conflictRound_eq hstep; rfl
  iintro ⟨Htbl, #Hq, #Hp, #Hf⟩
  iunfold QuorumLogF at Hq
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

end ghost

end EtcdGrove
end Perennial
