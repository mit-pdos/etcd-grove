/-
Lean-first (no Rocq counterpart). **Amendment A5 (Q21): `QuorumLogF`'s sufficiency** (2026-11-11,
trace-check, `notes/decisions.md`, "Amendment A5 (Q21)"). Raft-internal (not on `etc/api/raft.txt`).

The amended clause (`TracedCap.lean`): every server's committed prefix `P` is kept from a term `t` on
(`KeptFrom`: the servers holding `P` at a term `≥ t` a quorum, every append request in flight of a term
`≥ t` agreeing with `P`, every leader of a term `≥ t` holding `P`), `t` a term `P` was committed at or
after (`CommitCert`: raft's `commitJ` at `t`).

1. **An accepted append request's receive line keeps it** (task 3 of Q8 stage 1's slice 22b, the
   blocker of Q21), round by round of the specification's `AcceptAppendEntriesRequest` at a follower
   of the request's term: a truncation (`ConflictAppendEntriesRequest`, the last entry dropped while the
   request conflicts, `quorumLogF_conflict`), the append (`NoConflictAppendEntriesRequest`,
   `quorumLogF_noConflict`) and the reply with the raised commit index (`AppendEntriesAlreadyDone`,
   `quorumLogF_alreadyDone`, the receiver's new committed prefix a prefix of the sender's). A truncating
   receiver at a term `≥ t` holding `P` keeps it (the request agrees with `P`, so its conflict is past
   `P`); one below `t` is not counted.
2. **The `BecomeLeader` line keeps the leader clause** (`commitCert_camp`): a new leader of a term
   `T ≥ t` has `P` in its campaign log, by raft's leader completeness (`lc_core`) from the commit
   quorum the certificate names (or the bootstrap log), the term log of `T` not yet created (as
   `commit_le_camp`, `TraceSimLeader.lean`).
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

/-- **A truncation keeps `KeptFrom`** (amendment A5's point): at a follower `r` of the request's term,
the request in flight and its previous entry within `r`'s log, a server holding `P` at a term `≥ t` —
`r` among them — keeps it: the request, of `r`'s term `≥ t`, agrees with `P` (`KeptFrom`'s message
clause), so the conflict is past `P` and the dropped last entry too. A server below `t` (the truncating
receiver of `notes/decisions.md`, "Q8 stage 1 (slice 22b)", holding `P` by coincidence) is not counted.
The other servers, the leaders and the bags are unchanged. -/
theorem keptFrom_conflict {σ σ' : Etcdraft.State} {r : Etcdraft.ID} {m : Etcdraft.Msg}
    {P : List Etcdraft.Entry} {t : Int}
    (hm : m ∈ σ.messages.domain) (hty : m.type = .appendEntriesRequest)
    (hf : (σ.s r).state = Etcdraft.follower) (hterm : m.term = (σ.s r).currentTerm)
    (hp0 : 0 ≤ m.prevLogIndex) (hple : m.prevLogIndex ≤ (σ.s r).log.length)
    (hstep : σ.conflictAppendEntriesRequest r (m.prevLogIndex + 1) m = .ok (some σ'))
    (h : KeptFrom σ P t) : KeptFrom σ' P t := by
  obtain ⟨-, hnc, rfl⟩ := conflictRound_eq hstep
  obtain ⟨k, e, he, hkl, hne⟩ := conflict_pos hp0 hple hnc
  have hs : ∀ j, (σ.upd r (fun v => { v with log := (σ.s r).log.take ((σ.s r).log.length - 1) })).s j =
      if j = r then { σ.s r with log := (σ.s r).log.take ((σ.s r).log.length - 1) } else σ.s j := by
    intro j; unfold Etcdraft.State.upd; rfl
  refine keptFrom_of (σ := σ) rfl ?_ ?_ (fun x hx _ _ => .inl hx) h
  · intro j _ hpj htj
    rw [hs]
    by_cases hj : j = r
    · rw [if_pos hj]
      rw [hj] at hpj htj
      refine ⟨?_, htj⟩
      -- the conflict is past `P`: the request agrees with `P` where both have an entry
      have hag := h.2.1 m (List.mem_append_left _ hm) hty (by rw [hterm]; exact htj)
      have hPk : P.length ≤ m.prevLogIndex.toNat + k := by
        apply Nat.le_of_not_lt; intro hlt
        have h1 := hag k e he hlt
        rw [← prefix_getElem?_of_lt hpj hlt, h1] at hne
        exact hne rfl
      show P <+: (σ.s r).log.take ((σ.s r).log.length - 1)
      have hP : P = (σ.s r).log.take P.length := List.prefix_iff_eq_take.mp hpj
      have := List.take_prefix P.length ((σ.s r).log.take ((σ.s r).log.length - 1))
      rw [List.take_take, Nat.min_eq_left (by omega), ← hP] at this
      exact this
    · rw [if_neg hj]; exact ⟨hpj, htj⟩
  · intro l _ hll hlt
    rw [hs] at hll hlt ⊢
    split at hll
    · rename_i hl; subst hl; simp only at hll; rw [hf] at hll; exact absurd hll (by decide)
    · rename_i hl; simp only [hl, ↓reduceIte] at hlt ⊢; exact ⟨hll, hlt, id⟩

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
  refine keptFrom_of (σ := σ) rfl ?_ ?_ (fun x hx _ _ => .inl hx) h
  · intro j _ hpj htj
    rw [hs]; split
    · rename_i hj; subst hj; exact ⟨hpj.trans (List.prefix_append _ _), htj⟩
    · exact ⟨hpj, htj⟩
  · intro l _ hll hlt
    rw [hs] at hll hlt ⊢
    split at hll
    · rename_i hl; subst hl; simp only at hll hlt ⊢
      exact ⟨hll, hlt, fun hp => hp.trans (List.prefix_append _ _)⟩
    · rename_i hl; simp only [hl, ↓reduceIte] at hlt ⊢; exact ⟨hll, hlt, id⟩

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


/-- **A prefix of an abstract log from raft's terms**: a log `es` whose raft terms agree with `F`'s
below `n` (both at least `n` long) has, up to `n`, a prefix of `F`'s abstract log. -/
theorem logAbs_take_prefix_of_terms (C : List w64) (es F : List EntryM) (n : Nat)
    (hn1 : n ≤ es.length) (hn2 : n ≤ F.length)
    (hT : ∀ k, k < n → es[k]?.map EntryM.Term' = F[k]?.map EntryM.Term') :
    logAbs C C.length 1 (es.take n) <+: logAbs C C.length 1 F := by
  have hEq : logAbs C C.length 1 (es.take n) = logAbs C C.length 1 (F.take n) := by
    apply List.ext_getElem?
    intro k
    rw [logAbs_getElem?, logAbs_getElem?, List.getElem?_take, List.getElem?_take]
    split
    · rename_i hk
      have h := hT k hk
      rw [List.getElem?_eq_getElem (by omega : k < es.length),
        List.getElem?_eq_getElem (by omega : k < F.length)] at h ⊢
      simp only [Option.map_some, Option.some.injEq] at h ⊢
      exact entAbs_eq C C.length _ _ _ h
    · rfl
  rw [hEq]
  exact logAbs_prefix C C.length 1 _ _ (List.take_prefix _ _)

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A truncation round keeps `QuorumLogF`** (amendment A5, the sufficiency of Q21): an accepted
append request's `ConflictAppendEntriesRequest` at a follower of its term (`keptFrom_conflict`), every
committed prefix and its certificate unchanged (`committedL_conflict`). -/
theorem quorumLogF_conflict (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (r : Etcdraft.ID)
    (m : Etcdraft.Msg) (hm : m ∈ σ.messages.domain) (hty : m.type = .appendEntriesRequest)
    (hf : (σ.s r).state = Etcdraft.follower) (hterm : m.term = (σ.s r).currentTerm)
    (hp0 : 0 ≤ m.prevLogIndex) (hple : m.prevLogIndex ≤ (σ.s r).log.length)
    (hstep : σ.conflictAppendEntriesRequest r (m.prevLogIndex + 1) m = .ok (some σ')) :
    QuorumLogF (GF := GF) γ C σ ⊢ QuorumLogF γ C σ' := by
  have hsrv : σ'.server = σ.server := by
    obtain ⟨-, -, rfl⟩ := conflictRound_eq hstep; rfl
  exact quorumLogF_mono γ C σ σ' hsrv
    (fun i hi => ⟨i, hi, by rw [committedL_conflict hp0 hple hstep]; exact List.prefix_refl _⟩)
    (fun _ _ h => keptFrom_conflict hm hty hf hterm hp0 hple hstep h)

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

/-- A reply's bags: the old ones' but the request, and the reply. -/
theorem mem_msgs_reply (σ : Etcdraft.State) (x q y : Etcdraft.Msg)
    (hy : y ∈ (σ.reply x q).messages.domain ++ (σ.reply x q).pendingMessages.domain) :
    y ∈ σ.messages.domain ++ σ.pendingMessages.domain ∨ y = x := by
  rw [TraceSpecInv.reply_eq] at hy
  rcases TraceSpecInv.mem_msgs_send _ _ y hy with hy | rfl
  · left
    rcases List.mem_append.mp hy with hy | hy
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hy)
    · exact List.mem_append_right _ hy
  · right; rfl

/-- **A reply with the receiver's commit index raised to `c` keeps `QuorumLogF`**, `c` within the
request's sender's commit index (`ReqCommitC`) and the two committed prefixes comparable after it
(`LogInv`, `hcmp`): the receiver's new committed prefix is its old one's prefix or its sender's
(`committedL_raise_prefix`), whose witness it takes; the reply is not an append request. -/
theorem quorumLogF_commitReply (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (r : Etcdraft.ID)
    (c : Int) (x q : Etcdraft.Msg) (src : Etcdraft.ID) (hsrc : src ∈ σ.server)
    (hc : c ≤ (σ.s src).commitIndex) (hsl : (σ.s src).commitIndex ≤ (σ.s src).log.length)
    (hx : x.type ≠ .appendEntriesRequest)
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
          (hF k).1 (by rw [hs, if_pos rfl])
          (fun j hj => by unfold committedL; rw [(hF j).1, hs, if_neg hj])
          hc hsl hcmp with h | h
      · exact ⟨k, hk, h⟩
      · exact ⟨src, hsrc, h⟩
    · exact ⟨k, hk, by unfold committedL; rw [hs, if_neg hkr]; exact List.prefix_refl _⟩
  · intro P t h
    refine keptFrom_congr (σ := σ) (σ' := (σ.commitTo r c).reply x q) rfl (fun k => (hF k).1) (fun k => by rw [(hF k).2.1]; exact Int.le_refl _)
      (fun k hl => ⟨by rw [← (hF k).2.2]; exact hl, (hF k).2.1⟩) ?_ h
    intro y hy hty
    rcases mem_msgs_reply _ x q y hy with hy | rfl
    · exact hy
    · exact absurd hty hx

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
        exact quorumLogF_commitReply γ C σ r _ _ m m.source hsrc hcs hsl (by simp) hcmp
      · -- no raise: the reply only
        refine quorumLogF_congr γ C σ _ rfl (fun _ => rfl) (fun _ => rfl) (fun _ => Int.le_refl _)
          (fun _ h => ⟨h, rfl⟩) ?_
        intro y hy hty'
        rcases mem_msgs_reply _ _ m y hy with hy | rfl
        · exact hy
        · exact absurd hty' (by simp)
    · rename_i h1; simp only [h1, ↓reduceIte] at hcmp
      exact quorumLogF_commitReply γ C σ r _ _ m m.source hsrc
        (Int.le_trans (Int.min_le_left _ _) hcs) hsl (by simp) hcmp


/-- **The `BecomeLeader` line keeps `KeptFrom`'s leader clause** (amendment A5, the reason for
`CommitCert`): a new leader `i` of a term `T ≥ t`, before its term log exists (`terms !! T = none`, as
at its hook: `becomeLeader_hyps`, `TraceSimLeader.lean`), has a prefix committed at a term at most
`t` in its campaign log `F0`, its log in the specification's state: within the bootstrap log, both
start with it; a commit quorum of an earlier term than `T`, raft's leader completeness (`lc_core`)
puts its log in `F0` to its index; one of `T` itself names a record of an entry of `T`, which no term
log of `T` backs (`isEntryR_term_ne`). As `commit_le_camp`, with the agreement of the terms. -/
theorem commitCert_camp (γ : RaftNames) (C : List w64) (P : List Etcdraft.Entry) (t : Int)
    (F0 : List EntryM) (i T : w64) (γm : GName) (terms : GMap w64 TermRec)
    (hγm : γ.reTerms !! i = some γm) (hfree : terms !! T = none) (htT : t ≤ uint.Z T) :
    ⊢ votesTbl (GF := GF) γ -∗ CommitCert γ C P t -∗ isLeader γ i T -∗ isCamp γ i T F0 -∗
      logRecs γ base0 F0 -∗ ghostMapAuth γm 1 terms -∗ ⌜P <+: logAbs C C.length 1 F0⌝ := by
  iintro Htbl Hcc #Hl #Hc #HrF Ha
  iunfold CommitCert at Hcc
  icases Hcc with ⟨%es, %c, %Hp, #Hr, #Hj⟩
  obtain ⟨hP, hw, hc, hes, ht0, ht1⟩ := Hp
  icases isCamp_ok γ i T F0 $$ Hc with %Hcok
  have HwF := Hcok.1
  have hcn : (uint.nat c : Int) = uint.Z c := by word
  -- the terms of `F0` and `es` agree up to `c`, within `F0`
  ihave %Hag : ⌜uint.Z c ≤ F0.length ∧
      ∀ j : w64, uint.Z j ≤ uint.Z c → plogTermAt base0 F0 j = plogTermAt base0 es j⌝ $$ [Htbl Ha]
  · iunfold commitJ at Hj
    icases Hj with (%Hb0 | ⟨%t', %n, %G, #Hq, %Hcn⟩)
    · -- the bootstrap log, which both start with
      icases isCamp_boot γ i T F0 $$ Hc with %Hb
      icases logRecs_boot_termAt γ es hw $$ Hr with %Hbe
      icases logRecs_boot_termAt γ F0 HwF $$ HrF with %HbF
      have HbL := Hb.1.length_le
      ipureintro
      refine ⟨by omega, fun j hj => ?_⟩
      rw [← HbF j (by omega) (by omega), ← Hbe j (by omega) (by omega)]
    obtain ⟨Hcn, Htt, HGe⟩ := Hcn
    have htW : uint.Z (W64 t) = t := by word
    rw [htW] at Htt
    by_cases hn0 : uint.Z c = 0
    · ipureintro
      refine ⟨by omega, fun j hj => ?_⟩
      have : j = W64 0 := by word
      subst this
      rfl
    icases cq_base γ t' n G $$ Hq with ⟨%HGn, #HGl⟩
    icases leadFull_wf γ t' G $$ HGl with ⟨%HwG, #HrG⟩
    have hn1 : 0 < uint.Z n := by omega
    by_cases hT : t' = T
    · -- a commit quorum of `T`: an entry of `T` with a record, which no term log backs
      subst hT
      have HGn' := HGn
      rw [show base0 = entryID.mk (W64 0) (W64 0) from rfl, plogTermAt_base0 G n hn1] at HGn'
      obtain ⟨x, hx, hxt⟩ : ∃ x, G[uint.nat n - 1]? = some x ∧ x.Term' = t' := by
        cases h : G[uint.nat n - 1]? with
        | none => rw [h] at HGn'; cases HGn'
        | some x => rw [h] at HGn'; exact ⟨x, rfl, Option.some.inj HGn'⟩
      icases logRecs_isEntry γ base0 G _ x hx (by
          rw [base0_index]
          have h1 := uint_Z_lt n
          have h2 : ((uint.nat n : Nat) : Int) = uint.Z n := by word
          omega)
        $$ HrG with ⟨%pt, #He⟩
      icases isEntryR_term_ne γ i t' γm terms hγm hfree x pt $$ Hl Ha He with %Hne
      exact absurd hxt Hne
    · have Hlt : uint.Z t' < uint.Z T := by
        have : uint.Z t' ≠ uint.Z T := fun h => hT (uint_Z_inj.mp h)
        omega
      have Hcl := camp_last T F0 Hcok
      icases lc_core γ ((uint.Z T).toNat + 1) T t' n G i F0 F0
          (by have := uint_Z_nonneg T; omega) Hlt HwF Hcl
          $$ Htbl Hq Hl Hc HrF with %HnF
      have HnFr := (plogTermAt_some_range _ _ _ _ HnF).2
      have HlenF : plogLastIndexZ base0 F0 = (F0.length : Int) := by
        unfold plogLastIndexZ; rw [base0_index]; simp
      have HlenG : plogLastIndexZ base0 G = (G.length : Int) := by
        unfold plogLastIndexZ; rw [base0_index]; simp
      have HnG := (plogTermAt_some_range _ _ _ _ HGn).2
      icases full_match γ F0 G n HwF HwG.1 (by rw [HnF]; rfl) (by rw [HnF, HGn])
          $$ HrF HrG with %HFG
      icases full_match γ G es c HwG.1 hw
          (plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg _, by omega⟩) HGe
          $$ HrG Hr with %HGe'
      ipureintro
      refine ⟨by omega, fun j hj => ?_⟩
      rw [HFG j (by omega), HGe' j hj]
  obtain ⟨hcF, Hag⟩ := Hag
  ipureintro
  by_cases hn0 : uint.nat c = 0
  · rw [hn0, List.take_zero] at hP
    simp only [logAbs, List.mapIdx_nil] at hP
    rw [List.prefix_nil.mp hP]; exact List.nil_prefix
  have hT := terms_of_plog es F0 (uint.nat c) (by have := uint_Z_lt c; omega) (fun j hj =>
    (Hag j (by omega)).symm)
  exact hP.trans (logAbs_take_prefix_of_terms C es F0 (uint.nat c) (by omega) (by omega) hT)

end ghost

end EtcdGrove
end Perennial
