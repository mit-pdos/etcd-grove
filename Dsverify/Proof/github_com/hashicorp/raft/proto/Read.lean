/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Read.lean (241f27e).
-/
/-
`proto` (stage 2) — snapshots and the read bound: what a read outside the log (`Raft.Barrier`,
`Raft.VerifyLeader`, then a read of the FSM's state) may rely on, as pure laws of the model.

**Snapshots.** A goroutine that needs an *upper* bound on the protocol state at some instant (a
client's call: what any FSM may have applied by then; a follower's heartbeat response: its term
then) cannot keep it as a persistent fact about the current state (it does not stay true). It keeps
a *snapshot* `Snap`: the voters' terms and durable prefixes and the leader logs' lengths at that
instant, numbered by the order snapshots were taken (`idx`). (A snapshot is this countable
projection of `PState`, not a `PState`: ghost state stores only countable values.) `snapOf σ n` is
the snapshot of `σ`; `SnapOK σ s` is what the current state `σ` knows of an earlier snapshot `s`
(it is preserved by every step, `snapOK_grows`).

**The read bound.** A read begins at a snapshot `sc` (the client's call). What any FSM may have
applied by then is at most the voters' durable prefixes in `sc` (`lastApplied ≤ dur`), and every
durable prefix is covered by a publication (`IPub`): a commit index some leader stored with
`setCommitIndex` while leading.
* `read_bound` (VerifyLeader): if `T` has a leader and a quorum each had a term `≤ T` after `sc`
  (the verify quorum: each answered a heartbeat sent after the read began, with `j`'s term `T`;
  so already at `sc` its term was `≤ T`), every durable prefix of `sc` is in `llog T`'s election
  part (`≤ len0 T`) or is covered by a publication of `T` itself (which `j`'s main loop handed to
  its FSM before it answers the verify).
* `read_bound_barrier` (Barrier): if the entry at `b` of term `T` (a barrier appended after `sc`:
  `llog T` was shorter than `b` at `sc`) is committed, every durable prefix of `sc` is below `b`.

Both are proved from `IPub`, leader completeness (`ILC`), "acknowledgements imply term"
(`IAcks`), quorum intersection, log matching and `Grows` (`SnapOK` keeps, for each voter, the
publication covering its prefix at `sc` and the quorum whose acknowledgements made it committed,
each of whose members had reached its term at `sc`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Kinds

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ## Snapshots -/

/-- A snapshot of the protocol state: its number (snapshots are numbered in the order they were
taken), each server's term and durable-prefix length, and the length of `llog T` for `T` below
`llens.length` (`0` beyond: no leader). -/
structure Snap where
  idx : Nat
  terms : List (SID × Nat)
  durs : List (SID × Nat)
  llens : List Nat
deriving DecidableEq, Inhabited

/-- The value of `i` in an association list (`0` if absent). -/
def alookup (l : List (SID × Nat)) (i : SID) : Nat := ((l.find? (fun p => p.1 = i)).map (·.2)).getD 0

/-- Server `i`'s term at the snapshot. -/
def Snap.term (s : Snap) (i : SID) : Nat := alookup s.terms i

/-- Server `i`'s durable-prefix length at the snapshot. -/
def Snap.dur (s : Snap) (i : SID) : Nat := alookup s.durs i

/-- The length of the leader log of `T` at the snapshot. -/
def Snap.llen (s : Snap) (T : Nat) : Nat := (s.llens[T]?).getD 0

/-- The frontier of what any FSM may have applied at the snapshot: the largest durable prefix (a
server's FSM applies only entries of its durable prefix: `lastApplied ≤ dur`). -/
def Snap.maxDur (s : Snap) : Nat := (s.durs.map (·.2)).foldr max 0

/-- The snapshot of `σ`, number `n`. -/
def snapOf (σ : PState) (n : Nat) : Snap where
  idx := n
  terms := σ.srvs.map (fun i => (i, σ.term i))
  durs := σ.srvs.map (fun i => (i, (σ.srv i).dur.1))
  llens := (List.range (σ.maxT + 1)).map (fun T => (σ.llog T).length)

/-- `s1` was taken no later than `s2`: its number, terms, durable prefixes and leader-log lengths
are at most `s2`'s. -/
def snapLe (s1 s2 : Snap) : Prop :=
  s1.idx ≤ s2.idx ∧ (∀ i, s1.term i ≤ s2.term i) ∧ (∀ i, s1.dur i ≤ s2.dur i) ∧
  (∀ T, s1.llen T ≤ s2.llen T)

/-- **What the current state `σ` knows of an earlier snapshot `s`**: its keys are the servers (in
order, so `Snap.term`/`Snap.dur` read each server's own entry and `Snap.maxDur` is the largest
server's prefix); its terms, durable prefixes
and leader-log lengths are at most `σ`'s; the leader logs' entries it counted are still there and
each is counted in its own term's leader log (log matching at `s`); a leader log it counted
non-empty had its leader elected by then (its election part was counted); each server's durable prefix
at `s` is `0` or covered by a publication `(T', k)` whose recorded commit `(T', k' ≥ k, p)` was in
`llog T'` at `s` and was acknowledged by a quorum of its configuration (the entry at `p` of
`llog T'`) each of whose members had reached `T'` at `s`; and (stage 4) every early vote of a term
`T ≠ 1` whose leader log was counted non-empty (a vote cast before that leader existed, so before
`s`) was cast by a server that had reached that term at `s` (review T1-3: not for `T = 1`, which
never has a leader, so all its votes are early and may come later; the read bound uses the clause
only for a leader's term `T₁ ≥ 2`; kept by `Grows`' last conjunct: no new early vote of a term
with a leader). -/
def SnapOK (σ : PState) (s : Snap) : Prop :=
  s.terms.map (·.1) = σ.srvs ∧ s.durs.map (·.1) = σ.srvs ∧
  (∀ i ∈ σ.srvs, s.term i ≤ σ.term i ∧ s.dur i ≤ (σ.srv i).dur.1) ∧
  (∀ i, i ∉ σ.srvs → s.term i = 0 ∧ s.dur i = 0) ∧
  (∀ T, s.llen T ≤ (σ.llog T).length) ∧
  (∀ T x e, x ≤ s.llen T → ent (σ.llog T) x = some e → x ≤ s.llen e.term) ∧
  (∀ T, s.llen T ≠ 0 → T = 1 ∨ (σ.leader T ≠ none ∧ σ.len0 T ≤ s.llen T)) ∧
  (∀ i ∈ σ.srvs, s.dur i = 0 ∨
    ∃ T' k k' p Q, s.dur i ≤ k ∧ k ≤ k' ∧ σ.pubs T' k ∧ σ.commits T' k' p ∧ k' ≤ s.llen T' ∧
      isQuorumOf (cfgAt σ (σ.llog T') p) Q ∧ (∀ j ∈ Q, T' ≤ s.term j ∧ ∃ m, k' ≤ m ∧ σ.acked j T' m)) ∧
  (∀ T j c L, s.llen T ≠ 0 → T ≠ 1 → σ.votes j T = some (c, L, true) → T ≤ s.term j)

/-! ### Helpers (internal) -/

theorem alookup_map_of_mem (vs : List SID) (f : SID → Nat) (i : SID) (h : i ∈ vs) :
    alookup (vs.map fun j => (j, f j)) i = f i := by
  induction vs with
  | nil => cases h
  | cons a vs ih =>
    unfold alookup
    by_cases ha : a = i
    · subst ha; simp
    · have hi : i ∈ vs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm ha
        · exact h
      have := ih hi
      unfold alookup at this
      simp [ha] at this ⊢
      exact this

theorem alookup_map_of_not_mem (vs : List SID) (f : SID → Nat) (i : SID) (h : i ∉ vs) :
    alookup (vs.map fun j => (j, f j)) i = 0 := by
  unfold alookup
  have : (vs.map fun j => (j, f j)).find? (fun p => decide (p.1 = i)) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    simp only [decide_eq_true_eq]
    intro e; subst e; exact h hj
  rw [this]; rfl

theorem alookup_cases (l : List (SID × Nat)) (i : SID) :
    alookup l i = 0 ∨ ∃ p ∈ l, alookup l i = p.2 := by
  unfold alookup
  cases hf : l.find? (fun p => decide (p.1 = i)) with
  | none => left; rfl
  | some p => right; exact ⟨p, List.mem_of_find?_eq_some hf, rfl⟩

theorem alookup_of_mem_nodup {l : List (SID × Nat)} (hnd : (l.map (·.1)).Nodup) {p : SID × Nat}
    (hp : p ∈ l) : alookup l p.1 = p.2 := by
  induction l with
  | nil => cases hp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    unfold alookup
    rcases List.mem_cons.mp hp with e | hp'
    · subst e; simp
    · have hne : a.1 ≠ p.1 := by
        intro e; exact hnd.1 ⟨p, hp', e.symm⟩
      have := ih hnd.2 hp'
      unfold alookup at this
      simp [hne] at this ⊢
      exact this

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with e | h
    · subst e; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem foldr_max_le {l : List Nat} {X : Nat} (h : ∀ x ∈ l, x ≤ X) : l.foldr max 0 ≤ X := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem snapOf_term (σ : PState) (n : Nat) (i : SID) :
    (snapOf σ n).term i = if i ∈ σ.srvs then σ.term i else 0 := by
  unfold Snap.term snapOf
  split
  · exact alookup_map_of_mem _ (fun j => σ.term j) i ‹_›
  · exact alookup_map_of_not_mem _ (fun j => σ.term j) i ‹_›

theorem snapOf_dur (σ : PState) (n : Nat) (i : SID) :
    (snapOf σ n).dur i = if i ∈ σ.srvs then (σ.srv i).dur.1 else 0 := by
  unfold Snap.dur snapOf
  split
  · exact alookup_map_of_mem _ (fun j => (σ.srv j).dur.1) i ‹_›
  · exact alookup_map_of_not_mem _ (fun j => (σ.srv j).dur.1) i ‹_›

theorem snapOf_llen (σ : PState) (n : Nat) (T : Nat) :
    (snapOf σ n).llen T = if T ≤ σ.maxT then (σ.llog T).length else 0 := by
  unfold Snap.llen snapOf
  simp only [List.getElem?_map]
  split
  · rw [List.getElem?_range (by omega)]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-- A leader log beyond `maxT` is empty. -/
theorem llog_gt_maxT {σ : PState} (h : PInv σ) {T : Nat} (hT : σ.maxT < T) : σ.llog T = [] := by
  have hB := h.2.2.2.2.2.2.2.2.2.2.1
  exact h.2.1.2 T (by have := hB.2.2.2.1; omega) (hB.2.2.1 T hT)

/-- The snapshot of the current state is known (`IPub`, `ICommits`, `IAcks`, `ILogs`). -/
theorem snapOK_now (σ : PState) (n : Nat) (h : PInv σ) : SnapOK σ (snapOf σ n) := by
  have h0 := h
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  have hmax : ∀ T, σ.leader T ≠ none → T ≤ σ.maxT := by
    intro T hT; apply Classical.byContradiction; intro hc
    exact hT (hB.2.2.1 T (by omega))
  refine ⟨by simp [snapOf, Function.comp_def], by simp [snapOf, Function.comp_def], fun i hi => ?_, fun i hi => ?_, fun T => ?_,
    fun T x e hx he => ?_, fun T hT => ?_, fun i hi => ?_, fun T j c L _ _ hv => ?_⟩
  · rw [snapOf_term, snapOf_dur, if_pos hi, if_pos hi]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rw [snapOf_term, snapOf_dur, if_neg hi, if_neg hi]; exact ⟨rfl, rfl⟩
  · rw [snapOf_llen]; split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  · have he' := LMok_ent (hLo.2.1 T) he
    have hl' := ent_le_length he'
    have hle : e.term ≤ σ.maxT := by
      apply Classical.byContradiction; intro hc
      rw [llog_gt_maxT h0 (by omega)] at he'
      simp [ent] at he'
    rw [snapOf_llen, if_pos hle]; exact hl'.2
  · rw [snapOf_llen] at hT ⊢
    split at hT
    · rw [if_pos ‹_›]
      by_cases h1 : T = 1
      · exact Or.inl h1
      · right
        have hne := llog_leader hL h1 (by omega)
        obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hne
        exact ⟨hne, (hL.1 T ℓ hℓ).2.2.2.1⟩
    · exact absurd rfl hT
  · rw [snapOf_dur, if_pos hi]
    rcases hP.2 i hi with h0 | ⟨T, k, hTi, hdk, hpk⟩
    · exact Or.inl h0
    · right
      obtain ⟨hld, k', p, hkk, hck⟩ := hP.1 T k hpk
      obtain ⟨hcm, _⟩ := hCo.1 T k' p hck
      obtain ⟨_, _, hk'l, _, e, he, _, Q, hQ, hQa⟩ := hcm
      have hcf : cfgAt σ (σ.llog T) p = σ.cv e.data := by simp [cfgAt, cfgAtC, he]
      refine ⟨T, k, k', p, Q, hdk, hkk, hpk, hck, ?_, by rw [hcf]; exact hQ, fun j hj => ?_⟩
      · rw [snapOf_llen, if_pos (hmax T hld)]; exact hk'l
      · obtain ⟨m, hm, ha⟩ := hQa j hj
        rw [snapOf_term, if_pos (hA j T m ha).1]
        exact ⟨(hA j T m ha).2.2.2.1, m, hm, ha⟩
  · obtain ⟨hj, _, hTv, _⟩ := hV.1 j T c L true hv
    rw [snapOf_term, if_pos hj]
    exact Nat.le_trans hTv (hV.2.1 j hj).1
  /- stage-3 proof:
  := by
  have h0 := h
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP⟩ := h
  have hmax : ∀ T, σ.leader T ≠ none → T ≤ σ.maxT := by
    intro T hT; apply Classical.byContradiction; intro hc
    exact hT (hB.2.2.1 T (by omega))
  refine ⟨by simp [snapOf, Function.comp_def], by simp [snapOf, Function.comp_def], fun i hi => ?_, fun i hi => ?_, fun T => ?_,
    fun T x e hx he => ?_, fun T hT => ?_, fun i hi => ?_⟩
  · rw [snapOf_term, snapOf_dur, if_pos hi, if_pos hi]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · rw [snapOf_term, snapOf_dur, if_neg hi, if_neg hi]; exact ⟨rfl, rfl⟩
  · rw [snapOf_llen]; split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  · have he' := LMok_ent (hLo.2.1 T) he
    have hl' := ent_le_length he'
    have hle : e.term ≤ σ.maxT := by
      apply Classical.byContradiction; intro hc
      rw [llog_gt_maxT h0 (by omega)] at he'
      simp [ent] at he'
    rw [snapOf_llen, if_pos hle]; exact hl'.2
  · rw [snapOf_llen] at hT ⊢
    split at hT
    · rw [if_pos ‹_›]
      by_cases h1 : T = 1
      · exact Or.inl h1
      · right
        have hne := llog_leader hL h1 (by omega)
        obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hne
        exact ⟨hne, (hL.1 T ℓ hℓ).2.2.2.1⟩
    · exact absurd rfl hT
  · rw [snapOf_dur, if_pos hi]
    rcases hP.2 i hi with h0 | ⟨T, k, hTi, hdk, hpk⟩
    · exact Or.inl h0
    · right
      obtain ⟨hld, k', hkk, hck⟩ := hP.1 T k hpk
      obtain ⟨hcm, _⟩ := hCo.1 T k' hck
      obtain ⟨_, _, hk'l, _, Q, hQ, hQa⟩ := hcm
      refine ⟨T, k, k', Q, hdk, hkk, hpk, hck, ?_, hQ, fun j hj => ?_⟩
      · rw [snapOf_llen, if_pos (hmax T hld)]; exact hk'l
      · obtain ⟨m, hm, ha⟩ := hQa j hj
        rw [snapOf_term, if_pos (hQ.2.1 j hj)]
        exact ⟨(hA j T m ha).2.2.2.1, m, hm, ha⟩
  -/

/-- What a state knows of a snapshot it keeps knowing after any step. -/
theorem snapOK_grows (σ σ' : PState) (s : Snap) (h : PInv σ) (hg : Grows σ σ')
    (hs : SnapOK σ s) : SnapOK σ' s := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ := hg
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hs
  refine ⟨g1 ▸ s1, g1 ▸ s2, fun i hi => ?_, fun i hi => ?_, fun T => ?_, fun T x e hx he => ?_,
    fun T hT => ?_, fun i hi => ?_, fun T j c L h1 h2 hv => ?_⟩
  · rw [g1] at hi; exact ⟨Nat.le_trans (s3 i hi).1 (g10 i), Nat.le_trans (s3 i hi).2 (g11 i)⟩
  · rw [g1] at hi; exact s4 i hi
  · exact Nat.le_trans (s5 T) (g4 T).1.length_le
  · apply s6 T x e hx
    have hx' := Nat.le_trans hx (s5 T)
    rw [agree_ent (agree_of_prefix (g4 T).1 hx') (Nat.le_refl x)]; exact he
  · rcases s7 T hT with h1 | ⟨hl, hl0⟩
    · exact Or.inl h1
    · right
      obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
      refine ⟨by rw [g3 T ℓ hℓ]; simp, ?_⟩
      rw [(g4 T).2 (Or.inl hl)]; exact hl0
  · rw [g1] at hi
    rcases s8 i hi with h0 | ⟨T', k, k', p, Q, a1, a2, a3, a4, a5, a6, a7⟩
    · exact Or.inl h0
    · right
      have hcf : cfgAt σ' (σ'.llog T') p = cfgAt σ (σ.llog T') p := by
        cases hep : ent (σ.llog T') p with
        | none =>
          exfalso
          have : cfgAt σ (σ.llog T') p = [] := by simp [cfgAt, cfgAtC, hep]
          rw [this] at a6; exact not_quorum_nil Q a6
        | some e =>
          have hp := (ent_le_length hep).2
          have := agree_ent (agree_of_prefix (g4 T').1 hp) (Nat.le_refl p)
          simp only [cfgAt, cfgAtC, g2.2, ← this, hep]
      refine ⟨T', k, k', p, Q, a1, a2, g14 _ _ a3, g8 _ _ _ a4, a5, by rw [hcf]; exact a6,
        fun j hj => ⟨(a7 j hj).1, ?_⟩⟩
      obtain ⟨m, hm, ha⟩ := (a7 j hj).2
      exact ⟨m, hm, g7 _ _ _ ha⟩
  · rcases g15 j T c L hv with hv' | hn
    · exact s9 T j c L h1 h2 hv'
    · rcases s7 T h1 with h3 | ⟨h3, _⟩
      · exact absurd h3 h2
      · exact absurd hn h3
  /- stage-3 proof:
  := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hg
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hs
  refine ⟨g1 ▸ s1, g1 ▸ s2, fun i hi => ?_, fun i hi => ?_, fun T => ?_, fun T x e hx he => ?_,
    fun T hT => ?_, fun i hi => ?_⟩
  · rw [g1] at hi; exact ⟨Nat.le_trans (s3 i hi).1 (g10 i), Nat.le_trans (s3 i hi).2 (g11 i)⟩
  · rw [g1] at hi; exact s4 i hi
  · exact Nat.le_trans (s5 T) (g4 T).1.length_le
  · apply s6 T x e hx
    have hx' := Nat.le_trans hx (s5 T)
    rw [agree_ent (agree_of_prefix (g4 T).1 hx') (Nat.le_refl x)]; exact he
  · rcases s7 T hT with h1 | ⟨hl, hl0⟩
    · exact Or.inl h1
    · right
      obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
      refine ⟨by rw [g3 T ℓ hℓ]; simp, ?_⟩
      rw [(g4 T).2 (Or.inl hl)]; exact hl0
  · rw [g1] at hi
    rcases s8 i hi with h0 | ⟨T', k, k', Q, a1, a2, a3, a4, a5, a6, a7⟩
    · exact Or.inl h0
    · right
      refine ⟨T', k, k', Q, a1, a2, g14 _ _ a3, g8 _ _ a4, a5, isQuorum_congr g1 a6,
        fun j hj => ⟨(a7 j hj).1, ?_⟩⟩
      obtain ⟨m, hm, ha⟩ := (a7 j hj).2
      exact ⟨m, hm, g7 _ _ _ ha⟩
  -/

/-- A snapshot taken now is after every snapshot the state knows of (with a larger number). -/
theorem snapLe_now (σ : PState) (s : Snap) (n : Nat) (h : PInv σ) (hs : SnapOK σ s)
    (hn : s.idx ≤ n) : snapLe s (snapOf σ n) := by
  have hB := h.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hn, fun i => ?_, fun i => ?_, fun T => ?_⟩
  · rw [snapOf_term]; split
    · exact (hs.2.2.1 i ‹_›).1
    · rw [(hs.2.2.2.1 i ‹_›).1]; exact Nat.le_refl _
  · rw [snapOf_dur]; split
    · exact (hs.2.2.1 i ‹_›).2
    · rw [(hs.2.2.2.1 i ‹_›).2]; exact Nat.le_refl _
  · rw [snapOf_llen]; split
    · exact hs.2.2.2.2.1 T
    · apply Classical.byContradiction; intro hc
      rcases hs.2.2.2.2.2.2.1 T (by omega) with h1 | ⟨hl, _⟩
      · have := hB.2.2.2.1; omega
      · exact hl (hB.2.2.1 T (by omega))

theorem snapLe_refl (s : Snap) : snapLe s s := by
  exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩

theorem snapLe_trans {s1 s2 s3 : Snap} (h1 : snapLe s1 s2) (h2 : snapLe s2 s3) : snapLe s1 s3 := by
  exact ⟨Nat.le_trans h1.1 h2.1, fun i => Nat.le_trans (h1.2.1 i) (h2.2.1 i),
    fun i => Nat.le_trans (h1.2.2.1 i) (h2.2.2.1 i), fun T => Nat.le_trans (h1.2.2.2 T) (h2.2.2.2 T)⟩

/-- Each voter's durable prefix is at most the frontier. -/
theorem Snap.dur_le_maxDur (s : Snap) (i : SID) : s.dur i ≤ s.maxDur := by
  unfold Snap.dur Snap.maxDur
  rcases alookup_cases s.durs i with h0 | ⟨p, hp, he⟩
  · rw [h0]; exact Nat.zero_le _
  · rw [he]; exact le_foldr_max (List.mem_map_of_mem (f := (·.2)) hp)

/-- The frontier only grows (for a snapshot with distinct keys). -/
theorem Snap.maxDur_mono {s1 s2 : Snap} (h : snapLe s1 s2) (hnd : (s1.durs.map (·.1)).Nodup) :
    s1.maxDur ≤ s2.maxDur := by
  unfold Snap.maxDur
  apply foldr_max_le
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have e := alookup_of_mem_nodup hnd hp
  have h1 := h.2.2.1 p.1
  have h2 := Snap.dur_le_maxDur s2 p.1
  unfold Snap.dur at h1 h2
  unfold Snap.maxDur at h2
  rw [e] at h1
  exact Nat.le_trans h1 h2

/-- The frontier of a snapshot keyed by the voters is at most any common bound of the voters'
prefixes (what hr3's `p_after` needs from the per-voter read bounds). -/
theorem Snap.maxDur_le {s : Snap} {vs : List SID} (hk : s.durs.map (·.1) = vs) (hnd : vs.Nodup)
    (X : Nat)
    (h : ∀ i ∈ vs, s.dur i ≤ X) : s.maxDur ≤ X := by
  unfold Snap.maxDur
  apply foldr_max_le
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have hpv : p.1 ∈ vs := by rw [← hk]; exact List.mem_map_of_mem (f := (·.1)) hp
  have := alookup_of_mem_nodup (by rw [hk]; exact hnd) hp
  have h' := h p.1 hpv
  unfold Snap.dur at h'
  rw [this] at h'
  exact h'

/-- The frontier of a known snapshot is at most the committed log's length (every durable prefix
is committed: `IDur`, `ICommits`). -/
theorem maxDur_le_C (σ : PState) (s : Snap) (h : PInv σ) (hs : SnapOK σ s) :
    s.maxDur ≤ σ.C.length := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  apply Snap.maxDur_le (hs.2.1) hG.2.2.1
  intro i hi
  have h1 := (hs.2.2.1 i hi).2
  rcases (hD i hi).1 with h0 | ⟨_, ⟨k', p, hk', hck⟩, _⟩
  · omega
  · have := (hCo.1 _ _ _ hck).2.2.1
    omega
  /- stage-3 proof:
  := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP⟩ := h
  apply Snap.maxDur_le (hs.2.1) hG.2.2.1
  intro i hi
  have h1 := (hs.2.2.1 i hi).2
  rcases (hD i hi).1 with h0 | ⟨_, ⟨k', hk', hck⟩, _⟩
  · omega
  · have := (hCo.1 _ _ hck).2.1
    omega
  -/

/-! ## The read bound -/

/-- **The read bound** (VerifyLeader's; stage 4: over the leader's configuration at the snapshot):
if `T` has a leader in `σ` whose log at the snapshot `sc` held an entry of its own term
(`len0 T < sc.llen T`: the no-op precedes every verify), and a quorum `Q` of the latest
configuration of `llog T [1..sc.llen T]` each of whose members had a term `≤ T` at `sc`, every
server's durable prefix at `sc` is at most `len0 T` or at most a publication of `T`.
Why (stage 3): the prefix is covered by a publication `(T', k)` (`SnapOK`). `T' = T`: done. `T' < T`:
its recorded commit is in `llog T`'s election part (`ILC`), so `k ≤ len0 T`. `T' > T`: impossible.
Stage 4 (`notes/stage4-plan.md`, A3's third use): let `T₁` be the least term above `T` with a
leader log counted at `sc` (`T'` is one), `L₁` its election log; its early voters had reached `T₁`
at `sc` (`SnapOK`'s last clause), so its election quorum is disjoint from `Q`; `lastTerm L₁ ≤ T`
by minimality; `L₁` agreeing with `llog T [1..sc.llen T]` is that log (the snapshot counted `L₁`'s
entries), so the two quorums are of one configuration; otherwise `CL0` with `q = sc.llen T` gives
a commit `L₁` lacks (against `ILC`) or meeting quorums. -/
theorem read_bound (σ : PState) (sc : Snap) (T : Nat) (Q : List SID)
    (h : PInv σ) (hs : SnapOK σ sc) (hl : σ.leader T ≠ none) (hn : σ.len0 T < sc.llen T)
    (hQ : isQuorumOf (cfgOf σ ((σ.llog T).take (sc.llen T))) Q) (hq : ∀ q ∈ Q, sc.term q ≤ T) :
    ∀ i ∈ σ.srvs, sc.dur i ≤ σ.len0 T ∨ ∃ k, sc.dur i ≤ k ∧ σ.pubs T k := by
  have h0 := h
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  have hCo' : ∀ T k p, σ.commits T k p → committed σ T k p ∧ cfgAdm σ T k p :=
    fun T k p h => ⟨(hCo.1 T k p h).1, (hCo.1 T k p h).2.1⟩
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hs
  intro i hi
  rcases s8 i hi with h0 | ⟨T', k, k', p', Q', a1, a2, a3, a4, a5, a6, a7⟩
  · left; rw [h0]; exact Nat.zero_le _
  · rcases Nat.lt_trichotomy T' T with hlt | heq | hgt
    · left
      have hcm := hCo.1 _ _ _ a4
      have := hLC T' k' p' hcm.1 hcm.2.1 T hlt hl
      unfold lacks at this
      have := (Classical.not_not.mp this).1
      omega
    · right; subst heq; exact ⟨k, a1, a3⟩
    · exfalso
      have hk1 := (hCo.1 _ _ _ a4).1.2.1
      -- `T₁`: the least term above `T` counted at `sc`
      obtain ⟨T₁, ⟨hT₁, hs₁⟩, hmin⟩ :=
        exists_least (P := fun t => T < t ∧ sc.llen t ≠ 0) ⟨T', hgt, by omega⟩
      have hT2 := leader_ge_two hL hl
      rcases s7 T₁ hs₁ with h1 | ⟨hl₁, hl0₁⟩
      · omega
      obtain ⟨ℓ₁, hℓ₁⟩ := Option.ne_none_iff_exists'.mp hl₁
      obtain ⟨_, _, hlen1, hlen0, _, hel, _, _, ⟨QE, hQE, hQEv⟩, _⟩ := hL.1 T₁ ℓ₁ hℓ₁
      -- the election quorum of `T₁` is disjoint from `Q`
      have hdisj : ∀ j, j ∈ QE → j ∈ Q → False := by
        intro j hjE hjQ
        obtain ⟨L, hv⟩ := hQEv j hjE
        have := s9 T₁ j ℓ₁ L hs₁ (by omega) hv
        have := hq j hjQ
        omega
      have hElen : ((σ.llog T₁).take (σ.len0 T₁)).length = σ.len0 T₁ := by simp; omega
      have hE : LMok σ ((σ.llog T₁).take (σ.len0 T₁)) := LMok_take (hLo.2.1 T₁) _
      -- the election log's last term is at most `T` (minimality of `T₁`)
      have hlast : ∃ e, ent (σ.llog T₁) (σ.len0 T₁) = some e ∧
          e.term = lastTerm ((σ.llog T₁).take (σ.len0 T₁)) := by
        obtain ⟨e, he⟩ := ent_isSome _ (σ.len0 T₁) hlen1 hlen0
        refine ⟨e, he, ?_⟩
        unfold lastTerm; rw [hElen, termAt_take _ _ _ (Nat.le_refl _), termAt_of_ent he]
      obtain ⟨eL, heL, heLt⟩ := hlast
      have hET : lastTerm ((σ.llog T₁).take (σ.len0 T₁)) ≤ T := by
        apply Classical.byContradiction; intro hc
        have hlt₁ : eL.term < T₁ := by
          have := hel _ hlen1 (Nat.le_refl _); rw [termAt_of_ent heL] at this; exact this
        have := s6 T₁ _ eL hl0₁ heL
        exact hmin eL.term (by omega) ⟨by omega, by omega⟩
      have hq' : sc.llen T ≤ (σ.llog T).length := s5 T
      have hmeetE : cfgMeet (cfgOf σ ((σ.llog T₁).take (σ.len0 T₁)))
          (cfgOf σ ((σ.llog T).take (sc.llen T))) → False := by
        intro hm
        obtain ⟨j, hjE, hjQ⟩ := hm QE Q hQE hQ
        exact hdisj j hjE hjQ
      by_cases hag : sc.llen T ≤ ((σ.llog T₁).take (σ.len0 T₁)).length ∧
          agree ((σ.llog T₁).take (σ.len0 T₁)) (σ.llog T) (sc.llen T)
      · -- the election log is `llog T [1..sc.llen T]`
        rw [hElen] at hag
        have hlenEq : σ.len0 T₁ = sc.llen T := by
          apply Classical.byContradiction; intro hne
          have hgt' : sc.llen T < σ.len0 T₁ := by omega
          -- `eL` (at `len0 T₁`) has term `T`, so it is counted in `llog T`
          have htq : termAt ((σ.llog T₁).take (σ.len0 T₁)) (sc.llen T) = T := by
            rw [agree_termAt hag.2 (Nat.le_refl _)]
            obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hl
            exact own_term hL hl hn hq'
          have hmono := LMok_term_mono hG hL hE (k := sc.llen T) (k' := ((σ.llog T₁).take (σ.len0 T₁)).length)
            (by omega) (by rw [hElen]; omega) (Nat.le_refl _)
          have heT : eL.term = T := by
            have : termAt ((σ.llog T₁).take (σ.len0 T₁)) ((σ.llog T₁).take (σ.len0 T₁)).length =
                lastTerm ((σ.llog T₁).take (σ.len0 T₁)) := rfl
            rw [htq, this] at hmono; omega
          have := s6 T₁ _ eL hl0₁ heL
          rw [heT] at this; omega
        have hX : (σ.llog T₁).take (σ.len0 T₁) = (σ.llog T).take (sc.llen T) := by
          have := hag.2.2.2
          rw [hlenEq] at this ⊢
          rwa [List.take_take, Nat.min_self] at this
        apply hmeetE; rw [hX]; exact cfgMeet_refl _
      · rcases CL0' σ T₁ hG hL hLo hR hCo'
            (fun T0 k0 p0 hc0 ha0 T2 h1 h2 h3 => hLC T0 k0 p0 hc0 ha0 T2 h1 h3)
            _ hE T (sc.llen T) (lastCfgIdx ((σ.llog T).take (sc.llen T))) hET (by omega) hl hq'
            (Or.inl rfl) hag with hm | ⟨T0, k0, p0, hc0, hT0, hl0, hm⟩
        · apply hmeetE
          rw [cfgOf_take σ (σ.llog T) (sc.llen T)]; exact hm
        · have hnl := hLC T0 k0 p0 (hCo' _ _ _ hc0).1 (hCo' _ _ _ hc0).2 T₁ (by omega) hl₁
          unfold lacks at hnl
          obtain ⟨h1, h2⟩ := Classical.not_not.mp hnl
          exact hl0 ⟨by omega, agree_take_left _ h2 h1⟩
  /- stage-3 proof:
  := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP⟩ := h
  intro i hi
  rcases hs.2.2.2.2.2.2.2 i hi with h0 | ⟨T', k, k', Q', a1, a2, a3, a4, a5, a6, a7⟩
  · left; rw [h0]; exact Nat.zero_le _
  · rcases Nat.lt_trichotomy T' T with hlt | heq | hgt
    · left
      have hcm := (hCo.1 _ _ a4).1
      have := hLC T' k' hcm T hlt hl
      unfold lacks at this
      have := (Classical.not_not.mp this).1
      omega
    · right; subst heq; exact ⟨k, a1, a3⟩
    · exfalso
      obtain ⟨j, hj1, hj2⟩ := quorum_inter a6 hQ
      have := (a7 j hj1).1
      have := hq j hj2
      omega
  -/

/-- **The read bound of a barrier**: if the committed log's entry `e` at `b` was appended after the
snapshot `sc` (`llog e.term` was shorter than `b` at `sc`), every server's durable prefix at `sc`
is below `b`.
Why: the prefix is covered by a recorded commit `(T', k')` that was in `llog T'` at `sc`
(`SnapOK`); the committed log agrees with `llog T'` up to `k'` (`ICommits`). If `k' ≥ b`, the
committed entry `e` at `b` was `llog T'`'s at `sc`, so (log matching at `sc`) `llog e.term` had `b`
entries at `sc`: impossible. So the prefix is `≤ k' < b`. -/
theorem read_bound_barrier (σ : PState) (sc : Snap) (b : Nat) (e : Entry)
    (h : PInv σ) (hs : SnapOK σ sc) (hb : ent σ.C b = some e) (hnew : sc.llen e.term < b) :
    ∀ i ∈ σ.srvs, sc.dur i < b := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  intro i hi
  have hb1 := ent_le_length hb
  rcases hs.2.2.2.2.2.2.2.1 i hi with h0 | ⟨T', k, k', p, Q', a1, a2, a3, a4, a5, _, _⟩
  · omega
  · apply Classical.byContradiction; intro hc
    have hbk : b ≤ k' := by omega
    have hag := (hCo.1 _ _ _ a4).2.2
    have he' : ent (σ.llog T') b = some e := by rw [← agree_ent hag hbk]; exact hb
    have := hs.2.2.2.2.2.1 T' b e (by omega) he'
    omega
  /- stage-3 proof:
  := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP⟩ := h
  intro i hi
  have hb1 := ent_le_length hb
  rcases hs.2.2.2.2.2.2.2 i hi with h0 | ⟨T', k, k', Q', a1, a2, a3, a4, a5, _, _⟩
  · omega
  · apply Classical.byContradiction; intro hc
    have hbk : b ≤ k' := by omega
    have hag := (hCo.1 _ _ a4).2
    have he' : ent (σ.llog T') b = some e := by rw [← agree_ent hag hbk]; exact hb
    have := hs.2.2.2.2.2.1 T' b e (by omega) he'
    omega
  -/

end proto
end github_com.hashicorp.raft
end Perennial
