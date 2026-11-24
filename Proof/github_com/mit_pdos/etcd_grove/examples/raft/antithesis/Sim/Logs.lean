/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: logs, sets and the binding's log functions (#33 S4)

Shared by the per-report lemmas that read a log (`send`, `ready`): raft's `plogTermAt`/`plogLast` from
`base0` against the binding's `TermAt`/`Len` of the reported log (`logOf`); the evaluation of
`PrevOk`, `HasFirst` (R 366-375), `Sendable` of a leader's request (B 117-128) and its inversion;
`setAdd`'s membership and `Granted`'s monotonicity in `msgs`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Apply
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Recv

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

/-! ## Sets -/

theorem mem_setAdd {s : SSet} {x y : Str} : y ∈ setAdd s x ↔ y ∈ s ∨ y = x := by
  unfold setAdd
  simp only
  split
  · rename_i h
    have hx : x ∈ s := List.mem_of_getElem? h
    constructor
    · exact .inl
    · rintro (h | h)
      · exact h
      · exact h ▸ hx
  · constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact .inl (List.mem_of_mem_take h)
      · rcases List.mem_cons.mp h with h | h
        · exact .inr h
        · exact .inl (List.mem_of_mem_drop h)
    · rintro (h | h)
      · rw [← List.take_append_drop (s.takeWhile (fun y => strLess y x)).length s, List.mem_append] at h
        rcases h with h | h
        · exact List.mem_append.mpr (.inl h)
        · exact List.mem_append.mpr (.inr (List.mem_cons.mpr (.inr h)))
      · exact List.mem_append.mpr (.inr (List.mem_cons.mpr (.inl h)))

theorem foldl_setAdd_mono {P P' : Str → Prop} [DecidablePred P] [DecidablePred P'] (hP : ∀ j, P j → P' j)
    (x : Str) : ∀ (l : List Str) (acc acc' : SSet), (∀ y, y ∈ acc → y ∈ acc') →
      x ∈ l.foldl (fun out j => if P j then setAdd out j else out) acc →
      x ∈ l.foldl (fun out j => if P' j then setAdd out j else out) acc'
  | [], _, _, h, hx => h x hx
  | j :: l, acc, acc', h, hx => by
    simp only [List.foldl_cons] at hx ⊢
    refine foldl_setAdd_mono hP x l _ _ (fun y hy => ?_) hx
    by_cases hj : P j
    · rw [if_pos hj] at hy; rw [if_pos (hP j hj)]
      rcases mem_setAdd.mp hy with h1 | h1
      · exact mem_setAdd.mpr (.inl (h y h1))
      · exact mem_setAdd.mpr (.inr h1)
    · rw [if_neg hj] at hy
      by_cases hj' : P' j
      · rw [if_pos hj']; exact mem_setAdd.mpr (.inl (h y hy))
      · rw [if_neg hj']; exact h y hy

/-- `Granted(i)` grows with `msgs` (the rest of what it reads unchanged). -/
theorem granted_mono {s1 s : State} (i : Nat) (hcfg : s1.cfg = s.cfg) (hct : s1.currentTerm = s.currentTerm)
    (hm : ∀ f ∈ s.msgs, f ∈ s1.msgs) (hv : s1.votes = s.votes) {x : Str} (hx : (s.granted i).has x = true) :
    (s1.granted i).has x = true := by
  unfold State.granted at hx ⊢
  rw [hcfg, hct, hv]
  simp only [SSet.has, List.contains_iff_mem] at hx ⊢
  have key : ∀ acc acc' : SSet, (∀ y, y ∈ acc → y ∈ acc') → x ∈ acc → x ∈ acc' := fun _ _ h hx => h x hx
  have hfold := foldl_setAdd_mono (P := fun j => (j != s.cfg.server[i]! &&
      s.msgs.contains { type := go!"grant", src := j, dst := s.cfg.server[i]!, term := s.currentTerm[i]! }) = true)
    (P' := fun j => (j != s.cfg.server[i]! &&
      s1.msgs.contains { type := go!"grant", src := j, dst := s.cfg.server[i]!, term := s.currentTerm[i]! }) = true)
    (fun j hj => by
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hj ⊢
      exact ⟨hj.1, hm _ hj.2⟩) x s.cfg.server [] []
  split at hx <;> split
  · rcases mem_setAdd.mp hx with h | h
    · exact mem_setAdd.mpr (.inl (hfold (fun _ h => h) h))
    · exact mem_setAdd.mpr (.inr h)
  · rename_i h1 h2; exact absurd h1 h2
  · exact mem_setAdd.mpr (.inl (hfold (fun _ h => h) hx))
  · exact hfold (fun _ h => h) hx

/-! ## Terms of a log -/

section logs
variable [GooseExts]

theorem entOf_term (e : EntryM) : (entOf e).term = uint.Z e.Term' := by
  unfold entOf; split <;> rfl

theorem logOf_getElem? (l : List EntryM) (k : Nat) : (logOf l)[k]? = (l[k]?).map entOf :=
  List.getElem?_map

theorem logOf_getElem! {l : List EntryM} {k : Nat} {e : EntryM} (h : l[k]? = some e) :
    (logOf l)[k]! = entOf e := by
  rw [getElem!_def, logOf_getElem?, h]; rfl

/-- `TermAt(logOf l, i + 1)` is the term of `l[i]`. -/
theorem termAt_logOf {l : List EntryM} {i : Nat} {e : EntryM} (h : l[i]? = some e) :
    termAt (logOf l) ((i : Int) + 1) = uint.Z e.Term' := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp h).1
  unfold termAt
  rw [if_pos (by rw [logOf_length]; omega)]
  have : ((i : Int) + 1 - 1).toNat = i := by omega
  rw [this, logOf_getElem! h, entOf_term]

theorem plogTermAt_base0 {l : List EntryM} {k t : w64} (h : plogTermAt base0 l k = some t) :
    (uint.Z k = 0 ∧ t = W64 0) ∨
      (1 ≤ uint.Z k ∧ ∃ e, l[(uint.Z k - 1).toNat]? = some e ∧ e.Term' = t) := by
  unfold plogTermAt at h
  have hb : uint.Z (base0 : go_etcd_io.raft.v3.entryID).index' = 0 := rfl
  rw [hb] at h
  have hk : 0 ≤ uint.Z k := by word
  by_cases h0 : uint.Z k = 0
  · left
    rw [if_neg (by omega), if_pos h0] at h
    exact ⟨h0, (Option.some.inj h).symm⟩
  · right
    rw [if_neg (by omega), if_neg h0] at h
    refine ⟨by omega, ?_⟩
    have : (uint.Z k - 0 - 1).toNat = (uint.Z k - 1).toNat := by omega
    rw [this] at h
    cases he : l[(uint.Z k - 1).toNat]? with
    | none => rw [he] at h; cases h
    | some e => rw [he] at h; exact ⟨e, rfl, Option.some.inj h⟩

/-- Raft's `term(k)` of a log from `base0` is the binding's `TermAt` of the reported log, `k` within it. -/
theorem termAt_of_plog {l : List EntryM} {k t : w64} (h : plogTermAt base0 l k = some t) :
    uint.Z k ≤ l.length ∧ termAt (logOf l) (uint.Z k) = uint.Z t := by
  rcases plogTermAt_base0 h with ⟨h0, ht⟩ | ⟨h1, e, he, ht⟩
  · rw [h0, ht]
    refine ⟨by omega, ?_⟩
    unfold termAt; rw [if_neg (by omega)]; rfl
  · have hi := (List.getElem?_eq_some_iff.mp he).1
    refine ⟨by omega, ?_⟩
    have := termAt_logOf he
    have e1 : (((uint.Z k - 1).toNat : Nat) : Int) + 1 = uint.Z k := by omega
    rw [e1] at this; rw [this, ht]

/-- `lastEntryID()` of a log from `base0` whose indices are its positions: its length, and the term
the binding reads (`LastTerm`, R 220). -/
theorem plogLast_idx {l : List EntryM} (hidx : LogIdx l) :
    uint.Z (plogLast base0 l).index' = l.length ∧
      uint.Z (plogLast base0 l).term' = termAt (logOf l) l.length := by
  unfold plogLast
  cases hl : l.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl; subst hl
    exact ⟨rfl, rfl⟩
  | some e =>
    have hne : l ≠ [] := by intro h; subst h; cases hl
    have hlen : 0 < l.length := List.length_pos_iff.mpr hne
    have he : l[l.length - 1]? = some e := by
      rw [List.getLast?_eq_getElem?] at hl; exact hl
    have hi := hidx _ _ he
    have ht := termAt_logOf he
    have e1 : (((l.length - 1 : Nat) : Nat) : Int) + 1 = (l.length : Int) := by omega
    rw [e1] at ht hi
    exact ⟨hi, ht.symm⟩

/-! ## `PrevOk`, `HasFirst` -/

theorem atE_ok {l : List Entry} {k : Int} (h1 : 1 ≤ k) (h2 : k ≤ l.length) : atE l k = .ok (l[(k - 1).toNat]!) := by
  unfold atE; rw [if_neg (by omega)]; rfl

theorem beq_decide {a b : Int} {P : Prop} [Decidable P] (h : a = b ↔ P) : (a == b) = decide P := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]; exact h

/-- `PrevOk(j, m)` evaluates, to its condition. -/
theorem prevOk_eq (s : State) (j : Nat) (f : AppendFact) (h0 : 0 ≤ f.prevLogIndex) :
    s.prevOk j f = .ok (decide (f.prevLogIndex = 0 ∨ (f.prevLogIndex ≤ (s.log[j]!).length ∧
      ((s.log[j]!)[(f.prevLogIndex - 1).toNat]!).term = f.prevLogTerm))) := by
  unfold State.prevOk
  by_cases hp : f.prevLogIndex = 0
  · simp [hp, epure]
  · have hb : (f.prevLogIndex == 0) = false := by simpa using hp
    simp only [hb, Bool.false_eq_true, ite_false]
    by_cases hl : f.prevLogIndex ≤ ((s.log[j]!).length : Int)
    · rw [if_pos hl, atE_ok (by omega) hl, eok_bind]
      change Except.ok _ = _
      congr 1
      exact beq_decide ⟨fun h => .inr ⟨hl, h⟩, fun h => h.elim (fun h' => absurd h' hp) And.right⟩
    · rw [if_neg hl]
      change Except.ok false = _
      congr 1
      symm; exact decide_eq_false (fun h => h.elim hp (fun h' => hl h'.1))

/-- The condition `HasFirst(j, m, k)` checks at `q + 1`. -/
def HFAt (s : State) (j : Nat) (f : AppendFact) (q : Nat) : Prop :=
  f.prevLogIndex + ((q : Int) + 1) ≤ ((s.log[j]!).length : Int) ∧
    ((s.log[j]!)[(f.prevLogIndex + ((q : Int) + 1) - 1).toNat]!).term = (f.entries[q]!).term

instance (s : State) (j : Nat) (f : AppendFact) (q : Nat) : Decidable (HFAt s j f q) := by
  unfold HFAt; infer_instance

/-- `HasFirst(j, m, k)` evaluates, to its condition (for `k` within the entries). -/
theorem hasFirst_eq (s : State) (j : Nat) (f : AppendFact) (h0 : 0 ≤ f.prevLogIndex) :
    ∀ k : Nat, k ≤ f.entries.length →
      s.hasFirst j f (k : Int) = .ok (decide (∀ q < k, HFAt s j f q)) := by
  intro k
  unfold State.hasFirst
  rw [Int.toNat_natCast]
  induction k with
  | zero => intro _; simp [epure]
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldlM_append, ih (by omega), eok_bind]
    simp only [List.foldlM_cons, List.foldlM_nil]
    by_cases hA : ∀ q < k, HFAt s j f q
    · simp only [decide_eq_true hA, Bool.not_true, Bool.false_eq_true, ite_false]
      have hq1 : (1 : Int) ≤ (k : Int) + 1 := by omega
      have hq2 : (k : Int) + 1 ≤ (f.entries.length : Int) := by omega
      have hent : atE f.entries ((k : Int) + 1) = .ok (f.entries[k]!) := by
        rw [atE_ok hq1 hq2]; congr 2; omega
      by_cases hl : f.prevLogIndex + ((k : Int) + 1) ≤ ((s.log[j]!).length : Int)
      · rw [atE_ok (by omega) hl]
        simp only [decide_eq_true hl, andM_true, eok_bind, hent]
        change Except.ok _ = _
        congr 1
        refine beq_decide ⟨fun h q hq => ?_, fun h => (h k (by omega)).2⟩
        by_cases hqk : q < k
        · exact hA q hqk
        · have : q = k := by omega
          subst this; exact ⟨hl, h⟩
      · simp only [decide_eq_false hl]
        change Except.ok false = _
        congr 1
        exact (decide_eq_false (fun (h : ∀ q < k + 1, HFAt s j f q) => hl (h k (by omega)).1)).symm
    · simp only [decide_eq_false hA, Bool.not_false, ite_true]
      change Except.ok false = _
      congr 1
      symm; exact decide_eq_false (fun h => hA (fun q hq => h q (by omega)))

/-! ## Comparing entries -/

theorem entry_equal_true {e f : Entry} (h : e.equal f = .ok true) : e.term = f.term := by
  unfold Entry.equal at h
  by_cases hc : e.term ≠ f.term ∨ e.type ≠ f.type
  · rw [if_pos hc] at h; cases h
  · exact Classical.byContradiction fun h' => hc (.inl h')

theorem entriesEqualAux_true : ∀ {a b : List Entry}, a.length = b.length → entriesEqualAux a b = .ok true →
    ∀ i < a.length, (a[i]!).term = (b[i]!).term
  | [], _, _, _, i, hi => absurd hi (by simp)
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | x :: xs, y :: ys, hl, h, i, hi => by
    unfold entriesEqualAux at h
    cases he : x.equal y with
    | error e => rw [he] at h; cases h
    | ok b =>
      rw [he, eok_bind] at h
      cases b
      · simp only [Bool.not_false, ite_true] at h; cases h
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
        cases i with
        | zero => simpa using entry_equal_true he
        | succ i =>
          have := entriesEqualAux_true (by simpa using hl) h i (by simpa using hi)
          simpa using this

theorem entriesEqual_true {a b : List Entry} (h : entriesEqual a b = .ok true) :
    a.length = b.length ∧ ∀ i < a.length, (a[i]!).term = (b[i]!).term := by
  unfold entriesEqual at h
  by_cases hl : a.length ≠ b.length
  · rw [if_pos hl] at h; cases h
  · rw [if_neg hl] at h
    have hl' : a.length = b.length := Classical.byContradiction hl
    exact ⟨hl', entriesEqualAux_true hl' h⟩

/-! ## `Sendable` -/

theorem TermFn.has_of_get {α : Type} {f : TermFn α} {t : Int} {x : α} (h : f.get t = .ok x) :
    f.has t = true := by
  unfold TermFn.get at h; unfold TermFn.has
  split at h
  · rename_i p hp
    have := List.find?_some hp
    exact List.any_eq_true.mpr ⟨p, List.mem_of_find?_eq_some hp, by simpa using this⟩
  · cases h

theorem subSeq_one (s : List Entry) (c : Nat) (h : c ≤ s.length) : subSeq s 1 (c : Int) = .ok (s.take c) := by
  have := subSeq_nat s 0 c (by omega)
  simpa using this

theorem recordedIn_true {ch : List Entry} {tl : TermFn Int} {l : List Entry} {c : Nat} {t : Int}
    (h1 : c ≤ l.length) (h2 : c ≤ ch.length) (h3 : ∃ p ∈ tl, p.1 ≤ t ∧ (c : Int) ≤ p.2)
    (h4 : ch.take c = l.take c) : recordedIn ch tl l c t = .ok true := by
  unfold recordedIn
  have hany : tl.any (fun p => decide (p.1 ≤ t) && decide (p.2 ≥ (c : Int))) = true := by
    obtain ⟨p, hp, ha, hb⟩ := h3
    exact List.any_eq_true.mpr ⟨p, hp, by simp [ha, hb]⟩
  have e1 : decide ((c : Int) ≤ (l.length : Int)) = true := decide_eq_true (by omega)
  have e2 : decide ((c : Int) ≤ (ch.length : Int)) = true := decide_eq_true (by omega)
  simp only [e1, e2, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false, hany,
    subSeq_one _ _ h1, subSeq_one _ _ h2, eok_bind, h4, entriesEqual_self]

/-- **A leader's request is `Sendable`** (B 117-128): the leader in `leaders` at its term, its log
`ledLog`'s there, the previous entry's term `TermAt` of it, the entries its slice after it, the commit
`0` or recorded (`RecordedIn`, B 109-112: within the log and `chain`, `chain` agreeing with the log
there, and a `termLen` of a term up to the leader's at least it). -/
theorem sendable_leader {S : State} {src dst : Str} {lg : List EntryM} {T : Int} {p : Nat} {pt : Int}
    {es : List EntryM} {c : Nat}
    (hld : S.leaders.contains { server := src, term := T } = true)
    (hll : S.ledLog.get T = .ok (logOf lg))
    (hpt : termAt (logOf lg) p = pt) (hp : p ≤ lg.length)
    (hes : (lg.drop p).take es.length = es)
    (hc : c = 0 ∨ (c ≤ lg.length ∧ c ≤ S.chain.length ∧ (∃ x ∈ S.termLen, x.1 ≤ T ∧ (c : Int) ≤ x.2) ∧
      S.chain.take c = (logOf lg).take c)) :
    S.sendable ⟨src, dst, T, (p : Int), pt, logOf es, (c : Int)⟩ = .ok true := by
  have hk : p + es.length ≤ lg.length := by
    have := congrArg List.length hes
    simp only [List.length_take, List.length_drop] at this
    omega
  have hsub : subSeq (logOf lg) ((p : Int) + 1) ((p : Int) + ((logOf es).length : Int)) = .ok (logOf es) := by
    rw [logOf_length, subSeq_nat _ p es.length (by rw [logOf_length]; exact hk)]
    unfold logOf
    rw [← List.map_drop, ← List.map_take, hes]
  have hk' : decide ((p : Int) + ((logOf es).length : Int) ≤ ((logOf lg).length : Int)) = true :=
    decide_eq_true (by rw [logOf_length, logOf_length]; omega)
  unfold State.sendable sendableIn
  simp only [hld, TermFn.has_of_get hll, hll, Bool.not_true, Bool.false_eq_true, ite_false, eok_bind,
    hk', hpt, bne_self_eq_false, hsub, entriesEqual_self]
  rcases hc with h0 | ⟨h1, h2, h3, h4⟩
  · subst h0; rfl
  · by_cases h0 : c = 0
    · subst h0; rfl
    · have hb : ((c : Int) == 0) = false := by simpa using h0
      simp only [hb]
      change AntCheck.orM (.ok false) _ = _
      rw [orM_false]
      exact recordedIn_true (by rw [logOf_length]; exact h1) h2 h3 h4

/-- What a `Sendable` request says of its leader log (B 120-124). -/
theorem sendable_inv {S : State} {f : AppendFact} (h : S.sendable f = .ok true) :
    ∃ l, S.ledLog.get f.term = .ok l ∧ f.prevLogIndex + f.entries.length ≤ l.length ∧
      f.prevLogTerm = termAt l f.prevLogIndex ∧
      ∃ sub, subSeq l (f.prevLogIndex + 1) (f.prevLogIndex + f.entries.length) = .ok sub ∧
        entriesEqual f.entries sub = .ok true := by
  unfold State.sendable sendableIn at h
  cases h1 : S.leaders.contains { server := f.src, term := f.term } <;>
    simp only [h1, Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at h
  · cases h
  cases h2 : S.ledLog.has f.term <;>
    simp only [h2, Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at h
  · cases h
  cases hg : S.ledLog.get f.term with
  | error e => rw [hg] at h; cases h
  | ok l =>
    rw [hg, eok_bind] at h
    by_cases h3 : ¬ (f.prevLogIndex + (f.entries.length : Int) ≤ (l.length : Int))
    · simp only [h3, decide_false, Bool.not_false, ite_true] at h; cases h
    have h3 := Classical.not_not.mp h3
    simp only [h3, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at h
    by_cases h4 : ¬ f.prevLogTerm = termAt l f.prevLogIndex
    · have : (f.prevLogTerm != termAt l f.prevLogIndex) = true := by simpa using h4
      simp only [this, ite_true] at h; cases h
    have h4 := Classical.not_not.mp h4
    simp only [h4, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
    cases hs : subSeq l (f.prevLogIndex + 1) (f.prevLogIndex + (f.entries.length : Int)) with
    | error e => rw [hs] at h; cases h
    | ok sub =>
      rw [hs, eok_bind] at h
      cases he : entriesEqual f.entries sub with
      | error e => rw [he] at h; cases h
      | ok b =>
        rw [he, eok_bind] at h
        cases b
        · simp only [Bool.not_false, ite_true] at h; cases h
        · exact ⟨l, rfl, h3, h4, sub, hs, he⟩

end logs

end AntSim
end EtcdGrove
end Perennial
