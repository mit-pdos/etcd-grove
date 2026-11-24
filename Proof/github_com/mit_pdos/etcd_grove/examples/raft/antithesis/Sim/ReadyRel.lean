/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the relation after a `ready` (#33 S4, the invariant phase)

What `Ready` (B 439-447) leaves at node `n` is `OnDisk`'s successor (`odS`: the node's term, vote,
log, commit, confirmation; the roles, facts, votes, leaders, leader logs, `chain`, `termLen` given)
with `InMemory`'s configuration fields (`rdS`), and `Step`'s `i` (`readyS`). `ready_rel`: under side
conditions on the new values (`ReadyOk`, which `Ready.lean` proves per kind of `Ready`), the
relation holds of it with the node's view replaced, and `GlobalOk` with it. The other nodes'
facts are kept since `msgs`, `votes`, `leaders` only grow, `ledLog` only grows (at most the node's
term changes, extended or added), `chain` is extended and `termLen` dominated.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendRel
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyOD

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section rel
variable [GooseExts]

/-! ## Helpers: lists, leader logs, `Sendable` -/

theorem rr_set_get {α : Type} [Inhabited α] {l : List α} {n : Fin 3} (x : α) (hl : l.length = 3)
    (k : Fin 3) : (l.set n.val x)[k.val]! = if k = n then x else l[k.val]! := by
  by_cases h : k = n
  · subst h; rw [if_pos rfl, get!_set_self _ (by omega)]
  · rw [if_neg h, get!_set_ne _ _ (fun e => h (Fin.ext e))]

theorem rr_take_prefix {α : Type} {a b : List α} {k : Nat} (h : a <+: b) (hk : k ≤ a.length) :
    b.take k = a.take k := by
  obtain ⟨e, rfl⟩ := h
  exact List.take_append_of_le_length hk

theorem rr_subSeq_append (s e : List Entry) (m k : Int) (h : k ≤ s.length) :
    subSeq (s ++ e) m k = subSeq s m k := by
  unfold subSeq
  by_cases h1 : m > k
  · simp only [h1, ite_true]
  · by_cases h2 : m < 1
    · simp only [h1, h2, true_or, ite_true, ite_false]
    · have h3 : ¬ (k > ((s ++ e).length : Int)) := by simp only [List.length_append]; omega
      have h4 : ¬ (k > (s.length : Int)) := by omega
      simp only [h1, h2, h3, h4, or_self, ite_false]
      congr 1
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem rr_termAt_append (s e : List Entry) (k : Int) (h : k ≤ s.length) :
    termAt (s ++ e) k = termAt s k := by
  unfold termAt
  by_cases h1 : k > 0
  · have h2 : k ≤ ((s ++ e).length : Int) := by simp only [List.length_append]; omega
    rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, h⟩,
      getElem!_pos (s ++ e) _ (by simp only [List.length_append]; omega), getElem!_pos s _ (by omega),
      List.getElem_append_left]
  · rw [if_neg (fun h' => h1 h'.1), if_neg (fun h' => h1 h'.1)]

theorem rr_recordedIn_mono {ch ch' l l' : List Entry} {tl tl' : TermFn Int} {c t : Int}
    (hch : ch <+: ch') (hl : l <+: l') (htl : ∀ q ∈ tl, ∃ q' ∈ tl', q'.1 = q.1 ∧ q.2 ≤ q'.2)
    (h : recordedIn ch tl l c t = .ok true) : recordedIn ch' tl' l' c t = .ok true := by
  obtain ⟨e1, rfl⟩ := hch
  obtain ⟨e2, rfl⟩ := hl
  unfold recordedIn at h ⊢
  cases hc : (decide (c ≤ (l.length : Int)) && decide (c ≤ (ch.length : Int)))
  · simp only [hc, Bool.not_false, ite_true] at h; cases h
  have hc2 : c ≤ l.length ∧ c ≤ ch.length := by simpa using hc
  have hc' : (decide (c ≤ ((l ++ e2).length : Int)) && decide (c ≤ ((ch ++ e1).length : Int))) = true := by
    simp only [List.length_append, Bool.and_eq_true, decide_eq_true_eq]; omega
  simp only [hc, hc', Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
  cases ha : tl.any (fun p => decide (p.1 ≤ t) && decide (p.2 ≥ c))
  · simp only [ha, Bool.not_false, ite_true] at h; cases h
  have ha' : tl'.any (fun p => decide (p.1 ≤ t) && decide (p.2 ≥ c)) = true := by
    obtain ⟨q, hq, hq2⟩ := List.any_eq_true.mp ha
    obtain ⟨q', hq', h1, h2⟩ := htl q hq
    refine List.any_eq_true.mpr ⟨q', hq', ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq2 ⊢; omega
  simp only [ha, ha', Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
  rw [rr_subSeq_append _ _ _ _ hc2.2, rr_subSeq_append _ _ _ _ hc2.1]
  exact h

/-- `Sendable` is kept when the leaders grow, the leader logs are extended, `chain` is extended and
`termLen` dominated. -/
theorem rr_sendableIn_mono {ld ld' : List LeaderRec} {ll ll' : TermFn (List Entry)} {ch ch' : List Entry}
    {tl tl' : TermFn Int} {f : AppendFact}
    (hld : ∀ x ∈ ld, x ∈ ld') (hll : ∀ t l, ll.get t = .ok l → ∃ e, ll'.get t = .ok (l ++ e))
    (hch : ch <+: ch') (htl : ∀ q ∈ tl, ∃ q' ∈ tl', q'.1 = q.1 ∧ q.2 ≤ q'.2)
    (h : sendableIn ld ll ch tl f = .ok true) : sendableIn ld' ll' ch' tl' f = .ok true := by
  unfold sendableIn at h ⊢
  cases h1 : ld.contains { server := f.src, term := f.term } <;>
    simp only [h1, Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at h
  · cases h
  have h1' : ld'.contains { server := f.src, term := f.term } = true :=
    List.contains_iff_mem.mpr (hld _ (List.contains_iff_mem.mp h1))
  cases h2 : ll.has f.term <;>
    simp only [h2, Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true, ite_false] at h
  · cases h
  cases hg : ll.get f.term with
  | error e => rw [hg] at h; cases h
  | ok l =>
    rw [hg, eok_bind] at h
    obtain ⟨e, hg'⟩ := hll _ _ hg
    simp only [h1', TermFn.has_of_get hg', hg', Bool.not_true, Bool.false_eq_true, ite_false, eok_bind]
    by_cases h3 : ¬ (f.prevLogIndex + (f.entries.length : Int) ≤ (l.length : Int))
    · simp only [h3, decide_false, Bool.not_false, ite_true] at h; cases h
    have h3 := Classical.not_not.mp h3
    have h3' : f.prevLogIndex + (f.entries.length : Int) ≤ ((l ++ e).length : Int) := by
      simp only [List.length_append]; omega
    simp only [h3, h3', decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
    have hp : f.prevLogIndex ≤ l.length := by omega
    rw [rr_termAt_append _ _ _ hp, rr_subSeq_append _ _ _ _ h3]
    by_cases h4 : (f.prevLogTerm != termAt l f.prevLogIndex) = true
    · simp only [h4, ite_true] at h; cases h
    simp only [Bool.not_eq_true] at h4
    simp only [h4, Bool.false_eq_true, ite_false] at h ⊢
    cases hs : subSeq l (f.prevLogIndex + 1) (f.prevLogIndex + (f.entries.length : Int)) with
    | error e => rw [hs] at h; cases h
    | ok sub =>
      simp only [hs, eok_bind] at h ⊢
      cases he : entriesEqual f.entries sub with
      | error e => rw [he] at h; cases h
      | ok b =>
        simp only [he, eok_bind] at h ⊢
        cases b
        · simp only [Bool.not_false, ite_true] at h; cases h
        simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
        cases hz : (f.commit == 0)
        · simp only [hz] at h ⊢
          change AntCheck.orM (.ok false) _ = _ at h
          change AntCheck.orM (.ok false) _ = _
          rw [orM_false] at h ⊢
          exact rr_recordedIn_mono hch ⟨e, rfl⟩ htl h
        · rfl

theorem rr_get_cons {α : Type} (q : Int × α) (qs : TermFn α) (t : Int) :
    TermFn.get (q :: qs) t = if q.1 = t then .ok q.2 else TermFn.get qs t := by
  unfold TermFn.get
  by_cases h : q.1 = t
  · simp only [List.find?_cons, h, beq_self_eq_true, if_true]; rfl
  · have : (q.1 == t) = false := by simpa using h
    simp only [List.find?_cons, this, if_neg h]

theorem rr_get_with_self {α : Type} (f : TermFn α) (t : Int) (v : α) : (f.with t v).get t = .ok v := by
  induction f with
  | nil => simp only [TermFn.with, rr_get_cons, if_true]
  | cons q qs ih =>
    unfold TermFn.with
    split
    · rw [rr_get_cons, if_pos rfl]
    · rw [rr_get_cons, if_neg (by omega)]; exact ih

theorem rr_get_with_ne {α : Type} (f : TermFn α) {t t' : Int} (v : α) (h : t' ≠ t) :
    (f.with t v).get t' = f.get t' := by
  induction f with
  | nil =>
    simp only [TermFn.with, rr_get_cons, if_neg (Ne.symm h)]
  | cons q qs ih =>
    unfold TermFn.with
    split
    · rw [rr_get_cons, if_neg (Ne.symm h)]
      split
      · rename_i he; rw [rr_get_cons, if_neg (by rw [he]; exact Ne.symm h)]
      · rfl
    · rw [rr_get_cons, rr_get_cons, ih]

theorem rr_mem_with {α : Type} {f : TermFn α} {t : Int} {v : α} {x : Int × α} (h : x ∈ f.with t v) :
    x ∈ f ∨ x = (t, v) := by
  induction f with
  | nil => simp only [TermFn.with, List.mem_singleton] at h; exact .inr h
  | cons q qs ih =>
    unfold TermFn.with at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact .inr h
      · split at h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inl h
    · rcases List.mem_cons.mp h with h | h
      · exact .inl (h ▸ List.mem_cons_self ..)
      · exact (ih h).imp (List.mem_cons_of_mem _) id

theorem rr_get_of_has {α : Type} {f : TermFn α} {t : Int} (h : f.has t = true) : ∃ x, f.get t = .ok x := by
  unfold TermFn.has at h; unfold TermFn.get
  cases hf : f.find? (fun p => p.1 == t) with
  | some p => exact ⟨p.2, rfl⟩
  | none =>
    obtain ⟨p, hp, hpt⟩ := List.any_eq_true.mp h
    exact absurd hf (by rw [List.find?_eq_none]; intro hn; exact (hn p hp) hpt |>.elim)

theorem rr_has_with {α : Type} {f : TermFn α} {t t' : Int} (v : α) (h : f.has t' = true) :
    (f.with t v).has t' = true := by
  by_cases ht : t' = t
  · subst ht; exact TermFn.has_of_get (rr_get_with_self f t' v)
  · obtain ⟨x, hx⟩ := rr_get_of_has h
    exact TermFn.has_of_get (x := x) (by rw [rr_get_with_ne f v ht]; exact hx)

theorem rr_granted_mono {s1 s : State} (i : Nat) (hcfg : s1.cfg = s.cfg)
    (hct : s1.currentTerm[i]! = s.currentTerm[i]!)
    (hm : ∀ f ∈ s.msgs, f ∈ s1.msgs) (hv : ∀ y ∈ s.votes, y ∈ s1.votes) {x : Str}
    (hx : (s.granted i).has x = true) : (s1.granted i).has x = true := by
  unfold State.granted at hx ⊢
  rw [hcfg, hct]
  simp only [SSet.has, List.contains_iff_mem] at hx ⊢
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
  · rename_i h1 h2
    exact absurd (hv _ h1) h2
  · exact mem_setAdd.mpr (.inl (hfold (fun _ h => h) hx))
  · exact hfold (fun _ h => h) hx

/-- The state after a `ready` report at node `n` (`Ready`'s result, with `Step`'s `i`). -/
def readyS (S : State) (n : Nat) (t1 : Int) (vo : Option Str) (L1 : List Entry) (c : Int)
    (ro : List Str) (cf : Confirmed) (M : List Fact) (Vs : List VoteRec) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (p : Pre) (ch : List Entry) (tl : TermFn Int) (vi : SSet)
    (r : MemResult) : State :=
  { rdS (odS S n t1 vo L1 c ro cf M Vs ld ll p ch tl vi) r with i := S.i + 1 }

/-- **The side conditions of a `ready` at node `n`** leaving the new view `w` (its protocol state
`w.ps`) and the binding's new values: the node's durable fields are `w`'s; facts, votes and
leaders only grow, by the node's own (an ack of the node at its new term, covered by its new
confirmation or commit; its vote at its new term; its leadership at its term), each certified by
`G`; the leader logs unchanged, or the node's term's set to its new log (a leader's win or store,
extending what was there); `chain` extended, `termLen` dominated, the node's commit within and
agreeing with `chain`, recorded; the confirmation kept or moved to the new term (never lower at
the same term), a prefix of its term's leader log; the node's C2 and drain facts at the new
state. -/
structure ReadyOk (S : State) (V : Fin 3 → NodeView) (net : List Msg) (G : RaftFacts) (n : Fin 3)
    (w : NodeView) (t1 : Int) (vo : Option Str) (L1 : List Entry) (c : Int)
    (ro : List Str) (cf : Confirmed) (M : List Fact) (Vs : List VoteRec) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (p : Pre) (ch : List Entry) (tl : TermFn Int) (vi : SSet)
    (r : MemResult) : Prop where
  -- the node's durable fields
  hterm : t1 = uint.Z w.ps.term
  tge : S.currentTerm[n.val]! ≤ t1
  hvote : match vo with
    | some x => x = nameOf w.ps.vote ∧ 0 < t1
    | none => (t1 = S.currentTerm[n.val]! ∧ S.vote n.val = nameOf w.ps.vote) ∨
        (S.currentTerm[n.val]! < t1 ∧ w.ps.vote = W64 0)
  hlog : L1 = logOf w.ps.log
  hcommit : c = uint.Z w.ps.commit
  cge : S.commitIndex[n.val]! ≤ c
  hrole : ro[n.val]! = roleOf w.ps.role
  rlen : ro.length = 3
  rother : ∀ k : Fin 3, k ≠ n → ro[k.val]! = S.role[k.val]!
  rstay : S.role[n.val]! = leader → t1 = S.currentTerm[n.val]! → ro[n.val]! = leader
  hdel : w.delivered = (V n).delivered
  wf : w.ps.outbox = [] ∧ w.ps.base = base0 ∧ LogIdx w.ps.log ∧ w.delivered ++ w.ce <+: w.ps.log ∧
    (w.delivered ++ w.ce).length ≤ uint.nat w.ps.commit
  hmem : r.config = S.config ∧ r.confAt = S.confAt
  hviol : vi = []
  made : p.made = false
  -- facts, votes, leaders
  msub : ∀ f ∈ S.msgs, f ∈ M
  mnew : ∀ f ∈ M, f ∉ S.msgs → f.type = go!"vote" ∨
    (f.type = go!"ack" ∧ f.src = nameOf (nodeId n) ∧ (∃ j : Fin 3, f.dst = nameOf (nodeId j)) ∧
      f.term = t1 ∧ ((cf.term = f.term ∧ f.index ≤ cf.index) ∨ f.index ≤ c))
  vsub : ∀ y ∈ S.votes, y ∈ Vs
  vnew : ∀ y ∈ Vs, y ∉ S.votes →
    y = { voter := nameOf (nodeId n), term := t1, cand := nameOf w.ps.vote } ∧
      (nodeId n, w.ps.term, w.ps.vote) ∈ G.votes
  vin : vo ≠ none → { voter := nameOf (nodeId n), term := t1, cand := nameOf w.ps.vote } ∈ Vs
  lsub : ∀ l ∈ S.leaders, l ∈ ld
  lnew : ∀ l ∈ ld, l ∉ S.leaders →
    l = { server := nameOf (nodeId n), term := t1 } ∧ ro[n.val]! = leader ∧
      (nodeId n, w.ps.term) ∈ G.leaders
  glead : ro[n.val]! = leader → (nodeId n, w.ps.term) ∈ G.leaders
  -- leader logs
  hll : ll = S.ledLog ∨
    (ll = S.ledLog.with t1 L1 ∧ ro[n.val]! = leader ∧ t1 = S.currentTerm[n.val]! ∧
      (∀ l, S.ledLog.get t1 = .ok l → l <+: L1) ∧ { server := nameOf (nodeId n), term := t1 } ∈ ld ∧
      ∃ t l0, uint.Z t = t1 ∧ (t, l0) ∈ G.camps ∧ l0 <+: w.ps.log)
  -- chain and termLen
  hchain : S.chain <+: ch
  chainC : c ≤ ch.length ∧ ch.take c.toNat = L1.take c.toNat
  tlLen : ∀ q ∈ tl, q.2 ≤ ch.length
  tlC : c = 0 ∨ ∃ q ∈ tl, q.1 ≤ t1 ∧ c ≤ q.2
  tlDom : ∀ q ∈ S.termLen, ∃ q' ∈ tl, q'.1 = q.1 ∧ q.2 ≤ q'.2
  chainG : ∃ c' ≤ G.committed.length, ch = logOf (G.committed.take c')
  tlG : ∀ q ∈ tl, 0 ≤ q.2 ∧ ∃ x, uint.Z x = q.1 ∧ (x, q.2.toNat) ∈ G.commits
  logG : w.ps.log ∈ G.logs
  -- the confirmation
  cmono : cf = S.confirmed[n.val]! ∨
    (cf.term = t1 ∧ ll.has t1 = true ∧
      ((S.confirmed[n.val]!).term = t1 → (S.confirmed[n.val]!).index ≤ cf.index))
  hconf : ∀ l, ll.get cf.term = .ok l →
    cf.index ≤ L1.length ∧ cf.index ≤ l.length ∧ L1.take cf.index.toNat = l.take cf.index.toNat
  -- the node's C2 and drain facts
  lpart : LeaderPart (readyS S n.val t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) n w
  cpart : CandPart (readyS S n.val t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) n w
  hpend : ∀ q ∈ w.pend, PendOk (nodeId n) w q
  hqs : ∀ q ∈ w.qs, QsOk (readyS S n.val t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) n w q
  drain : w.told = (V n).told ∧ w.cause = (V n).cause
  hlead : LeadOk n w
  hvself : VoteSelf n w
  -- C3's recorded commits, C4's leader commits
  rnf : ro[n.val]! ≠ follower → t1 = S.currentTerm[n.val]! → S.role[n.val]! ≠ follower
  tlMono : ∀ T, tlOld S.termLen T ≤ tlOld tl T
  tlNew : ∀ T, tlOld S.termLen T < tlOld tl T → T = t1 ∧ (∃ l ∈ ld, l.term = t1) ∧
    ∀ k : Fin 3, k ≠ n → S.role[k.val]! = leader → S.currentTerm[k.val]! = t1 →
      tlOld tl t1 ≤ S.commitIndex[k.val]!
  tlSelf : ro[n.val]! = leader → (termAt L1 c = t1 → c ≤ tlOld tl t1) ∧ tlOld tl t1 ≤ c
  -- C3's leader configurations
  lconf : ∀ T, ll.has T = true → r.ledConf.get T = .ok cfg3.initConf
  -- C3's `termLen` sorted
  tlSort : tl.Pairwise (fun a b => a.1 < b.1)


/-! ## The new state, piece by piece -/

section main
variable {S : State} {V : Fin 3 → NodeView} {net : List Msg} {G : RaftFacts} {n : Fin 3}
    {w : NodeView} {t1 : Int} {vo : Option Str} {L1 : List Entry} {c : Int} {ro : List Str}
    {cf : Confirmed} {M : List Fact} {Vs : List VoteRec} {ld : List LeaderRec}
    {ll : TermFn (List Entry)} {p : Pre} {ch : List Entry} {tl : TermFn Int} {vi : SSet}
    {r : MemResult}

set_option hygiene false in
local notation "S₂" => readyS S n.val t1 vo L1 c ro cf M Vs ld ll p ch tl vi r

theorem rr_nameOf_zero : nameOf (W64 0) = [] := by unfold nameOf; simp

set_option hygiene false in
local notation "S₂[" v "]" => readyS S n.val t1 v L1 c ro cf M Vs ld ll p ch tl vi r

/-- What the vote is at the new state. -/
def VoteAt (S S2 : State) (n : Fin 3) (w : NodeView) (t1 : Int) (Vs : List VoteRec) : Prop :=
  S2.vote n.val = nameOf w.ps.vote ∧
    (S2.vote n.val ≠ [] → { voter := nameOf (nodeId n), term := t1, cand := S2.vote n.val } ∈ Vs) ∧
    (∀ k : Fin 3, k ≠ n → S2.vote k.val = S.vote k.val) ∧
    S2.voteTerm[n.val]! ≤ t1 ∧ (∀ k : Fin 3, k ≠ n → S2.voteTerm[k.val]! = S.voteTerm[k.val]!)

theorem rr_vote_some {x : Str} (hs : AntSim S V net)
    (hok : ReadyOk S V net G n w t1 (some x) L1 c ro cf M Vs ld ll p ch tl vi r) :
    VoteAt S (S₂[some x]) n w t1 Vs := by
  obtain ⟨⟨sh0, sh1, sh2, sh3, -⟩, -, -, -⟩ := hs
  have hct : (S₂[some x]).currentTerm[n.val]! = t1 := by
    show (S.currentTerm.set n.val t1)[n.val]! = t1; rw [get!_set_self _ (by omega)]
  have hcto : ∀ k : Fin 3, k ≠ n → (S₂[some x]).currentTerm[k.val]! = S.currentTerm[k.val]! := fun k hk => by
    show (S.currentTerm.set n.val t1)[k.val]! = _; rw [get!_set_ne _ _ (fun e => hk (Fin.ext e))]
  have hboot : S.bootTerm = 0 := by unfold State.bootTerm; rw [sh0]; rfl
  have hvo : ∀ k : Fin 3, (S₂[some x]).vote k.val =
      S.voteOf ((S₂[some x]).voteTerm[k.val]!) ((S₂[some x]).voteFor[k.val]!)
        ((S₂[some x]).currentTerm[k.val]!) := fun k => rfl
  obtain ⟨hx, ht0⟩ := hok.hvote
  have hvt : (S₂[some x]).voteTerm[n.val]! = t1 := by
    show (S.voteTerm.set n.val t1)[n.val]! = t1; rw [get!_set_self _ (by omega)]
  have hvf : (S₂[some x]).voteFor[n.val]! = x := by
    show (S.voteFor.set n.val x)[n.val]! = x; rw [get!_set_self _ (by omega)]
  have hvn : (S₂[some x]).vote n.val = x := by
    rw [hvo, hvt, hvf, hct]; unfold State.voteOf; rw [hboot]; simp [ht0]
  refine ⟨hvn.trans hx, fun _ => by rw [hvn, hx]; exact hok.vin (by simp), fun k hk => ?_, by rw [hvt]; exact Int.le_refl _,
    fun k hk => ?_⟩
  · rw [hvo, hcto k hk]
    show S.voteOf ((S.voteTerm.set n.val t1)[k.val]!) ((S.voteFor.set n.val x)[k.val]!) _ = _
    rw [get!_set_ne _ _ (fun e => hk (Fin.ext e)), get!_set_ne _ _ (fun e => hk (Fin.ext e))]; rfl
  · show (S.voteTerm.set n.val t1)[k.val]! = _; rw [get!_set_ne _ _ (fun e => hk (Fin.ext e))]

theorem rr_vote_none (hs : AntSim S V net)
    (hok : ReadyOk S V net G n w t1 none L1 c ro cf M Vs ld ll p ch tl vi r) :
    VoteAt S (S₂[none]) n w t1 Vs := by
  obtain ⟨⟨sh0, sh1, sh2, sh3, -⟩, ⟨-, -, -, -, -, -, -, -, -, -, -, -, hb13, -, hb15, -⟩, -, -⟩ := hs
  have hct : (S₂[none]).currentTerm[n.val]! = t1 := by
    show (S.currentTerm.set n.val t1)[n.val]! = t1; rw [get!_set_self _ (by omega)]
  have hcto : ∀ k : Fin 3, k ≠ n → (S₂[none]).currentTerm[k.val]! = S.currentTerm[k.val]! := fun k hk => by
    show (S.currentTerm.set n.val t1)[k.val]! = _; rw [get!_set_ne _ _ (fun e => hk (Fin.ext e))]
  have hvo : ∀ k : Fin 3, (S₂[none]).vote k.val =
      S.voteOf (S.voteTerm[k.val]!) (S.voteFor[k.val]!) ((S₂[none]).currentTerm[k.val]!) := fun k => rfl
  have htge := hok.tge
  have hvo2 : ∀ k : Fin 3, k ≠ n → (S₂[none]).vote k.val = S.vote k.val := fun k hk => by
    rw [hvo, hcto k hk]; rfl
  have hvt := hb15 n
  rcases hok.hvote with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hvn : (S₂[none]).vote n.val = S.vote n.val := by rw [hvo, hct, h1]; rfl
    refine ⟨hvn.trans h2, fun hne => ?_, hvo2, ?_, fun k _ => rfl⟩
    · rw [hvn] at hne ⊢; rw [h1]; exact hok.vsub _ (hb13 n hne)
    · show S.voteTerm[n.val]! ≤ t1; omega
  · have hvn : (S₂[none]).vote n.val = [] := by
      rw [hvo, hct]; unfold State.voteOf
      have : (S.voteTerm[n.val]! == t1) = false := by simp only [beq_eq_false_iff_ne]; omega
      rw [this]; rfl
    refine ⟨by rw [hvn, h2, rr_nameOf_zero], fun hne => absurd hvn hne, hvo2, ?_, fun k _ => rfl⟩
    show S.voteTerm[n.val]! ≤ t1; omega

theorem rr_vote (hs : AntSim S V net) (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    VoteAt S (S₂) n w t1 Vs := by
  cases vo with
  | some x => exact rr_vote_some hs hok
  | none => exact rr_vote_none hs hok

/-- The leader logs only grow. -/
theorem rr_ll (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    (∀ t l, S.ledLog.get t = .ok l → ∃ e, ll.get t = .ok (l ++ e)) ∧
    (∀ t, S.ledLog.has t = true → ll.has t = true) := by
  rcases hok.hll with h | ⟨h, -, -, hpre, -⟩
  · subst h; exact ⟨fun t l hl => ⟨[], by rw [hl, List.append_nil]⟩, fun t h => h⟩
  · subst h
    refine ⟨fun t l hl => ?_, fun t ht => rr_has_with _ ht⟩
    by_cases ht : t = t1
    · subst ht
      obtain ⟨e, he⟩ := hpre l hl
      exact ⟨e, by rw [rr_get_with_self, he]⟩
    · exact ⟨[], by rw [rr_get_with_ne _ _ ht, hl, List.append_nil]⟩

theorem rr_ct_n (h : S.currentTerm.length = 3) : (S₂).currentTerm[n.val]! = t1 :=
  get!_set_self _ (by omega)
theorem rr_ct_o {k : Fin 3} (hk : k ≠ n) : (S₂).currentTerm[k.val]! = S.currentTerm[k.val]! :=
  get!_set_ne _ _ (fun e => hk (Fin.ext e))
theorem rr_log_n (h : S.log.length = 3) : (S₂).log[n.val]! = L1 := get!_set_self _ (by omega)
theorem rr_log_o {k : Fin 3} (hk : k ≠ n) : (S₂).log[k.val]! = S.log[k.val]! :=
  get!_set_ne _ _ (fun e => hk (Fin.ext e))
theorem rr_cm_n (h : S.commitIndex.length = 3) : (S₂).commitIndex[n.val]! = c := get!_set_self _ (by omega)
theorem rr_cm_o {k : Fin 3} (hk : k ≠ n) : (S₂).commitIndex[k.val]! = S.commitIndex[k.val]! :=
  get!_set_ne _ _ (fun e => hk (Fin.ext e))
theorem rr_cf_n (h : S.confirmed.length = 3) : (S₂).confirmed[n.val]! = cf := get!_set_self _ (by omega)
theorem rr_cf_o {k : Fin 3} (hk : k ≠ n) : (S₂).confirmed[k.val]! = S.confirmed[k.val]! :=
  get!_set_ne _ _ (fun e => hk (Fin.ext e))
theorem rr_ct_ge (hs : AntSim S V net) (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r)
    (k : Fin 3) : S.currentTerm[k.val]! ≤ (S₂).currentTerm[k.val]! := by
  by_cases hk : k = n
  · rw [hk, rr_ct_n hs.1.2.1]; exact hok.tge
  · rw [rr_ct_o hk]; exact Int.le_refl _

theorem rr_vote_ne_ack : (go!"vote" : Str) ≠ go!"ack" := by decide

/-- C3 at the new state. -/
theorem rr_binding (hs : AntSim S V net) (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    BindingOk (S₂) := by
  have hv := rr_vote hs hok
  have hge := rr_ct_ge hs hok
  have hllm := rr_ll hok
  obtain ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩, hb, -, -⟩ := hs
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18,
    hb19⟩ := hb
  refine ⟨hok.hviol, hb2, ?_, hok.tlLen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hok.tlSort⟩
  · -- undo
    intro k q hq
    change (S.undo.set n.val (some p))[k.val]! = some q at hq
    rw [rr_set_get _ sh11] at hq
    split at hq
    · obtain rfl := Option.some.inj hq; exact hok.made
    · exact hb3 k q hq
  · -- commits within chain
    intro k
    by_cases hk : k = n
    · rw [hk, rr_cm_n sh5, rr_log_n sh4]; exact hok.chainC
    · rw [rr_cm_o hk, rr_log_o hk]
      obtain ⟨h1, h2⟩ := hb5 k
      have hl := hok.hchain.length_le
      refine ⟨show S.commitIndex[k.val]! ≤ (ch.length : Int) by omega, ?_⟩
      show ch.take _ = _
      rw [rr_take_prefix hok.hchain (by omega), h2]
  · -- commits recorded
    intro k
    by_cases hk : k = n
    · rw [hk, rr_cm_n sh5, rr_ct_n sh1]; exact hok.tlC
    · rw [rr_cm_o hk, rr_ct_o hk]
      rcases hb6 k with h | ⟨q, hq, h1, h2⟩
      · exact .inl h
      · obtain ⟨q', hq', e1, e2⟩ := hok.tlDom q hq
        exact .inr ⟨q', hq', by omega, by omega⟩
  · -- confirmations prefixes of leader logs
    intro k l hlg
    by_cases hk : k = n
    · rw [hk] at hlg ⊢; rw [rr_cf_n sh10] at hlg ⊢; rw [rr_log_n sh4]; exact hok.hconf l hlg
    · rw [rr_cf_o hk] at hlg ⊢; rw [rr_log_o hk]
      change ll.get (S.confirmed[k.val]!).term = .ok l at hlg
      rcases hok.hll with heq | ⟨heq, -, ht1, hpre, -⟩
      · rw [heq] at hlg; exact hb7 k l hlg
      · by_cases hT : (S.confirmed[k.val]!).term = t1
        · rw [heq, hT, rr_get_with_self] at hlg
          obtain rfl := Except.ok.inj hlg
          rcases (hb16 k).1 with h0 | hhas | hall
          · rw [h0]; simp
          · obtain ⟨l0, hl0⟩ := rr_get_of_has hhas
            have hp0 := hpre l0 (hT ▸ hl0)
            obtain ⟨o1, o2, o3⟩ := hb7 k l0 hl0
            have hlen := hp0.length_le
            exact ⟨o1, by omega, by rw [o3, rr_take_prefix hp0 (by omega)]⟩
          · have := hall n; omega
        · rw [heq, rr_get_with_ne _ _ hT] at hlg; exact hb7 k l hlg
  · -- acks within confirmation or commit
    intro k a ha hty hsrc hterm
    change a ∈ M at ha
    by_cases hm : a ∈ S.msgs
    · by_cases hk : k = n
      · rw [hk] at hsrc hterm ⊢
        rw [rr_ct_n sh1] at hterm; rw [rr_cf_n sh10, rr_cm_n sh5]
        have hle := hb14 n a hm hty hsrc
        have htg := hok.tge
        have old := hb8 n a hm hty hsrc (by omega)
        rcases hok.cmono with e | ⟨e1, -, e3⟩
        · rw [e]; exact old.imp id (fun h => Int.le_trans h hok.cge)
        · rcases old with ⟨o1, o2⟩ | o
          · exact .inl ⟨e1.trans hterm.symm, Int.le_trans o2 (e3 (o1.trans hterm))⟩
          · exact .inr (Int.le_trans o hok.cge)
      · rw [rr_ct_o hk] at hterm; rw [rr_cf_o hk, rr_cm_o hk]; exact hb8 k a hm hty hsrc hterm
    · rcases hok.mnew a ha hm with hvt | ⟨-, hsrc', -, ht', hcov⟩
      · rw [hvt] at hty; exact absurd hty rr_vote_ne_ack
      · have hkn : k = n := name_inj (hsrc.symm.trans hsrc')
        rw [hkn, rr_cf_n sh10, rr_cm_n sh5]; exact hcov
  · -- leader logs' terms led
    intro q hq
    change q ∈ ll at hq
    rcases hok.hll with heq | ⟨heq, -, -, -, hin, -⟩
    · rw [heq] at hq; obtain ⟨l, hl, e⟩ := hb9 q hq; exact ⟨l, hok.lsub l hl, e⟩
    · rw [heq] at hq
      rcases rr_mem_with hq with hq | rfl
      · obtain ⟨l, hl, e⟩ := hb9 q hq; exact ⟨l, hok.lsub l hl, e⟩
      · exact ⟨_, hin, rfl⟩
  · -- leaders at their current term
    intro k l hl hsv
    change l ∈ ld at hl
    by_cases hm : l ∈ S.leaders
    · have old := hb10 k l hm hsv
      by_cases hk : k = n
      · rw [hk] at old ⊢; rw [rr_ct_n sh1]
        show _ ∨ (_ ∧ ro[n.val]! = leader)
        have htg := hok.tge
        rcases old with h | ⟨h1, h2⟩
        · exact .inl (by omega)
        · by_cases he : t1 = S.currentTerm[n.val]!
          · exact .inr ⟨by omega, hok.rstay h2 he⟩
          · exact .inl (by omega)
      · rw [rr_ct_o hk]
        show _ ∨ (_ ∧ ro[k.val]! = leader)
        rw [hok.rother k hk]; exact old
    · obtain ⟨rfl, hro, -⟩ := hok.lnew l hl hm
      have hkn : k = n := name_inj hsv.symm
      rw [hkn, rr_ct_n sh1]; exact .inr ⟨rfl, hro⟩
  · -- facts' servers
    intro f hf hty
    change f ∈ M at hf
    by_cases hm : f ∈ S.msgs
    · exact hb11 f hm hty
    · rcases hok.mnew f hf hm with h | ⟨-, h1, h2, -⟩
      · exact absurd h hty
      · exact ⟨⟨n, h1⟩, h2⟩
  · -- votes' voters
    intro y hy
    change y ∈ Vs at hy
    by_cases hm : y ∈ S.votes
    · exact hb12 y hm
    · exact ⟨n, by rw [(hok.vnew y hy hm).1]⟩
  · -- a node's vote recorded
    intro k hne
    by_cases hk : k = n
    · rw [hk] at hne ⊢; rw [rr_ct_n sh1]; exact hv.2.1 hne
    · rw [hv.2.2.1 k hk] at hne ⊢; rw [rr_ct_o hk]; exact hok.vsub _ (hb13 k hne)
  · -- AckTermsOk
    intro k a ha hty hsrc
    change a ∈ M at ha
    by_cases hm : a ∈ S.msgs
    · exact Int.le_trans (hb14 k a hm hty hsrc) (hge k)
    · rcases hok.mnew a ha hm with hvt | ⟨-, hsrc', -, ht', -⟩
      · rw [hvt] at hty; exact absurd hty rr_vote_ne_ack
      · have hkn : k = n := name_inj (hsrc.symm.trans hsrc')
        rw [hkn, rr_ct_n sh1, ht']; exact Int.le_refl _
  · -- VoteTermOk
    intro k
    by_cases hk : k = n
    · rw [hk, rr_ct_n sh1]; exact hv.2.2.2.1
    · rw [rr_ct_o hk, hv.2.2.2.2 k hk]; exact hb15 k
  · -- ConfirmedOk
    intro j
    have hold : ∀ C : Confirmed, ((C.index = 0 ∨ S.ledLog.has C.term = true ∨
        ∀ i : Fin 3, C.term < S.currentTerm[i.val]!)) →
        (C.index = 0 ∨ ll.has C.term = true ∨ ∀ i : Fin 3, C.term < (S₂).currentTerm[i.val]!) :=
      fun C h => h.imp id (Or.imp (hllm.2 _) (fun h i => Int.lt_of_lt_of_le (h i) (hge i)))
    by_cases hj : j = n
    · rw [hj, rr_cf_n sh10, rr_ct_n sh1]
      rcases hok.cmono with e | ⟨e1, e2, -⟩
      · rw [e]; exact ⟨hold _ (hb16 n).1, Int.le_trans (hb16 n).2 hok.tge⟩
      · exact ⟨.inr (.inl (e1 ▸ e2)), Int.le_of_eq e1⟩
    · rw [rr_cf_o hj, rr_ct_o hj]; exact ⟨hold _ (hb16 j).1, (hb16 j).2⟩
  · -- TermLenOk
    refine ⟨fun T hT => ?_, fun k hk => ?_⟩
    · change 0 < tlOld tl T at hT
      by_cases hlt : tlOld S.termLen T < tlOld tl T
      · obtain ⟨e1, ⟨l, hl, hlt'⟩, -⟩ := hok.tlNew T hlt
        exact .inl ⟨l, hl, hlt'.trans e1.symm⟩
      · rcases hb17.1 T (by omega) with ⟨l, hl, hlt'⟩ | h
        · exact .inl ⟨l, hok.lsub l hl, hlt'⟩
        · exact .inr fun i => Int.lt_of_lt_of_le (h i) (hge i)
    · change ro[k.val]! = leader at hk
      change (AntCheck.termAt ((S₂).log[k.val]!) ((S₂).commitIndex[k.val]!) = (S₂).currentTerm[k.val]! →
          (S₂).commitIndex[k.val]! ≤ tlOld tl ((S₂).currentTerm[k.val]!)) ∧
        tlOld tl ((S₂).currentTerm[k.val]!) ≤ (S₂).commitIndex[k.val]!
      by_cases hkn : k = n
      · subst hkn
        rw [rr_ct_n sh1, rr_cm_n sh5, rr_log_n sh4]; exact hok.tlSelf hk
      · rw [rr_ct_o hkn, rr_cm_o hkn, rr_log_o hkn]
        have hk' : S.role[k.val]! = leader := by rw [← hok.rother k hkn]; exact hk
        obtain ⟨o1, o2⟩ := hb17.2 k hk'
        refine ⟨fun h => Int.le_trans (o1 h) (hok.tlMono _), ?_⟩
        by_cases hlt : tlOld S.termLen (S.currentTerm[k.val]!) < tlOld tl (S.currentTerm[k.val]!)
        · obtain ⟨e1, -, e3⟩ := hok.tlNew _ hlt
          rw [e1]; exact e3 k hkn hk' e1
        · omega
  · -- LedConfOk
    exact hok.lconf

/-- C4 at the new state. -/
theorem rr_net (hs : AntSim S V net) (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    NetOk (S₂) net := by
  have hge := rr_ct_ge hs hok
  have hllm := rr_ll hok
  obtain ⟨⟨sh0, sh1, -, -, -, sh5, -, -, -, -, sh10, -⟩, hb, hn, -⟩ := hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb16, -⟩ := hb
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hn
  have hsend : ∀ f, S.sendable f = .ok true → (S₂).sendable f = .ok true := fun f h =>
    rr_sendableIn_mono hok.lsub hllm.1 hok.hchain hok.tlDom h
  refine ⟨fun m hm => ?_, ?_, hn3, fun m hm hty i hsrc hro hct => ?_⟩
  rotate_left 2
  · change ro[i.val]! ≠ follower at hro
    by_cases hin : i = n
    · subst hin
      rw [rr_ct_n sh1] at hct; rw [rr_cm_n sh5]
      obtain ⟨-, ⟨i', hsrc', hti⟩, -⟩ := hn1 m hm
      have hii : i' = i := nodeId_inj (hsrc'.symm.trans hsrc)
      subst hii
      have ht1 : t1 = S.currentTerm[i'.val]! := by have := hok.tge; omega
      exact Int.le_trans (hn4 m hm hty i' hsrc (hok.rnf hro ht1) (ht1 ▸ hct)) hok.cge
    · rw [rr_ct_o hin] at hct; rw [rr_cm_o hin]
      rw [hok.rother i hin] at hro
      exact hn4 m hm hty i hsrc hro hct
  · obtain ⟨hty, ⟨i, hsrc, hti⟩, j, hdst, hj⟩ := hn1 m hm
    refine ⟨hty, ⟨i, hsrc, Int.le_trans hti (hge i)⟩, j, hdst, fun hle => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hj (Int.le_trans (hge j) hle)
    refine ⟨fun ht => ?_, fun ht => ?_, fun ht => hok.msub _ (h3 ht), fun ht => AckIn.mono hok.msub (h4 ht)⟩
    · have := h1 ht
      cases hf : AntCheck.toAppendFact (msgOf m m.dst) with
      | error e => rw [hf] at this; cases this
      | ok f => rw [hf] at this; exact hsend f this
    · obtain ⟨f, hf, hfm⟩ := h2 ht; exact ⟨f, hf, hok.msub f hfm⟩
  · intro m hm hty j hdst hle
    have old := hn2 m hm hty j hdst (Int.le_trans (hge j) hle)
    by_cases hj : j = n
    · rw [hj] at hle old ⊢; rw [rr_ct_n sh1] at hle; rw [rr_cf_n sh10, rr_cm_n sh5]
      rcases hok.cmono with e | ⟨e1, -, e3⟩
      · rw [e]; exact old.imp id (fun h => Int.le_trans h hok.cge)
      · rcases old with ⟨o1, o2⟩ | o
        · have hc := (hb16 n).2
          have htg := hok.tge
          have ht : (S.confirmed[n.val]!).term = t1 := by omega
          exact .inl ⟨by omega, Int.le_trans o2 (e3 ht)⟩
        · exact .inr (Int.le_trans o hok.cge)
    · rw [rr_cf_o hj, rr_cm_o hj]; exact old

/-- Another node's facts at the new state. -/
theorem rr_node_other (hs : AntSim S V net) (hgo : GlobalOk S net G) (hl : RaftLaws G)
    (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) {k : Fin 3} (hk : k ≠ n) :
    NodeOk (S₂) net k (V k) := by
  have hv := rr_vote hs hok
  obtain ⟨⟨⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13⟩, hL, hC, hP, hQ, hT, hca, hlo⟩⟩ :=
    (⟨hs.2.2.2 k⟩ : Nonempty (NodeOk S net k (V k)))
  refine ⟨⟨by rw [rr_ct_o hk]; exact d1, by rw [hv.2.2.1 k hk]; exact d2, by rw [rr_log_o hk]; exact d3,
    by rw [rr_cm_o hk]; exact d4, by show ro[k.val]! = _; rw [hok.rother k hk]; exact d5, d6, d7, d8, d9,
    by show r.config[k.val]! = _; rw [hok.hmem.1]; exact d10,
    by show r.confAt[k.val]! = _; rw [hok.hmem.2]; exact d11, d12, d13⟩, ?_, ?_, hP, ?_, hT, hca, hlo⟩
  · intro hlk
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL hlk
    refine ⟨List.contains_iff_mem.mpr (hok.lsub _ (List.contains_iff_mem.mp l1)), ?_,
      fun j x h1 h2 => AckIn.mono hok.msub (l3 j x h1 h2), fun j hj => (l4 j hj).imp id (AckIn.mono hok.msub),
      by unfold LeaderConfOk; rw [rr_cf_o hk]; exact l5⟩
    change ll.get _ = _
    rcases hok.hll with heq | ⟨heq, hro, -, -, -, -⟩
    · rw [heq]; exact l2
    · rw [heq]
      by_cases hT : uint.Z (V k).ps.term = t1
      · exfalso
        obtain ⟨j, t, hjt, hsv, htt⟩ := hgo.1 _ (List.contains_iff_mem.mp l1)
        have hgn := hok.glead hro
        have htw : t = w.ps.term := uint_Z_inj.mp (by rw [← htt]; exact hT.trans hok.hterm)
        have hj := hl.1 _ hjt _ hgn htw
        exact hk (nodeId_inj ((nameOf_inj hsv).trans hj))
      · rw [rr_get_with_ne _ _ hT]; exact l2
  · intro hck
    obtain ⟨c1, c2⟩ := hC hck
    refine ⟨fun j hj => rr_granted_mono (s1 := S₂) (s := S) k.val rfl (rr_ct_o hk) hok.msub hok.vsub (c1 j hj), ?_⟩
    rw [rr_ct_o hk]
    have hvr : (S₂).voteRequest k.val (S.currentTerm[k.val]!) = S.voteRequest k.val (S.currentTerm[k.val]!) := by
      unfold State.voteRequest State.lastTerm; rw [rr_log_o hk]; rfl
    rw [hvr]; exact hok.msub _ c2
  · intro q hq
    obtain ⟨a1, a2, a3, a4, a5⟩ := hQ q hq
    exact ⟨a1, a2, a3, a4, a5.imp (fun h => ⟨h.1, AckIn.mono hok.msub h.2⟩) (fun h => ⟨h.1, hok.vsub _ h.2⟩)⟩

/-- The node's facts at the new state. -/
theorem rr_node_self (hs : AntSim S V net) (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    NodeOk (S₂) net n w := by
  have hv := rr_vote hs hok
  have sh := hs.1
  obtain ⟨⟨-, -, -, -, -, d6, -, -, -, d10, d11, -, -⟩, -, -, -, -, hT, hca, -⟩ := hs.2.2.2 n
  obtain ⟨w1, w2, w3, w4, w5⟩ := hok.wf
  refine ⟨⟨by rw [rr_ct_n sh.2.1]; exact hok.hterm, hv.1, by rw [rr_log_n sh.2.2.2.2.1]; exact hok.hlog,
    by rw [rr_cm_n sh.2.2.2.2.2.1]; exact hok.hcommit, hok.hrole, by rw [hok.hdel]; exact d6, w1, w2, w3,
    by show r.config[n.val]! = _; rw [hok.hmem.1]; exact d10,
    by show r.confAt[n.val]! = _; rw [hok.hmem.2]; exact d11, w4, w5⟩,
    hok.lpart, hok.cpart, hok.hpend, hok.hqs, ?_, ?_, hok.hlead, hok.hvself⟩
  · intro ht
    rw [hok.drain.1] at ht
    obtain ⟨m, hm, hp⟩ := hT ht
    exact ⟨m, hok.drain.2 ▸ hm, hp⟩
  · intro m hm
    rw [hok.drain.2] at hm
    exact hca m hm

/-- C5 at the new state. -/
theorem rr_global (hs : AntSim S V net) (hgo : GlobalOk S net G)
    (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    GlobalOk (S₂) net G := by
  have sh4 := hs.1.2.2.2.2.1
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hgo
  refine ⟨fun l hl => ?_, fun y hy => ?_, fun k => ?_, fun q hq => ?_, hok.chainG, hok.tlG, g7⟩
  · change l ∈ ld at hl
    by_cases hm : l ∈ S.leaders
    · exact g1 l hm
    · obtain ⟨rfl, -, hg⟩ := hok.lnew l hl hm
      exact ⟨nodeId n, w.ps.term, hg, rfl, hok.hterm⟩
  · change y ∈ Vs at hy
    by_cases hm : y ∈ S.votes
    · exact g2 y hm
    · obtain ⟨rfl, hg⟩ := hok.vnew y hy hm
      exact ⟨nodeId n, w.ps.term, w.ps.vote, hg, rfl, hok.hterm, rfl⟩
  · by_cases hk : k = n
    · rw [hk, rr_log_n sh4]; exact ⟨w.ps.log, hok.logG, hok.hlog⟩
    · rw [rr_log_o hk]; exact g3 k
  · change q ∈ ll at hq
    rcases hok.hll with heq | ⟨heq, -, -, -, -, hcamp⟩
    · rw [heq] at hq; exact g4 q hq
    · rw [heq] at hq
      rcases rr_mem_with hq with hq | rfl
      · exact g4 q hq
      · exact ⟨w.ps.log, hok.logG, hok.hlog, hcamp⟩

/-- The binding's lists at the new state. -/
theorem rr_shape (hs : AntSim S V net) (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    Shape (S₂) := by
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hs.1
  refine ⟨sh0, by show (S.currentTerm.set _ _).length = 3; rw [List.length_set]; exact sh1, ?_, ?_,
    by show (S.log.set _ _).length = 3; rw [List.length_set]; exact sh4,
    by show (S.commitIndex.set _ _).length = 3; rw [List.length_set]; exact sh5, hok.rlen, sh7,
    by show r.config.length = 3; rw [hok.hmem.1]; exact sh8,
    by show r.confAt.length = 3; rw [hok.hmem.2]; exact sh9,
    by show (S.confirmed.set _ _).length = 3; rw [List.length_set]; exact sh10,
    by show (S.undo.set _ _).length = 3; rw [List.length_set]; exact sh11, sh12, sh13, sh14⟩
  · show (match vo with | some _ => S.voteTerm.set n.val t1 | none => S.voteTerm).length = 3
    cases vo <;> simp only [List.length_set, sh2]
  · show (match vo with | some x => S.voteFor.set n.val x | none => S.voteFor).length = 3
    cases vo <;> simp only [List.length_set, sh3]

end main

/-- **The relation after a `ready`**, and no violation. -/
theorem ready_rel {S : State} {V : Fin 3 → NodeView} {net : List Msg} {G : RaftFacts} {n : Fin 3}
    {w : NodeView} {t1 : Int} {vo : Option Str} {L1 : List Entry} {c : Int} {ro : List Str}
    {cf : Confirmed} {M : List Fact} {Vs : List VoteRec} {ld : List LeaderRec}
    {ll : TermFn (List Entry)} {p : Pre} {ch : List Entry} {tl : TermFn Int} {vi : SSet}
    {r : MemResult}
    (hs : AntSim S V net) (hgo : GlobalOk S net G) (hl : RaftLaws G)
    (hok : ReadyOk S V net G n w t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) :
    AntSim (readyS S n.val t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) (setV V n w) net ∧
      GlobalOk (readyS S n.val t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) net G ∧
      violated (readyS S n.val t1 vo L1 c ro cf M Vs ld ll p ch tl vi r) = [] := by
  have hg := rr_global hs hgo hok
  refine ⟨⟨rr_shape hs hok, rr_binding hs hok, rr_net hs hok, fun k => ?_⟩, hg,
    violated_nil hok.hviol hl hg⟩
  by_cases hk : k = n
  · simp only [setV, hk, ite_true]; exact rr_node_self hs hok
  · simp only [setV, hk, ite_false]; exact rr_node_other hs hgo hl hok hk

end rel

end AntSim
end EtcdGrove
end Perennial
