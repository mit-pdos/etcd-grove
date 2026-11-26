/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `GC` (#33 S4, the invariant phase)

`antSim_gc` (`Stmts.lean`): from a state related to the nodes, the checker's `GC` steps
(`gcLoop`, B 713-723, taken while `GCDue` before each event) end within `gcFuel` with no
violation, and the relation holds after them. A `GC` step removes only what C2-C4 never name: a
vote request or a leader log of a term every node has passed (`Over`), a grant, an ack or a vote
of a term its receiver (voter) has passed, an ack below a larger one of the same sender, receiver
and term (`notes/antithesis-rawnode-design.md` §3.3). It removes something whenever it is due,
so `gcFuel` (the facts, votes and leader logs, plus one) bounds the steps.

Also here, for every per-report lemma: the laws of the transcription's evaluation (`filterM`,
`anyM`), the servers' names (`nameOf` injective, `State.idx` of a node's name), `violated` empty
under `GlobalOk` (`violated_nil`), and `Prefix.snoc` (one more event through `Checker.next`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Stmts

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

variable {R : RunCfg}

/-! ## The evaluation monad -/

theorem eok_bind {α β : Type} (x : α) (f : α → EvalM β) : ((Except.ok x : EvalM α) >>= f) = f x := rfl

theorem epure {α : Type} (x : α) : (Pure.pure x : EvalM α) = .ok x := rfl

theorem filterM_go {α : Type} (f : α → EvalM Bool) : ∀ (xs acc g : List α),
    xs.foldlM (fun out x => do if (← f x) then pure (out ++ [x]) else pure out) acc = .ok g →
    ∀ y ∈ g, y ∈ acc ∨ (y ∈ xs ∧ f y = .ok true)
  | [], acc, g, h => by
    simp only [List.foldlM_nil] at h; cases h; exact fun y hy => .inl hy
  | x :: xs, acc, g, h => by
    rw [List.foldlM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok b =>
      rw [hx] at h
      cases b with
      | true =>
        intro y hy
        rcases filterM_go f xs (acc ++ [x]) g h y hy with h1 | ⟨h1, h2⟩
        · rcases List.mem_append.mp h1 with h1 | h1
          · exact .inl h1
          · rw [List.mem_singleton] at h1; subst h1; exact .inr ⟨List.mem_cons_self, hx⟩
        · exact .inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      | false =>
        intro y hy
        rcases filterM_go f xs acc g h y hy with h1 | ⟨h1, h2⟩
        · exact .inl h1
        · exact .inr ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- An element of `filterM`'s result is one of the list's that the test accepts. -/
theorem filterM_mem {α : Type} {f : α → EvalM Bool} {xs g : List α} (h : filterM xs f = .ok g)
    {y : α} (hy : y ∈ g) : y ∈ xs ∧ f y = .ok true := by
  rcases filterM_go f xs [] g h y hy with h1 | h1
  · cases h1
  · exact h1

theorem filterM_go_ok {α : Type} (f : α → EvalM Bool) : ∀ (xs acc : List α),
    (∀ x ∈ xs, ∃ b, f x = .ok b) →
    ∃ g, xs.foldlM (fun out x => do if (← f x) then pure (out ++ [x]) else pure out) acc = .ok g
  | [], acc, _ => ⟨acc, rfl⟩
  | x :: xs, acc, h => by
    rw [List.foldlM_cons]
    obtain ⟨b, hb⟩ := h x List.mem_cons_self
    rw [hb]
    cases b with
    | true => exact filterM_go_ok f xs _ (fun y hy => h y (List.mem_cons_of_mem _ hy))
    | false => exact filterM_go_ok f xs _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- `filterM` evaluates where its test does. -/
theorem filterM_ok {α : Type} {f : α → EvalM Bool} {xs : List α} (h : ∀ x ∈ xs, ∃ b, f x = .ok b) :
    ∃ g, filterM xs f = .ok g :=
  filterM_go_ok f xs [] h

/-- `anyM` holds of a witness. -/
theorem anyM_true {α : Type} {f : α → EvalM Bool} : ∀ {xs : List α}, anyM xs f = .ok true →
    ∃ x ∈ xs, f x = .ok true
  | [], h => by simp only [anyM, epure] at h; cases h
  | x :: xs, h => by
    simp only [anyM] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok b =>
      rw [hx] at h
      cases b with
      | true => exact ⟨x, List.mem_cons_self, hx⟩
      | false =>
        obtain ⟨y, hy, hy'⟩ := anyM_true h
        exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- `anyM` evaluates where its test does. -/
theorem anyM_ok {α : Type} {f : α → EvalM Bool} : ∀ {xs : List α}, (∀ x ∈ xs, ∃ b, f x = .ok b) →
    ∃ b, anyM xs f = .ok b
  | [], _ => ⟨false, rfl⟩
  | x :: xs, h => by
    simp only [anyM]
    obtain ⟨b, hb⟩ := h x List.mem_cons_self
    rw [hb]
    cases b with
    | true => exact ⟨true, rfl⟩
    | false => exact anyM_ok (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-! ## The servers' names -/

theorem nameOf_inj {a b : w64} (h : nameOf a = nameOf b) : a = b := by
  unfold nameOf at h
  by_cases ha : a = W64 0 <;> by_cases hb : b = W64 0
  · rw [ha, hb]
  · simp [ha, hb] at h; exact absurd h hb
  · simp [ha, hb] at h; exact absurd h ha
  · simp only [ha, hb, ite_false, List.append_cancel_left_eq] at h
    have h2 := congrArg (fun s => internal.strconv.parseUint s 10 64) h
    simp only [internal.strconv.parseUint_fmtUint10] at h2
    injection h2 with h2
    exact BitVec.eq_of_toNat_eq h2

theorem nodeId_inj {R : RunCfg} {i j : Fin R.N} (h : nodeId i = nodeId j) : i = j := by
  have := R.hK.2.2; have hi := i.isLt; have hj := j.isLt
  unfold nodeId at h; apply Fin.ext
  have h2 := congrArg (fun w : w64 => w.toNat) h
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt] at h2
  omega

theorem name_inj {R : RunCfg} {i j : Fin R.N} (h : nameOf (nodeId i) = nameOf (nodeId j)) : i = j :=
  nodeId_inj (nameOf_inj h)

theorem server_get {N : Nat} (j : Fin N) : (namesL N)[j.val]! = nameOf (nodeId j) := by
  simp [namesL, nodeId, j.isLt]

theorem namesL_length (N : Nat) : (namesL N).length = N := by simp [namesL]

/-- Up to 9 servers, the names are sorted (`raft1` < … < `raft9`), so `SetOf(names(N))` is
`names(N)`, and each name's position is its node's. -/
theorem setOf_namesL {N : Nat} (hN : N ≤ 9) : AntCheck.setOf (namesL N) = namesL N := by
  have : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 ∨ N = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem idxOf_name {N : Nat} (hN : N ≤ 9) (j : Fin N) : (namesL N).idxOf? (nameOf (nodeId j)) = some j.val := by
  have : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 ∨ N = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert j <;> decide +kernel

theorem RunCfg.server_eq (R : RunCfg) : R.cfg.server = namesL R.N := setOf_namesL R.hK.2.2

theorem idx_name {R : RunCfg} {S : State} (h : S.cfg = R.cfg) (j : Fin R.N) :
    S.idx (nameOf (nodeId j)) = .ok j.val := by
  unfold State.idx; rw [h, R.server_eq, idxOf_name R.hK.2.2]; rfl

theorem server_of {R : RunCfg} {S : State} (h : S.cfg = R.cfg) (j : Fin R.N) :
    S.cfg.server[j.val]! = nameOf (nodeId j) := by
  rw [h, R.server_eq, server_get]

theorem server_length {R : RunCfg} {S : State} (h : S.cfg = R.cfg) : S.cfg.server.length = R.N := by
  rw [h, R.server_eq, namesL_length]

/-! ## What `GC` removes -/

theorem effTerm_le (S : State) (j : Nat) : S.effTerm j ≤ S.currentTerm[j]! := by
  unfold State.effTerm; split
  · exact Int.le_refl _
  · unfold imin; split <;> omega

/-- A term some node has not passed is not `Over`. -/
theorem over_false {S : State} (hc : S.cfg = R.cfg) {t : Int} (j : Fin R.N) (h : S.currentTerm[j.val]! ≤ t) :
    S.over t = false := by
  unfold State.over
  rw [server_length hc]
  cases h' : (List.range R.N).all (fun j => decide (S.effTerm j > t))
  · rfl
  · rw [List.all_eq_true] at h'
    have h1 := h' j.val (List.mem_range.mpr j.isLt)
    have h2 := effTerm_le S j.val
    simp only [decide_eq_true_eq] at h1
    omega

theorem garbage_vote {S : State} {g : List Fact} (hg : S.garbage = .ok g) {f : Fact} (hf : f ∈ g)
    (ht : f.type = go!"vote") : S.over f.term = true := by
  unfold State.garbage at hg
  have h := (filterM_mem hg hf).2
  simp (config := { decide := true }) only [ht, ite_true, epure] at h
  injection h

theorem garbage_grant {S : State} (hc : S.cfg = R.cfg) {g : List Fact} (hg : S.garbage = .ok g) {f : Fact}
    (hf : f ∈ g) (ht : f.type = go!"grant") (j : Fin R.N) (hd : f.dst = nameOf (nodeId j)) :
    S.effTerm j.val > f.term := by
  unfold State.garbage at hg
  have h := (filterM_mem hg hf).2
  simp (config := { decide := true }) only [ht, hd, idx_name hc, ite_true, ite_false, epure, eok_bind,
    Bool.false_eq_true] at h
  injection h with h
  exact of_decide_eq_true h

theorem garbage_ack {S : State} (hc : S.cfg = R.cfg) {g : List Fact} (hg : S.garbage = .ok g) {f : Fact}
    (hf : f ∈ g) (ht : f.type = go!"ack") (j : Fin R.N) (hd : f.dst = nameOf (nodeId j)) :
    S.effTerm j.val > f.term ∨ ∃ a ∈ S.msgs, a.type = go!"ack" ∧ a.src = f.src ∧ a.dst = f.dst ∧
      a.term = f.term ∧ a.index > f.index := by
  unfold State.garbage at hg
  have h := (filterM_mem hg hf).2
  simp (config := { decide := true }) only [ht, hd, idx_name hc, ite_true, ite_false, epure, eok_bind,
    Bool.false_eq_true] at h
  by_cases he : S.effTerm j.val > f.term
  · exact .inl he
  · right
    rw [if_neg (by simpa using he)] at h
    obtain ⟨a, ha, h⟩ := anyM_true h
    refine ⟨a, ha, ?_⟩
    by_cases hcond : (a.type == go!"ack" && a.src == f.src && a.dst == nameOf (nodeId j) && a.term == f.term &&
        decide (a.index > f.index)) = true
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcond
      exact ⟨h1, h2, h3.trans hd.symm, h4, h5⟩
    · rw [if_neg hcond] at h; cases h

/-- The facts' well-formedness `GC` needs (`BindingOk`'s last conjuncts). -/
def FactsWf (R : RunCfg) (S : State) : Prop :=
  (∀ f ∈ S.msgs, f.type ≠ go!"vote" →
    (∃ i : Fin R.N, f.src = nameOf (nodeId i)) ∧ ∃ j : Fin R.N, f.dst = nameOf (nodeId j)) ∧
  (∀ v ∈ S.votes, ∃ i : Fin R.N, v.voter = nameOf (nodeId i))

theorem garbage_ok {S : State} (hc : S.cfg = R.cfg) (hw : FactsWf R S) : ∃ g, S.garbage = .ok g := by
  unfold State.garbage
  apply filterM_ok
  intro m hm
  by_cases hv : m.type = go!"vote"
  · simp (config := { decide := true }) only [hv, ite_true, epure]; exact ⟨_, rfl⟩
  · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hw.1 m hm hv
    have hv' : (m.type == go!"vote") = false := by simp [hv]
    simp only [hv', hj, idx_name hc, eok_bind, epure, Bool.false_eq_true, ite_false]
    split
    · exact ⟨_, rfl⟩
    split
    · split
      · exact ⟨_, rfl⟩
      apply anyM_ok
      intro a _
      split
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rw [hcond.1.1.1.2, hi, idx_name hc, eok_bind]
        split <;> exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem oldVotes_ok {S : State} (hc : S.cfg = R.cfg) (hw : FactsWf R S) : ∃ o, S.oldVotes = .ok o := by
  unfold State.oldVotes
  apply filterM_ok
  intro v hv
  obtain ⟨i, hi⟩ := hw.2 v hv
  rw [hi, idx_name hc, eok_bind]
  exact ⟨_, rfl⟩

theorem oldVotes_mem {S : State} (hc : S.cfg = R.cfg) {o : List VoteRec} (ho : S.oldVotes = .ok o)
    {v : VoteRec} (hv : v ∈ o) (j : Fin R.N) (hj : v.voter = nameOf (nodeId j)) : S.effTerm j.val > v.term := by
  unfold State.oldVotes at ho
  have h := (filterM_mem ho hv).2
  rw [hj, idx_name hc, eok_bind] at h
  injection h with h
  exact of_decide_eq_true h

/-! ## Lists -/

theorem lset_minus_mem {α : Type} [DecidableEq α] {s t : List α} {x : α} :
    x ∈ lset.minus s t ↔ x ∈ s ∧ x ∉ t := by
  simp [lset.minus, List.mem_filter]

theorem lset_minus_length_le {α : Type} [DecidableEq α] (s t : List α) :
    (lset.minus s t).length ≤ s.length := List.length_filter_le _ _

theorem lset_minus_length_lt {α : Type} [DecidableEq α] {s t : List α} (ht : ∀ x ∈ t, x ∈ s)
    (hne : t ≠ []) : (lset.minus s t).length < s.length := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil t hne
  unfold lset.minus
  rw [List.length_filter_lt_length_iff_exists]
  exact ⟨x, ht x hx, by simp [hx]⟩

theorem find?_without {α : Type} (st : List Int) (t : Int) : ∀ f : TermFn α,
    (f.filter (fun p => !st.contains p.1)).find? (fun p => p.1 == t) =
      if st.contains t then none else f.find? (fun p => p.1 == t)
  | [] => by simp
  | p :: ps => by
    rw [List.filter_cons]
    by_cases hp : p.1 = t
    · subst hp
      by_cases hs : st.contains p.1 = true
      · simp only [hs, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
        rw [find?_without st p.1 ps, if_pos hs]
      · have hs' : st.contains p.1 = false := by simpa using hs
        simp only [hs', Bool.not_false, ite_true, Bool.false_eq_true, ite_false, List.find?_cons,
          beq_self_eq_true]
    · have hpt : (p.1 == t) = false := by simp [hp]
      by_cases hs : st.contains p.1 = true
      · simp only [hs, Bool.not_true, Bool.false_eq_true, ite_false, List.find?_cons, hpt]
        exact find?_without st t ps
      · simp only [hs, Bool.not_false, ite_true, List.find?_cons, hpt]
        exact find?_without st t ps

theorem get_without {α : Type} (f : TermFn α) (st : List Int) (t : Int) :
    (f.without st).get t = if st.contains t then evalError "a function on terms applied outside its domain"
      else f.get t := by
  unfold TermFn.without TermFn.get
  rw [find?_without]
  by_cases hs : st.contains t = true
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]

theorem has_without {α : Type} (f : TermFn α) (st : List Int) (t : Int) :
    (f.without st).has t = (!st.contains t && f.has t) := by
  unfold TermFn.without TermFn.has
  induction f with
  | nil => simp
  | cons p ps ih =>
    rw [List.filter_cons]
    by_cases hp : p.1 = t
    · subst hp; by_cases hs : st.contains p.1 = true <;> simp_all
    · have hpt : (p.1 == t) = false := by simp [hp]
      by_cases hs : st.contains p.1 = true
      · have hs' : st.contains p.1 = true := hs
        simp only [List.any_cons, hs', hpt, Bool.not_true, Bool.false_and, Bool.false_or, ih, ite_false,
          Bool.false_eq_true]
      · have hs' : st.contains p.1 = false := by simpa using hs
        simp only [List.any_cons, hs', hpt, Bool.not_false, Bool.true_and, Bool.false_or, ih, ite_true]

theorem exists_max {α : Type} (f : α → Int) (P : α → Prop) : ∀ (l : List α), (∃ x ∈ l, P x) →
    ∃ x ∈ l, P x ∧ ∀ y ∈ l, P y → f y ≤ f x
  | [], ⟨_, h, _⟩ => by cases h
  | a :: l, h => by
    by_cases hl : ∃ x ∈ l, P x
    · obtain ⟨x, hx, hPx, hmax⟩ := exists_max f P l hl
      by_cases ha : P a ∧ f a > f x
      · refine ⟨a, List.mem_cons_self, ha.1, fun y hy hPy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Int.le_refl _
        · have := hmax y hy hPy; omega
      · refine ⟨x, List.mem_cons_of_mem _ hx, hPx, fun y hy hPy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · by_cases hP : P y
          · have : ¬ f y > f x := fun h' => ha ⟨hP, h'⟩
            omega
          · exact absurd hPy hP
        · exact hmax y hy hPy
    · obtain ⟨x, hx, hPx⟩ := h
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨x, List.mem_cons_self, hPx, fun y hy hPy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Int.le_refl _
        · exact absurd ⟨y, hy, hPy⟩ hl
      · exact absurd ⟨x, hx, hPx⟩ hl

/-! ## One `GC` step -/

/-- The state `GC` leaves, given `Garbage` and `OldVotes`. -/
def gcRes (S : State) (g : List Fact) (o : List VoteRec) : State :=
  { S with msgs := lset.minus S.msgs g, votes := lset.minus S.votes o,
           ledLog := S.ledLog.without S.staleLed, ledConf := S.ledConf.without S.staleLed,
           ledAt := S.ledAt.without S.staleLed, elAt := S.elAt.without S.staleLed,
           leaders := S.leaders.filter (fun l => !S.over l.term) }

theorem gc_eq {S : State} {g : List Fact} {o : List VoteRec} (hg : S.garbage = .ok g)
    (ho : S.oldVotes = .ok o) : S.gc = .ok (gcRes S g o) := by
  unfold State.gc; rw [hg, ho]; rfl

section keep
variable {S : State} {g : List Fact} {o : List VoteRec} {t : Int}

theorem staleLed_contains (hn : S.over t = false) : S.staleLed.contains t = false := by
  unfold State.staleLed
  cases h : (List.map Prod.fst (List.filter (fun p => S.over p.1) S.ledLog)).contains t
  · rfl
  · exfalso
    have h' := List.contains_iff_mem.mp h
    simp only [List.mem_map, List.mem_filter] at h'
    obtain ⟨p, ⟨_, hp⟩, rfl⟩ := h'
    rw [hn] at hp; cases hp

theorem gcRes_leaders_sub {l : LeaderRec} (h : l ∈ (gcRes S g o).leaders) : l ∈ S.leaders :=
  (List.mem_filter.mp h).1

theorem gcRes_leaders_keep {l : LeaderRec} (h : l ∈ S.leaders) (hn : S.over l.term = false) :
    l ∈ (gcRes S g o).leaders :=
  List.mem_filter.mpr ⟨h, by simp [hn]⟩

theorem gcRes_msgs_sub {f : Fact} (h : f ∈ (gcRes S g o).msgs) : f ∈ S.msgs :=
  (lset_minus_mem.mp h).1

theorem gcRes_votes_sub {v : VoteRec} (h : v ∈ (gcRes S g o).votes) : v ∈ S.votes :=
  (lset_minus_mem.mp h).1

theorem gcRes_ledLog_sub {p : Int × List Entry} (h : p ∈ (gcRes S g o).ledLog) :
    p ∈ S.ledLog ∧ S.over p.1 = false := by
  have h' := List.mem_filter.mp h
  refine ⟨h'.1, ?_⟩
  cases hn : S.over p.1
  · rfl
  · exfalso
    have : S.staleLed.contains p.1 = true := by
      unfold State.staleLed
      exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨h'.1, hn⟩, rfl⟩)
    have h2 := h'.2
    rw [this] at h2; cases h2

theorem gcRes_get (hn : S.over t = false) : (gcRes S g o).ledLog.get t = S.ledLog.get t := by
  show (S.ledLog.without S.staleLed).get t = _
  rw [get_without, staleLed_contains hn]; rfl

theorem gcRes_has (hn : S.over t = false) : (gcRes S g o).ledLog.has t = S.ledLog.has t := by
  show (S.ledLog.without S.staleLed).has t = _
  rw [has_without, staleLed_contains hn]; rfl

theorem gcRes_get_ok {l : List Entry} (h : (gcRes S g o).ledLog.get t = .ok l) : S.ledLog.get t = .ok l := by
  change (S.ledLog.without S.staleLed).get t = _ at h
  rw [get_without] at h
  split at h
  · cases h
  · exact h

variable (hc : S.cfg = R.cfg) (hg : S.garbage = .ok g) (ho : S.oldVotes = .ok o)
include hc hg

theorem gcRes_vote_keep {f : Fact} (h : f ∈ S.msgs) (ht : f.type = go!"vote") (hn : S.over f.term = false) :
    f ∈ (gcRes S g o).msgs := by
  refine lset_minus_mem.mpr ⟨h, fun hf => ?_⟩
  rw [garbage_vote hg hf ht] at hn; cases hn

theorem gcRes_grant_keep {f : Fact} (h : f ∈ S.msgs) (ht : f.type = go!"grant") (j : Fin R.N)
    (hd : f.dst = nameOf (nodeId j)) (hle : S.currentTerm[j.val]! ≤ f.term) : f ∈ (gcRes S g o).msgs := by
  refine lset_minus_mem.mpr ⟨h, fun hf => ?_⟩
  have := garbage_grant hc hg hf ht j hd
  have := effTerm_le S j.val
  omega

theorem gcRes_ack_keep {src : Str} {t k : Int} (j : Fin R.N) (h : AckIn S src (nameOf (nodeId j)) t k)
    (hle : S.currentTerm[j.val]! ≤ t) : AckIn (gcRes S g o) src (nameOf (nodeId j)) t k := by
  obtain ⟨a, ha, hP, hmax⟩ := exists_max (fun a : Fact => a.index)
    (fun a => a.type = go!"ack" ∧ a.src = src ∧ a.dst = nameOf (nodeId j) ∧ a.term = t ∧ k ≤ a.index)
    S.msgs (by obtain ⟨a, ha, h1, h2, h3, h4, h5⟩ := h; exact ⟨a, ha, h1, h2, h3, h4, h5⟩)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  refine ⟨a, lset_minus_mem.mpr ⟨ha, fun hag => ?_⟩, h1, h2, h3, h4, h5⟩
  rcases garbage_ack hc hg hag h1 j h3 with he | ⟨b, hb, hb1, hb2, hb3, hb4, hb5⟩
  · have := effTerm_le S j.val; omega
  · have := hmax b hb ⟨hb1, hb2.trans h2, hb3.trans h3, hb4.trans h4, by omega⟩
    omega

omit hg in
include ho in
theorem gcRes_votes_keep {v : VoteRec} (h : v ∈ S.votes) (j : Fin R.N) (hj : v.voter = nameOf (nodeId j))
    (hle : S.currentTerm[j.val]! ≤ v.term) : v ∈ (gcRes S g o).votes := by
  refine lset_minus_mem.mpr ⟨h, fun hv => ?_⟩
  have := oldVotes_mem hc ho hv j hj
  have := effTerm_le S j.val
  omega

end keep

/-! ## The binding's functions over what `GC` keeps -/

theorem contains_eq_of {α : Type} [DecidableEq α] {l1 l2 : List α} {x : α} (h1 : x ∈ l1 → x ∈ l2)
    (h2 : x ∈ l2 → x ∈ l1) : l1.contains x = l2.contains x := by
  cases h : l2.contains x
  · cases h' : l1.contains x
    · rfl
    · have := h1 (List.contains_iff_mem.mp h'); rw [List.contains_iff_mem.mpr this] at h; cases h
  · exact List.contains_iff_mem.mpr (h2 (List.contains_iff_mem.mp h))

theorem toAppendFact_msgOf [GooseExts] (m : Msg) (to : w64) : toAppendFact (msgOf m to) =
    .ok { src := nameOf m.src, dst := nameOf to, term := uint.Z m.term, prevLogIndex := uint.Z m.index,
          prevLogTerm := uint.Z m.logterm, entries := logOf m.entries, commit := uint.Z m.commit } := rfl

theorem voteFact_msgOf [GooseExts] (m : Msg) (to : w64) : voteFact (msgOf m to) =
    .ok { type := go!"vote", src := nameOf m.src, term := uint.Z m.term, lastLogIndex := uint.Z m.index,
          lastLogTerm := uint.Z m.logterm } := rfl

/-- `Granted(i)` reads only the configuration, `currentTerm`, `i`'s grants and its self-vote. -/
theorem granted_congr {s1 s : State} (i : Nat) (hcfg : s1.cfg = s.cfg) (hct : s1.currentTerm = s.currentTerm)
    (hm : ∀ j, s1.msgs.contains (Fact.mk go!"grant" j (s.cfg.server[i]!) (s.currentTerm[i]!) 0 0 0) =
      s.msgs.contains (Fact.mk go!"grant" j (s.cfg.server[i]!) (s.currentTerm[i]!) 0 0 0))
    (hv : s1.votes.contains (VoteRec.mk (s.cfg.server[i]!) (s.currentTerm[i]!) (s.cfg.server[i]!)) =
      s.votes.contains (VoteRec.mk (s.cfg.server[i]!) (s.currentTerm[i]!) (s.cfg.server[i]!))) :
    s1.granted i = s.granted i := by
  unfold State.granted
  rw [hcfg, hct]
  simp only [hm, hv]

theorem sendable_gc {S : State} {g : List Fact} {o : List VoteRec} {F : AppendFact}
    (hn : S.over F.term = false) : (gcRes S g o).sendable F = S.sendable F := by
  unfold State.sendable sendableIn
  have hl : (gcRes S g o).leaders.contains { server := F.src, term := F.term } =
      S.leaders.contains { server := F.src, term := F.term } :=
    contains_eq_of gcRes_leaders_sub (fun h => gcRes_leaders_keep h hn)
  rw [hl, gcRes_has hn, gcRes_get hn]; rfl

/-! ## `violated` -/

/-- **No violation** where `viol` is empty and `GlobalOk` holds: `ElectionSafety` and `OneVotePerTerm`
are raft's (`RaftLaws`). -/
theorem violated_nil [GooseExts] {S : State} {net : List Msg} {G : RaftFacts} (hv : S.viol = [])
    (hl : RaftLaws G) (hg : GlobalOk R S net G) : violated S = [] := by
  have he : S.electionSafety = true := by
    unfold State.electionSafety
    rw [List.all_eq_true]; intro a ha; rw [List.all_eq_true]; intro b hb
    obtain ⟨j, t, hjt, has, hat⟩ := hg.1 a ha
    obtain ⟨j', t', hjt', hbs, hbt⟩ := hg.1 b hb
    by_cases hab : a.term = b.term
    · have htt : t = t' := uint_Z_inj.mp (by rw [← hat, ← hbt, hab])
      have hjj : j = j' := hl.1 _ hjt _ hjt' htt
      have : a.server = b.server := by rw [has, hbs, hjj]
      simp [hab, this]
    · simp [hab]
  have ho : S.oneVotePerTerm = true := by
    unfold State.oneVotePerTerm
    rw [List.all_eq_true]; intro a ha; rw [List.all_eq_true]; intro b hb
    obtain ⟨x, t, c, hx, hav, hat, hac⟩ := hg.2.1 a ha
    obtain ⟨x', t', c', hx', hbv, hbt, hbc⟩ := hg.2.1 b hb
    by_cases hab : a.voter = b.voter ∧ a.term = b.term
    · have hxx : x = x' := nameOf_inj (by rw [← hav, ← hbv, hab.1])
      have htt : t = t' := uint_Z_inj.mp (by rw [← hat, ← hbt, hab.2])
      have hcc : c = c' := hl.2.1 _ hx _ hx' hxx htt
      have : a.cand = b.cand := by rw [hac, hbc, hcc]
      simp [hab.1, hab.2, this]
    · by_cases h1 : a.voter = b.voter
      · have h2 : ¬ a.term = b.term := fun h2 => hab ⟨h1, h2⟩
        simp [h2]
      · simp [h1]
  unfold violated
  simp [he, ho, hv]

/-! ## The relation after one `GC` step -/

section rel
variable [GooseExts]

theorem BindingOk.factsWf {dec : CCDec} {S : State} (hb : BindingOk R dec S) : FactsWf R S :=
  ⟨hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1⟩

theorem gc_rel {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg} {xnet : List XMsg}
    {G : RaftFacts} {g : List Fact}
    {o : List VoteRec} (hs : AntSim R dec S V net xnet) (hgo : GlobalOk R S net G) (hg : S.garbage = .ok g)
    (ho : S.oldVotes = .ok o) : AntSim R dec (gcRes S g o) V net xnet ∧ GlobalOk R (gcRes S g o) net G := by
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs
  have hc : S.cfg = R.cfg := hsh.1
  obtain ⟨hb1, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18,
    hb19⟩ := hb
  refine ⟨⟨hsh, ?_, ?_, hxn, ?_⟩, ?_⟩
  · -- BindingOk
    refine ⟨hb1, hb4, hb5, hb6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb15, ?_, ?_, ?_, hb19.1,
      hb19.2.1, fun f hf hty => hb19.2.2 f (gcRes_msgs_sub hf) hty⟩
    · intro n l hl
      exact hb7 n l (gcRes_get_ok hl)
    · intro n a ha
      exact hb8 n a (gcRes_msgs_sub ha)
    · intro p hp
      obtain ⟨hp1, hp2⟩ := gcRes_ledLog_sub hp
      obtain ⟨l, hl, hlt⟩ := hb9 p hp1
      exact ⟨l, gcRes_leaders_keep hl (by rw [hlt]; exact hp2), hlt⟩
    · intro n l hl
      exact hb10 n l (gcRes_leaders_sub hl)
    · intro f hf
      exact hb11 f (gcRes_msgs_sub hf)
    · intro v hv
      exact hb12 v (gcRes_votes_sub hv)
    · intro n hv
      exact gcRes_votes_keep hc ho (hb13 n hv) n rfl (Int.le_refl _)
    · intro n a ha
      exact hb14 n a (gcRes_msgs_sub ha)
    · intro j
      obtain ⟨h1, h2⟩ := hb16 j
      refine ⟨?_, h2⟩
      rcases h1 with h | h | h
      · exact .inl h
      · cases hov : S.over (S.confirmed[j.val]!).term
        · exact .inr (.inl ((gcRes_has (g := g) (o := o) hov).trans h))
        · refine .inr (.inr fun i => ?_)
          refine Int.lt_of_not_ge fun hle => ?_
          rw [over_false (S := S) (t := (S.confirmed[j.val]!).term) hc i hle] at hov; cases hov
      · exact .inr (.inr h)
    · refine ⟨fun T hT => ?_, hb17.2⟩
      rcases hb17.1 T hT with ⟨l, hl, hlt⟩ | h
      · cases hov : S.over l.term
        · exact .inl ⟨l, gcRes_leaders_keep hl hov, hlt⟩
        · refine .inr fun i => ?_
          refine Int.lt_of_not_ge fun hle => ?_
          rw [over_false (S := S) (t := l.term) hc i (by rw [hlt]; exact hle)] at hov; cases hov
      · exact .inr h
    · intro T hT
      change (S.ledLog.without S.staleLed).has T = true at hT
      rw [has_without] at hT
      cases hs : S.staleLed.contains T
      · rw [hs] at hT
        obtain ⟨l, a, cs, h1, h2, h3, h4, h5⟩ := hb18 T (by simpa using hT)
        refine ⟨l, a, cs, ?_, ?_, h3, ?_, h5⟩
        · show (S.ledLog.without S.staleLed).get T = _; rw [get_without, hs]; exact h1
        · show (S.ledAt.without S.staleLed).get T = _; rw [get_without, hs]; exact h2
        · show (S.ledConf.without S.staleLed).get T = _; rw [get_without, hs]; exact h4
      · rw [hs] at hT; cases hT
  · -- NetOk
    refine ⟨fun m hm => ?_, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2⟩
    obtain ⟨hty, hsrc, j, hdst, hj⟩ := hn.1 m hm
    refine ⟨hty, hsrc, j, hdst, fun hle => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hj hle
    have hov : S.over (uint.Z m.term) = false := over_false hc j hle
    refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
    · have := h1 ht
      rw [toAppendFact_msgOf, eok_bind] at this ⊢
      rw [sendable_gc hov]; exact this
    · obtain ⟨f, hf, hfm⟩ := h2 ht
      rw [voteFact_msgOf] at hf; cases hf
      refine ⟨_, voteFact_msgOf m m.dst, ?_⟩
      exact gcRes_vote_keep hc hg hfm rfl hov
    · exact gcRes_grant_keep hc hg (h3 ht) rfl j (by rw [hdst]) hle
    · have := h4 ht
      rw [hdst] at this ⊢
      exact gcRes_ack_keep hc hg j this hle
  · -- NodeOk
    intro n
    obtain ⟨hd, hM, hSy, hU, hQu, hR, hCL, hF, hL, hC, hP, hX, hQ, hT⟩ := hno n
    have hct : S.currentTerm[n.val]! ≤ uint.Z (V n).ps.term := by rw [hd.1]; exact hF.durTerm
    have hov : S.over (uint.Z (V n).ps.term) = false := over_false hc n hct
    refine ⟨hd, hM, hSy, hU, hQu, hR, hCL, hF, ?_, ?_, hP, hX, ?_, hT⟩
    · intro hlead
      obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := hL hlead
      refine ⟨?_, ?_, ?_, ?_, hl5⟩
      · exact List.contains_iff_mem.mpr (gcRes_leaders_keep (List.contains_iff_mem.mp hl1) hov)
      · rw [gcRes_get hov]; exact hl2
      · intro j k hk hkt
        exact gcRes_ack_keep hc hg n (hl3 j k hk hkt) hct
      · intro j hj
        rcases hl4 j hj with h | h
        · exact .inl h
        · exact .inr (gcRes_ack_keep hc hg n h hct)
    · intro hcand
      obtain ⟨hC1, hC2⟩ := hC hcand
      refine ⟨fun j hj => ?_, gcRes_vote_keep hc hg hC2 rfl (over_false hc n (Int.le_refl _))⟩
      have := hC1 j hj
      have heq : (gcRes S g o).granted n.val = S.granted n.val := by
        refine granted_congr (s1 := gcRes S g o) (s := S) n.val rfl rfl ?_ ?_
        · intro x
          refine contains_eq_of gcRes_msgs_sub (fun h => gcRes_grant_keep hc hg h rfl n
            (server_of hc n) (Int.le_refl _))
        · exact contains_eq_of gcRes_votes_sub (fun h => gcRes_votes_keep hc ho h n
            (server_of hc n) (Int.le_refl _))
      rw [heq]; exact this
    · intro q hq
      obtain ⟨q1, q2, q3, q4, q5⟩ := hQ q hq
      refine ⟨q1, q2, q3, q4, ?_⟩
      rcases q5 with ⟨h1, h0, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, h0, gcRes_ack_keep hc hg n h2 hct⟩
      · exact .inr ⟨h1, gcRes_votes_keep hc ho h2 n rfl hct⟩
  · -- GlobalOk
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hgo
    refine ⟨fun l hl => g1 l (gcRes_leaders_sub hl), fun v hv => g2 v (gcRes_votes_sub hv), g3,
      fun p hp => g4 p (gcRes_ledLog_sub hp).1, g5, g6, g7⟩

end rel

/-! ## The loop -/

/-- What `gcFuel` counts: the facts, votes and leader logs. -/
def gcM (S : State) : Nat := S.msgs.length + S.votes.length + S.ledLog.length

theorem gcDue_eq {S : State} {g : List Fact} {o : List VoteRec} (hg : S.garbage = .ok g)
    (ho : S.oldVotes = .ok o) :
    S.gcDue = .ok (decide (g.length + o.length ≥ gcBatch) || S.staleLed.length != 0) := by
  unfold State.gcDue; rw [hg, ho]; rfl

/-- A due `GC` removes something. -/
theorem gcM_lt {S : State} {g : List Fact} {o : List VoteRec} (hg : S.garbage = .ok g)
    (ho : S.oldVotes = .ok o) (hd : (decide (g.length + o.length ≥ gcBatch) || S.staleLed.length != 0) = true) :
    gcM (gcRes S g o) < gcM S := by
  have hm := lset_minus_length_le S.msgs g
  have hv := lset_minus_length_le S.votes o
  have hl : (S.ledLog.without S.staleLed).length ≤ S.ledLog.length := List.length_filter_le _ _
  have hgs : ∀ x ∈ g, x ∈ S.msgs := fun x hx => (filterM_mem (by unfold State.garbage at hg; exact hg) hx).1
  have hos : ∀ x ∈ o, x ∈ S.votes := fun x hx => (filterM_mem (by unfold State.oldVotes at ho; exact ho) hx).1
  show (lset.minus S.msgs g).length + (lset.minus S.votes o).length + (S.ledLog.without S.staleLed).length <
    S.msgs.length + S.votes.length + S.ledLog.length
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hd
  rcases hd with hd | hd
  · by_cases hg0 : g = []
    · subst hg0
      have ho0 : o ≠ [] := by intro h; subst h; simp [gcBatch] at hd
      have := lset_minus_length_lt hos ho0
      omega
    · have := lset_minus_length_lt hgs hg0
      omega
  · have hlt : (S.ledLog.without S.staleLed).length < S.ledLog.length := by
      unfold TermFn.without
      rw [List.length_filter_lt_length_iff_exists]
      have hne : S.staleLed ≠ [] := fun h => hd (by rw [h]; rfl)
      obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
      have ht0 := ht
      unfold State.staleLed at ht
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
      refine ⟨p, (List.mem_filter.mp hp).1, ?_⟩
      simp [ht0]
    omega

section rel
variable [GooseExts]

theorem gcLoop_rel {dec : CCDec} {V : Fin R.N → NodeView} {net : List Msg} {xnet : List XMsg}
    {G : RaftFacts} (hl : RaftLaws G) :
    ∀ (k : Nat) (S : State), gcM S < k → AntSim R dec S V net xnet → GlobalOk R S net G →
      ∃ S', gcLoop k S = .ok (S', none) ∧ AntSim R dec S' V net xnet ∧ GlobalOk R S' net G
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, S, hlt, hs, hgo => by
    have hc : S.cfg = R.cfg := hs.1.1
    obtain ⟨g, hg⟩ := garbage_ok hc hs.2.1.factsWf
    obtain ⟨o, ho⟩ := oldVotes_ok hc hs.2.1.factsWf
    cases hd : (decide (g.length + o.length ≥ gcBatch) || S.staleLed.length != 0)
    · refine ⟨S, ?_, hs, hgo⟩
      rw [gcLoop, gcDue_eq hg ho, hd]; rfl
    · obtain ⟨hs1, hgo1⟩ := gc_rel hs hgo hg ho
      have hv := violated_nil hs1.2.1.1 hl hgo1
      obtain ⟨S', h', hs', hgo'⟩ := gcLoop_rel hl k (gcRes S g o) (by have := gcM_lt hg ho hd; omega) hs1 hgo1
      refine ⟨S', ?_, hs', hgo'⟩
      rw [gcLoop, gcDue_eq hg ho, hd]
      simp only [eok_bind, Bool.not_true, Bool.false_eq_true, ite_false, gc_eq hg ho, hv, bne_self_eq_false]
      exact h'

end rel

/-- **`GC`** (B 713-723): the `GC` steps due end within `gcFuel`, with no violation, the relation
holding after them. -/
theorem antSim_gc [GooseExts] : antSim_gc.stmt := by
  intro R dec S V net xnet G hs hl hgo
  exact gcLoop_rel hl (gcFuel S) S (by unfold gcFuel gcM; omega) hs hgo

/-- **One more event**: the checker at `S` takes `ev` when its `GC` steps end at `S1` with no verdict,
`Step` takes `ev` there to `S2`, and `S2` breaks no invariant. -/
theorem Prefix.snoc {cfg : Config} {evs : List Event} {S S1 S2 : State} {ev : Event}
    (hp : Prefix cfg evs S) (hgc : gcLoop (gcFuel S) S = .ok (S1, none)) (hst : S1.step ev = .ok (some S2))
    (hv : violated S2 = []) : Prefix cfg (evs ++ [ev]) S2 := by
  obtain ⟨c, hc, hd, hs⟩ := hp
  subst hs
  refine ⟨{ c with state := S2 }, ?_, hd, rfl⟩
  cases h0 : init0 cfg with
  | error e => rw [h0] at hc; cases hc
  | ok s =>
    rw [h0] at hc
    change evs.foldlM (fun c ev => c.next ev) ({ state := s } : Checker) = .ok c at hc
    change (evs ++ [ev]).foldlM (fun c ev => c.next ev) ({ state := s } : Checker) = _
    have hn : c.next ev = .ok { c with state := S2 } := by
      unfold Checker.next
      simp only [hd, Bool.false_eq_true, ite_false, hgc, eok_bind, hst, hv, bne_self_eq_false]
      rfl
    rw [List.foldlM_append, hc, eok_bind, List.foldlM_cons, hn, eok_bind]
    rfl

end AntSim
end EtcdGrove
end Perennial
