/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ClosestPure.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Pure facts of `ComputeClosestPeers`' ranking (`replica/replica.go`): peer `i`'s position is the
number of peers `j` before it in the order "lower latency, then lower id" (`cp.before`); the
positions of distinct peers differ (`cp.rank_inj`) and are below `N` (`cp.rank_lt`).
-/
module

public import Init

@[expose] public section

namespace cp

/-- `j` before `i`: lower latency `v`, ties broken by the lower index. -/
def before (v : Nat → Int) (j i : Nat) : Bool :=
  decide (v j < v i) || (decide (v j = v i) && decide (j < i))

/-- `i`'s position among `0..N-1`. -/
def rank (v : Nat → Int) (N i : Nat) : Nat :=
  ((List.range N).filter (fun j => before v j i)).length

theorem before_irrefl (v : Nat → Int) (i : Nat) : before v i i = false := by
  simp [before]

theorem before_trans (v : Nat → Int) (a b c : Nat) (h1 : before v a b = true)
    (h2 : before v b c = true) : before v a c = true := by
  simp only [before, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem before_total (v : Nat → Int) (a b : Nat) (h : a ≠ b) :
    before v a b = true ∨ before v b a = true := by
  simp only [before, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem before_asymm (v : Nat → Int) (a b : Nat) (h : before v a b = true) :
    before v b a = false := by
  simp only [before, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [before, Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_false_iff_not,
    decide_eq_true_eq]
  omega

theorem filter_length_mono {α : Type} (p q : α → Bool) (l : List α)
    (himp : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have ih' := ih (fun x hx => himp x (List.mem_cons_of_mem y hx))
    have hy := himp y List.mem_cons_self
    by_cases hp : p y = true
    · simp [List.filter_cons, hp, hy hp]; omega
    · cases hq : q y <;> simp [List.filter_cons, hp, hq] <;> omega

theorem filter_length_lt {α : Type} (p q : α → Bool) (l : List α)
    (himp : ∀ x ∈ l, p x = true → q x = true) (hex : ∃ x ∈ l, q x = true ∧ p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => obtain ⟨x, hx, -⟩ := hex; simp at hx
  | cons y l ih =>
    have himp' : ∀ x ∈ l, p x = true → q x = true :=
      fun x hx => himp x (List.mem_cons_of_mem y hx)
    have hle := filter_length_mono p q l himp'
    obtain ⟨x, hx, hqx, hpx⟩ := hex
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [List.filter_cons, hqx, hpx]; omega
    · have := ih himp' ⟨x, hx, hqx, hpx⟩
      by_cases hp : p y = true
      · simp [List.filter_cons, hp, himp y List.mem_cons_self hp]; omega
      · cases hq : q y <;> simp [List.filter_cons, hp, hq] <;> omega

theorem rank_lt (v : Nat → Int) (N i : Nat) (hi : i < N) : rank v N i < N := by
  unfold rank
  have := (List.length_filter_lt_length_iff_exists (p := fun j => before v j i)
    (l := List.range N)).2 ⟨i, List.mem_range.2 hi, by simp [before_irrefl]⟩
  simpa using this

theorem rank_lt_of_before (v : Nat → Int) (N i i' : Nat) (hi : i < N)
    (h : before v i i' = true) : rank v N i < rank v N i' := by
  unfold rank
  apply filter_length_lt
  · intro x _ hx; exact before_trans v x i i' hx h
  · exact ⟨i, List.mem_range.2 hi, h, before_irrefl v i⟩

theorem rank_inj (v : Nat → Int) (N i i' : Nat) (hi : i < N) (hi' : i' < N) (hne : i ≠ i') :
    rank v N i ≠ rank v N i' := by
  rcases before_total v i i' hne with h | h
  · exact Nat.ne_of_lt (rank_lt_of_before v N i i' hi h)
  · exact Nat.ne_of_gt (rank_lt_of_before v N i' i hi' h)

/-- The ranking loop's count after `j` peers. -/
theorem rank_step (v : Nat → Int) (j i : Nat) :
    ((List.range (j + 1)).filter (fun k => before v k i)).length =
      ((List.range j).filter (fun k => before v k i)).length +
        (if before v j i then 1 else 0) := by
  rw [List.range_succ, List.filter_append]
  cases h : before v j i <;> simp [h]

theorem rank_le (v : Nat → Int) (j i : Nat) :
    ((List.range j).filter (fun k => before v k i)).length ≤ j := by
  have := List.length_filter_le (fun k => before v k i) (List.range j)
  simpa using this

theorem take_filter_succ {α : Type} (Q : List α) (k : Nat) (q : α) (f : α → Bool)
    (h : Q[k]? = some q) :
    (Q.take (k + 1)).filter f = (Q.take k).filter f ++ (if f q then [q] else []) := by
  rw [List.take_add_one, h, List.filter_append]
  cases hf : f q <;> simp [hf]

theorem take_set_succ {α : Type} (l : List α) (g : Nat) (x : α) (hg : g < l.length) :
    (l.set g x).take (g + 1) = l.take g ++ [x] := by
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl g)]
  simp [List.getElem?_set, hg]

end cp
