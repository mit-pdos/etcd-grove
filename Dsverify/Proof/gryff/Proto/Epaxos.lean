/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/Epaxos.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

EPaxos's agreement on the RMW chain, as a pure theorem (the protocol unit's, U4).

**Setting.** Committed instances (`C`), each with its dependencies (`dep x y`: `x` depends on `y`;
for Gryff, `y`'s slot is in `x`'s deps' range for `y`'s leader). All RMWs conflict (one key), so
committed instances *interfere*: of two distinct committed instances, one depends on the other
(`Interf`, quorum intersection; U5's hub request H1 asks for this fact in the invariant).

**The executor** (`strongconnect` with G4) executes, from the instances it executed so far (`done`),
one strongly connected component `L` at a time: its members are committed and not executed, every
dependency of a member is executed or in `L` (Tarjan's search waits for every instance in the deps'
ranges to be committed and visits it), `L` is strongly connected, and `L` is sorted by a strict order
(G4: `(seq, leader, slot)`) (`StepOk`). A replica's executed sequence is a concatenation of such steps
(`Runs`).

**Theorem** (`runs_agree`): under interference, any two such sequences are prefix-comparable; so every
replica's executed sequence is a prefix of one sequence (the agreed chain). The heart is
`step_unique`: from the same executed set the next component is unique. The chain's entries (base,
CAS, result: `execOk`) are a function of the instances' order (`exec_prefix_of_inst_prefix`).

The Gryff instance (`gdep`, `gkeyLt`, `gInterf`, `gStepOk`) is at the end.
-/
module

public import Dsverify.Proof.gryff.Proto.Model

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.proto.epaxos

section generic
variable {α : Type} (C : α → Prop) (dep : α → α → Prop) (lt : α → α → Prop)

/-- Any two distinct committed instances interfere: one depends on the other. -/
def Interf : Prop := ∀ x y, C x → C y → x ≠ y → dep x y ∨ dep y x

/-- Reachability inside `L` along dependencies. -/
inductive ReachIn (L : List α) : α → α → Prop
  | refl (x : α) : ReachIn L x x
  | step {x y z : α} : dep x y → y ∈ L → ReachIn L y z → ReachIn L x z

/-- One step of the executor from `done`: a strongly connected component `L`, all of whose
dependencies are executed or in it, sorted by `lt`. -/
def StepOk (done L : List α) : Prop :=
  L ≠ [] ∧ (∀ x ∈ L, C x ∧ x ∉ done) ∧ (∀ x ∈ L, ∀ y, dep x y → y ∈ done ∨ y ∈ L) ∧
  (∀ x ∈ L, ∀ y ∈ L, ReachIn dep L x y) ∧ L.Pairwise lt

/-- A replica's executed sequence from `done`: a concatenation of executor steps. -/
inductive Runs : List α → List α → Prop
  | nil (done : List α) : Runs done []
  | step {done L l : List α} : StepOk C dep lt done L → Runs (done ++ L) l → Runs done (L ++ l)

variable {C dep lt}

/-- A path inside `L1` from a member of `L2`, where `L2` is closed under dependencies up to `done`
and `L1` avoids `done`, stays in `L2`. -/
theorem reachIn_closed {done L1 L2 : List α}
    (h1 : ∀ x ∈ L1, x ∉ done) (h2 : ∀ x ∈ L2, ∀ y, dep x y → y ∈ done ∨ y ∈ L2) :
    ∀ {x z : α}, ReachIn dep L1 x z → x ∈ L2 → z ∈ L2 := by
  intro x z h
  induction h with
  | refl => exact id
  | step hxy hy _ ih =>
    intro hx
    rcases h2 _ hx _ hxy with hd | h
    · exact absurd hd (h1 _ hy)
    · exact ih h

/-- Two lists strictly sorted by an irreflexive transitive relation, with the same members, are
equal. -/
theorem pairwise_eq_of_mem_iff (hirr : ∀ x, ¬ lt x x) (htr : ∀ x y z, lt x y → lt y z → lt x z) :
    ∀ {l1 l2 : List α}, l1.Pairwise lt → l2.Pairwise lt → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) (by simp)
  | a :: t1, b :: t2, p1, p2, h => by
    rw [List.pairwise_cons] at p1 p2
    have hab : a = b := by
      have ha := (h a).1 (List.mem_cons_self ..)
      have hb := (h b).2 (List.mem_cons_self ..)
      rcases List.mem_cons.1 ha with e | ha'
      · exact e
      rcases List.mem_cons.1 hb with e | hb'
      · exact e.symm
      exact absurd (htr _ _ _ (p1.1 _ hb') (p2.1 _ ha')) (hirr _)
    subst hab
    congr 1
    refine pairwise_eq_of_mem_iff hirr htr p1.2 p2.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (p1.1 _ hx) (hirr _)
      · exact e
    · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (p2.1 _ hx) (hirr _)
      · exact e

/-- **The next component is unique**: from the same executed set, two executor steps execute the
same component (in the same order). -/
theorem step_unique (hI : Interf C dep) (hirr : ∀ x, ¬ lt x x)
    (htr : ∀ x y z, lt x y → lt y z → lt x z) {done L1 L2 : List α}
    (s1 : StepOk C dep lt done L1) (s2 : StepOk C dep lt done L2) : L1 = L2 := by
  obtain ⟨ne1, mem1, cl1, sc1, so1⟩ := s1
  obtain ⟨ne2, mem2, cl2, sc2, so2⟩ := s2
  -- if they share a member, each is contained in the other
  have sub : ∀ {A B : List α}, (∀ x ∈ A, C x ∧ x ∉ done) →
      (∀ x ∈ B, ∀ y, dep x y → y ∈ done ∨ y ∈ B) → (∀ x ∈ A, ∀ y ∈ A, ReachIn dep A x y) →
      ∀ z, z ∈ A → z ∈ B → ∀ x ∈ A, x ∈ B := by
    intro A B mA cB sA z hzA hzB x hx
    exact reachIn_closed (fun x hx => (mA x hx).2) cB (sA z hzA x hx) hzB
  by_cases hshare : ∃ z, z ∈ L1 ∧ z ∈ L2
  · obtain ⟨z, h1, h2⟩ := hshare
    exact pairwise_eq_of_mem_iff hirr htr so1 so2 (fun x =>
      ⟨sub mem1 cl2 sc1 z h1 h2 x, sub mem2 cl1 sc2 z h2 h1 x⟩)
  · exfalso
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil L1 ne1
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil L2 ne2
    have hxy : x ≠ y := fun e => hshare ⟨x, hx, e ▸ hy⟩
    rcases hI x y (mem1 x hx).1 (mem2 y hy).1 hxy with d | d
    · rcases cl1 x hx y d with h | h
      · exact (mem2 y hy).2 h
      · exact hshare ⟨y, h, hy⟩
    · rcases cl2 y hy x d with h | h
      · exact (mem1 x hx).2 h
      · exact hshare ⟨x, hx, h⟩

/-- **EPaxos agreement**: two executed sequences from the same executed set are prefix-comparable. -/
theorem runs_agree (hI : Interf C dep) (hirr : ∀ x, ¬ lt x x)
    (htr : ∀ x y z, lt x y → lt y z → lt x z) {done l1 l2 : List α}
    (r1 : Runs C dep lt done l1) (r2 : Runs C dep lt done l2) : l1 <+: l2 ∨ l2 <+: l1 := by
  induction r1 generalizing l2 with
  | nil => exact Or.inl (List.nil_prefix)
  | @step d L l s1 _ ih =>
    cases r2 with
    | nil => exact Or.inr List.nil_prefix
    | step s2 r2' =>
      have := step_unique hI hirr htr s1 s2
      subst this
      rcases ih r2' with h | h
      · exact Or.inl ((List.prefix_append_right_inj L).2 h)
      · exact Or.inr ((List.prefix_append_right_inj L).2 h)

/-- The executed sequence of `Runs` from `[]` has no duplicates and avoids nothing executed:
every member is committed. -/
theorem runs_mem_committed {done l : List α} (r : Runs C dep lt done l) : ∀ x ∈ l, C x := by
  induction r with
  | nil => simp
  | step s _ ih =>
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact (s.2.1 x h).1
    · exact ih x h

/-- Runs compose: a run from `done` followed by a run from where it ends. -/
theorem runs_append {done l1 l2 : List α} (r1 : Runs C dep lt done l1)
    (r2 : Runs C dep lt (done ++ l1) l2) : Runs C dep lt done (l1 ++ l2) := by
  induction r1 with
  | nil => simpa using r2
  | @step d L l s _ ih =>
    rw [List.append_assoc]
    exact Runs.step s (ih (by simpa [List.append_assoc] using r2))

/-- One more step at the end of a run. -/
theorem runs_snoc {done l L : List α} (r : Runs C dep lt done l)
    (s : StepOk C dep lt (done ++ l) L) : Runs C dep lt done (l ++ L) :=
  runs_append r (by simpa using Runs.step s (Runs.nil _))

/-- Agreement among any family of replicas' sequences: pairwise comparable. -/
theorem runs_pairwise (hI : Interf C dep) (hirr : ∀ x, ¬ lt x x)
    (htr : ∀ x y z, lt x y → lt y z → lt x z) {ι : Type} (ex : ι → List α)
    (hr : ∀ k, Runs C dep lt [] (ex k)) (k1 k2 : ι) : ex k1 <+: ex k2 ∨ ex k2 <+: ex k1 :=
  runs_agree hI hirr htr (hr k1) (hr k2)

/-- Monotonicity in the committed set: a step (a run) over fewer committed instances is one over
more (commits are never undone, attributes never change). -/
theorem stepOk_mono {C' : α → Prop} (hC : ∀ x, C x → C' x) {done L : List α}
    (s : StepOk C dep lt done L) : StepOk C' dep lt done L :=
  ⟨s.1, fun x hx => ⟨hC _ (s.2.1 x hx).1, (s.2.1 x hx).2⟩, s.2.2.1, s.2.2.2.1, s.2.2.2.2⟩

theorem runs_mono {C' : α → Prop} (hC : ∀ x, C x → C' x) {done l : List α}
    (r : Runs C dep lt done l) : Runs C' dep lt done l := by
  induction r with
  | nil => exact Runs.nil _
  | step s _ ih => exact Runs.step (stepOk_mono hC s) ih

end generic

/-! ## The chain's entries are a function of the instances' order -/

/-- The entries of the chain whose instances are `is`, from the previous result `prev`, with each
instance's base and CAS given by `attr` (the executor's computation, G1). -/
def chainOf (attr : Int × Int → (Int × PTag) × Int × Int) :
    Option (Int × PTag) → List (Int × Int) → List ExecEntry
  | _, [] => []
  | prev, i :: is =>
    let b := (attr i).1
    let cur := match prev with
      | none => b
      | some p => if tagLt p.2 b.2 then b else p
    let res := (casStep (attr i).2.1 (attr i).2.2 cur.1, rmwTag cur.2)
    ⟨i, b, (attr i).2.1, (attr i).2.2, res⟩ :: chainOf attr (some res) is

/-- A chain satisfying `execOk` whose entries' bases and CASes are the instances' is `chainOf`
of its instances. -/
theorem execOk_eq_chainOf (attr : Int × Int → (Int × PTag) × Int × Int) :
    ∀ (prev : Option (Int × PTag)) (es : List ExecEntry), execOk prev es →
      (∀ e ∈ es, attr e.inst = (e.base, e.old, e.new)) →
      es = chainOf attr prev (es.map ExecEntry.inst)
  | _, [], _, _ => rfl
  | prev, ⟨i, b, o, n, r⟩ :: es, h, ha => by
    obtain ⟨hres, hrest⟩ := h
    have he : attr i = (b, o, n) := ha _ (List.mem_cons_self ..)
    have ih := execOk_eq_chainOf attr (some r) es hrest
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    simp only at hres
    subst hres
    simp only [List.map_cons, chainOf, he]
    exact congrArg (List.cons _) ih

theorem chainOf_prefix (attr : Int × Int → (Int × PTag) × Int × Int) :
    ∀ (prev : Option (Int × PTag)) (is1 is2 : List (Int × Int)), is1 <+: is2 →
      chainOf attr prev is1 <+: chainOf attr prev is2
  | _, [], _, _ => List.nil_prefix
  | prev, i :: is1, [], h => absurd h (by simp)
  | prev, i :: is1, j :: is2, h => by
    rw [List.cons_prefix_cons] at h
    obtain ⟨rfl, h⟩ := h
    simp only [chainOf, List.cons_prefix_cons, true_and]
    exact chainOf_prefix attr _ is1 is2 h

/-- Two `execOk` chains from no previous result, with the instances' bases and CASes, whose
instance sequences are prefix-comparable, are prefix-comparable. -/
theorem exec_prefix_of_inst_prefix (attr : Int × Int → (Int × PTag) × Int × Int)
    (es1 es2 : List ExecEntry) (h1 : execOk none es1) (h2 : execOk none es2)
    (a1 : ∀ e ∈ es1, attr e.inst = (e.base, e.old, e.new))
    (a2 : ∀ e ∈ es2, attr e.inst = (e.base, e.old, e.new))
    (hp : es1.map ExecEntry.inst <+: es2.map ExecEntry.inst) : es1 <+: es2 := by
  rw [execOk_eq_chainOf attr none es1 h1 a1, execOk_eq_chainOf attr none es2 h2 a2]
  exact chainOf_prefix attr none _ _ hp

/-! ## Gryff's instance -/

/-- Instance `x` (with deps `deps`) depends on `y`: `y`'s slot is in the deps' range of `y`'s
leader (one of the three). -/
def gdep (deps : Int × Int → List Int) (x y : Int × Int) : Prop :=
  0 ≤ y.1 ∧ y.1 < 3 ∧ 0 ≤ y.2 ∧ y.2 ≤ (deps x).getD y.1.toNat (-1)

/-- G4's order: `(seq, leader, slot)` lexicographically. -/
def gkeyLt (seq : Int × Int → Int) (x y : Int × Int) : Prop :=
  seq x < seq y ∨ (seq x = seq y ∧ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)))

theorem gkeyLt_irrefl (seq : Int × Int → Int) (x : Int × Int) : ¬ gkeyLt seq x x := by
  unfold gkeyLt; omega

theorem gkeyLt_trans (seq : Int × Int → Int) (x y z : Int × Int) :
    gkeyLt seq x y → gkeyLt seq y z → gkeyLt seq x z := by
  unfold gkeyLt; omega

/-- **The agreement theorem, Gryff's instance**: with committed instances `C` (attributes `seq`,
`deps`) that interfere, any two replicas' executed sequences (concatenations of executor steps
with G4's order) are prefix-comparable. -/
theorem gryff_runs_agree (C : Int × Int → Prop) (seq : Int × Int → Int)
    (deps : Int × Int → List Int) (hI : Interf C (gdep deps)) {l1 l2 : List (Int × Int)}
    (r1 : Runs C (gdep deps) (gkeyLt seq) [] l1) (r2 : Runs C (gdep deps) (gkeyLt seq) [] l2) :
    l1 <+: l2 ∨ l2 <+: l1 :=
  runs_agree hI (gkeyLt_irrefl seq) (gkeyLt_trans seq) r1 r2

end Perennial.gryff.proto.epaxos
