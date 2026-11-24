/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Kahn/Defs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Kahn networks of deterministic processes and the closure of predicted traces (stage 2, D9).

A network of `n` processes, each a deterministic partial step function over events; an event may
consume a message sent to the process (`recv`); a step's outputs are messages to processes (self
included) and external outputs. Given each process's *predicted trace* (a finite list of events,
from its prophecy), a vector of positions `p` is *reachable* when the processes can advance, one
event at a time, each event enabled when it happens: its step is defined on the process's state,
and the message it consumes has an unconsumed copy sent to it. Reachable vectors are closed under
componentwise max (Kahn's confluence: enabling is monotone, only the receiver consumes), so the
reachable vectors of finite traces have a greatest element, the closure `close T`. Reality (the
events the processes actually took, each enabled when taken) is always reachable, hence below the
closure, and strictly below it at a process whose next predicted event is enabled.

Every reachable vector is the projection of a run of the global transition system (`GRun`), and
between two reachable vectors `p ≤ q` there is a run through `p` to `q`: the protocol's pure
theorems are stated over global runs and instantiated with these.
-/
module

public import Perennial.Std.Word

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.kahn

/-- A process's output: a message to process `dst`, or an external output (a reply to a client). -/
inductive Out (n : Nat) (M X : Type) where
  | send (dst : Fin n) (m : M)
  | ext (x : X)

/-- A network of `n` deterministic processes. -/
structure Net where
  n : Nat
  /-- a process's state -/
  S : Type
  /-- an event (its full content) -/
  E : Type
  /-- a message's content -/
  M : Type
  /-- an external output -/
  X : Type
  [decM : DecidableEq M]
  init : Fin n → S
  /-- process `i`'s step: `none` when the event is not enabled in the state -/
  step : Fin n → S → E → Option (S × List (Out n M X))
  /-- the message an event consumes (`none`: a free event: a timer, a client request, ...) -/
  recv : E → Option M

attribute [instance] Net.decM

variable (N : Net)

/-- Run process `i` from state `s` over events `es`: the final state and the outputs, in order. -/
def runFrom (i : Fin N.n) : N.S → List N.E → Option (N.S × List (Out N.n N.M N.X))
  | s, [] => some (s, [])
  | s, e :: es => match N.step i s e with
    | none => none
    | some (s', o) => (runFrom i s' es).map (fun r => (r.1, o ++ r.2))

/-- Process `i`'s state and outputs after the events `es` from its initial state. -/
def runP (i : Fin N.n) (es : List N.E) : Option (N.S × List (Out N.n N.M N.X)) :=
  runFrom N i (N.init i) es

/-- The messages process `i` consumed in `es`. -/
def recvd (es : List N.E) : List N.M := es.filterMap N.recv

/-- The messages to `j` among outputs `o`. -/
def sentTo (j : Fin N.n) (o : List (Out N.n N.M N.X)) : List N.M :=
  o.filterMap (fun x => match x with | .send d m => if d = j then some m else none | .ext _ => none)

/-- Predicted traces, one per process. -/
abbrev Traces := Fin N.n → List N.E

/-- A vector of positions. -/
abbrev Pos := Fin N.n → Nat

variable {N}

/-- The outputs of process `i` within its first `k` predicted events (empty if undefined). -/
def outsAt (T : Traces N) (i : Fin N.n) (k : Nat) : List (Out N.n N.M N.X) :=
  ((runP N i ((T i).take k)).map Prod.snd).getD []

/-- How many copies of `m` were sent to `j` within the positions `p`. -/
def sentCount (T : Traces N) (p : Pos N) (j : Fin N.n) (m : N.M) : Nat :=
  (List.finRange N.n).foldr (fun i acc => (sentTo N j (outsAt T i (p i))).count m + acc) 0

/-- Process `i`'s next predicted event at `p` is enabled: it exists, the step is defined on the
process's state, and the message it consumes (if any) has an unconsumed copy sent to `i`. -/
def Enabled (T : Traces N) (p : Pos N) (i : Fin N.n) : Prop :=
  ∃ e, (T i)[p i]? = some e ∧
    ∃ s o, runP N i ((T i).take (p i)) = some (s, o) ∧ (N.step i s e).isSome ∧
      ∀ m, N.recv e = some m → (recvd N ((T i).take (p i + 1))).count m ≤ sentCount T p i m

/-- Advance process `i` by one event. -/
def bump (p : Pos N) (i : Fin N.n) : Pos N := fun j => if j = i then p j + 1 else p j

/-- The reachable position vectors of predicted traces `T`. -/
inductive Reach (T : Traces N) : Pos N → Prop where
  | zero : Reach T (fun _ => 0)
  | step {p : Pos N} {i : Fin N.n} : Reach T p → Enabled T p i → Reach T (bump p i)

/-- Componentwise order and max of positions. -/
def PosLe (p q : Pos N) : Prop := ∀ i, p i ≤ q i
def PosMax (p q : Pos N) : Pos N := fun i => max (p i) (q i)

/-! ### Proof helpers (unit K): runs of one process, sums over processes, monotone enabling -/

theorem runFrom_single (i : Fin N.n) (s : N.S) (e : N.E) :
    runFrom N i s [e] = N.step i s e := by
  simp only [runFrom]
  cases N.step i s e with
  | none => rfl
  | some r => simp

theorem runFrom_append_some {i : Fin N.n} {s s1 : N.S} {o1 : List (Out N.n N.M N.X)}
    {a : List N.E} (b : List N.E) (h : runFrom N i s a = some (s1, o1)) :
    runFrom N i s (a ++ b) = (runFrom N i s1 b).map (fun r => (r.1, o1 ++ r.2)) := by
  induction a generalizing s o1 with
  | nil =>
    simp only [runFrom, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hb : runFrom N i s b <;> simp [hb]
  | cons e a ih =>
    simp only [List.cons_append, runFrom] at h ⊢
    cases hs : N.step i s e with
    | none => simp [hs] at h
    | some r =>
      obtain ⟨s', o⟩ := r
      simp only [hs] at h ⊢
      cases ha : runFrom N i s' a with
      | none => simp [ha] at h
      | some r2 =>
        obtain ⟨s2, o2⟩ := r2
        simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih ha]
        cases runFrom N i s2 b <;> simp

theorem runFrom_append_inv {i : Fin N.n} {s s2 : N.S} {o : List (Out N.n N.M N.X)}
    {a b : List N.E} (h : runFrom N i s (a ++ b) = some (s2, o)) :
    ∃ s1 o1 o2, runFrom N i s a = some (s1, o1) ∧ runFrom N i s1 b = some (s2, o2) ∧
      o = o1 ++ o2 := by
  induction a generalizing s o with
  | nil => exact ⟨s, [], o, rfl, by simpa using h, rfl⟩
  | cons e a ih =>
    simp only [List.cons_append, runFrom] at h ⊢
    cases hs : N.step i s e with
    | none => simp [hs] at h
    | some r =>
      obtain ⟨s', o'⟩ := r
      simp only [hs] at h ⊢
      cases ha : runFrom N i s' (a ++ b) with
      | none => simp [ha] at h
      | some r2 =>
        obtain ⟨s3, o3⟩ := r2
        simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨s1, o1, o2, h1, h2, rfl⟩ := ih ha
        exact ⟨s1, o' ++ o1, o2, by simp [h1], h2, by simp⟩

theorem take_succ_of_getElem? {α : Type} {l : List α} {k : Nat} {e : α} (h : l[k]? = some e) :
    l.take (k + 1) = l.take k ++ [e] := by
  rw [List.take_add_one, h]; rfl

/-- Sums over a list of processes, in `sentCount`'s shape. -/
theorem foldr_mono {ι : Type} (l : List ι) (f g : ι → Nat) (h : ∀ i ∈ l, f i ≤ g i) :
    l.foldr (fun i acc => f i + acc) 0 ≤ l.foldr (fun i acc => g i + acc) 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    have := h a (by simp); have := ih (fun i hi => h i (by simp [hi])); omega

theorem foldr_lt {ι : Type} (l : List ι) (f g : ι → Nat) (h : ∀ i ∈ l, f i ≤ g i)
    (hl : ∃ i ∈ l, f i < g i) :
    l.foldr (fun i acc => f i + acc) 0 < l.foldr (fun i acc => g i + acc) 0 := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    simp only [List.foldr_cons]
    have ha := h a (by simp)
    have hm := foldr_mono l f g (fun i hi => h i (by simp [hi]))
    obtain ⟨i, hi, hlt⟩ := hl
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · omega
    · have := ih (fun i hi => h i (by simp [hi])) ⟨i, hi, hlt⟩; omega

theorem foldr_update {ι : Type} [DecidableEq ι] (l : List ι) (hl : l.Nodup) (f g : ι → Nat)
    (i : ι) (d : Nat) (hg : ∀ k, k ≠ i → g k = f k) (hi : g i = f i + d) :
    l.foldr (fun k acc => g k + acc) 0 =
      l.foldr (fun k acc => f k + acc) 0 + (if i ∈ l then d else 0) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rw [List.nodup_cons] at hl
    rw [ih hl.2]
    by_cases ha : a = i
    · subst ha
      simp [hl.1, hi]; omega
    · rw [hg a ha]
      by_cases hil : i ∈ l
      · simp [hil]; omega
      · have : ¬ (i = a ∨ i ∈ l) := by
          rintro (h | h)
          · exact ha h.symm
          · exact hil h
        simp [hil, Ne.symm ha]

/-- A reachable vector's prefixes run. -/
theorem reach_runP {T : Traces N} {r : Pos N} (h : Reach T r) :
    ∀ j, ∃ s o, runP N j ((T j).take (r j)) = some (s, o) := by
  induction h with
  | zero => intro j; exact ⟨N.init j, [], by simp [runP, runFrom]⟩
  | @step r i _ he ih =>
    intro j
    by_cases hj : j = i
    · subst hj
      obtain ⟨e, he1, s, o, hs, hse, _⟩ := he
      obtain ⟨⟨s', o'⟩, hso⟩ := Option.isSome_iff_exists.mp hse
      refine ⟨s', o ++ o', ?_⟩
      rw [show bump r j j = r j + 1 by simp [bump]]
      rw [take_succ_of_getElem? he1, runP, runFrom_append_some _ hs, runFrom_single, hso]
      rfl
    · simp only [bump, hj, ↓reduceIte]; exact ih j

theorem outsAt_prefix {T : Traces N} {j : Fin N.n} {k k' : Nat} (hk : k ≤ k')
    (h : ∃ s o, runP N j ((T j).take k') = some (s, o)) :
    ∃ o2, outsAt T j k' = outsAt T j k ++ o2 := by
  obtain ⟨s, o, h⟩ := h
  have he : (T j).take k' = (T j).take k ++ ((T j).take k').drop k := by
    conv => lhs; rw [← List.take_append_drop k ((T j).take k')]
    rw [List.take_take, Nat.min_eq_left hk]
  have h' := h
  rw [runP, he] at h'
  obtain ⟨s1, o1, o2, h1, _, rfl⟩ := runFrom_append_inv h'
  refine ⟨o2, ?_⟩
  simp only [outsAt, runP] at h h1 ⊢
  rw [h, h1]; rfl

theorem sentCount_mono {T : Traces N} {r r' : Pos N} (hle : PosLe r r')
    (h : ∀ j, ∃ s o, runP N j ((T j).take (r' j)) = some (s, o)) (i : Fin N.n) (m : N.M) :
    sentCount T r i m ≤ sentCount T r' i m := by
  unfold sentCount
  apply foldr_mono
  intro k _
  obtain ⟨o2, ho⟩ := outsAt_prefix (hle k) (h k)
  rw [ho]
  simp only [sentTo, List.filterMap_append, List.count_append]
  omega

/-- Enabling only grows with the other processes' progress. -/
theorem enabled_mono {T : Traces N} {r r' : Pos N} {i : Fin N.n} (he : Enabled T r i)
    (hle : PosLe r r') (hi : r' i = r i)
    (h : ∀ j, ∃ s o, runP N j ((T j).take (r' j)) = some (s, o)) : Enabled T r' i := by
  obtain ⟨e, he1, s, o, hs, hse, hm⟩ := he
  refine ⟨e, hi ▸ he1, s, o, hi ▸ hs, hse, fun m hrm => ?_⟩
  rw [hi]
  exact Nat.le_trans (hm m hrm) (sentCount_mono hle h i m)

/-- Kahn's confluence: reachable vectors are closed under max. -/
theorem reach_max {T : Traces N} {p q : Pos N} : Reach T p → Reach T q → Reach T (PosMax p q) := by
  intro hp hq
  induction hq with
  | zero =>
    have : PosMax p (fun _ => 0) = p := funext fun i => by simp [PosMax]
    rw [this]; exact hp
  | @step q i _ he ih =>
    by_cases h : q i < p i
    · have : PosMax p (bump q i) = PosMax p q := funext fun j => by
        simp only [PosMax, bump]; split <;> subst_vars <;> omega
      rw [this]; exact ih
    · have : PosMax p (bump q i) = bump (PosMax p q) i := funext fun j => by
        simp only [PosMax, bump]; split <;> subst_vars <;> omega
      rw [this]
      refine Reach.step ih (enabled_mono he (fun j => Nat.le_max_right _ _) ?_ (reach_runP ih))
      simp only [PosMax]; omega

/-- A reachable vector stays within the traces. -/
theorem reach_le_length {T : Traces N} {p : Pos N} : Reach T p → ∀ i, p i ≤ (T i).length := by
  intro h
  induction h with
  | zero => intro i; exact Nat.zero_le _
  | @step p i _ he ih =>
    intro j
    obtain ⟨e, he1, _⟩ := he
    have := (List.getElem?_eq_some_iff.mp he1).1
    simp only [bump]; split
    · subst_vars; omega
    · exact ih j

/-- The sum of a vector's positions. -/
def sumPos (p : Pos N) : Nat := (List.finRange N.n).foldr (fun i acc => p i + acc) 0

/-- The reachable vectors have a greatest element. -/
theorem exists_close (T : Traces N) : ∃ c, Reach T c ∧ ∀ p, Reach T p → PosLe p c := by
  apply Classical.byContradiction
  intro hne
  have H : ∀ c, Reach T c → ∃ p, Reach T p ∧ ∃ i, c i < p i := by
    intro c hc
    apply Classical.byContradiction
    intro h'
    exact hne ⟨c, hc, fun p hp i => Nat.le_of_not_lt fun hlt => h' ⟨p, hp, i, hlt⟩⟩
  have key : ∀ k, ∃ p, Reach T p ∧ k ≤ sumPos p := by
    intro k
    induction k with
    | zero => exact ⟨_, Reach.zero, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨p, hp, hk⟩ := ih
      obtain ⟨q, hq, i, hi⟩ := H p hp
      refine ⟨PosMax p q, reach_max hp hq, ?_⟩
      have : sumPos p < sumPos (PosMax p q) :=
        foldr_lt _ _ _ (fun j _ => Nat.le_max_left _ _)
          ⟨i, List.mem_finRange i, by simp only [PosMax]; omega⟩
      omega
  obtain ⟨p, hp, hk⟩ := key (sumPos (fun i => (T i).length) + 1)
  have := foldr_mono (List.finRange N.n) p (fun i => (T i).length)
    (fun i _ => reach_le_length hp i)
  exact Nat.not_succ_le_self _ (Nat.le_trans hk this)

/-- The closure of the predicted traces: the greatest reachable vector. -/
noncomputable def close (T : Traces N) : Pos N := Classical.choose (exists_close T)

theorem close_reach (T : Traces N) : Reach T (close T) :=
  (Classical.choose_spec (exists_close T)).1

theorem close_ge {T : Traces N} {p : Pos N} (h : Reach T p) : PosLe p (close T) :=
  (Classical.choose_spec (exists_close T)).2 p h

/-- A process whose next predicted event is enabled at a reachable vector is strictly below the
closure there. -/
theorem close_next {T : Traces N} {p : Pos N} {i : Fin N.n} (h : Reach T p) (he : Enabled T p i) :
    p i < close T i := by
  have := close_ge (Reach.step h he) i
  simp only [bump, ↓reduceIte] at this
  omega

/-! ## Global runs -/

/-- A global configuration: each process's state and the messages in flight to it. -/
structure Cfg (N : Net) where
  st : Fin N.n → N.S
  inflight : Fin N.n → List N.M

/-- The initial configuration. -/
def Cfg.init (N : Net) : Cfg N := ⟨N.init, fun _ => []⟩

/-- Remove one copy of the consumed message, if any. -/
def consume {M : Type} [DecidableEq M] : Option M → List M → List M
  | some m, l => l.erase m
  | none, l => l

/-- A global step: process `i` takes event `e`, consuming one copy of its message; its outputs'
messages join the receivers' in-flight lists; `x` are its external outputs. -/
def GStep (c : Cfg N) (i : Fin N.n) (e : N.E) (c' : Cfg N) (x : List N.X) : Prop :=
  ∃ s' o, N.step i (c.st i) e = some (s', o) ∧
    (∀ m, N.recv e = some m → m ∈ c.inflight i) ∧
    x = o.filterMap (fun y => match y with | .ext x => some x | .send _ _ => none) ∧
    c'.st = (fun j => if j = i then s' else c.st j) ∧
    c'.inflight = (fun j =>
      (if j = i then consume (N.recv e) (c.inflight j) else c.inflight j) ++ sentTo N j o)

/-- A run: its labels `(i, e)` from configuration `c` to `c'`. -/
inductive GRun : Cfg N → List (Fin N.n × N.E) → Cfg N → Prop where
  | nil (c : Cfg N) : GRun c [] c
  | cons {c c1 c' : Cfg N} {i : Fin N.n} {e : N.E} {x : List N.X} {l : List (Fin N.n × N.E)} :
      GStep c i e c1 x → GRun c1 l c' → GRun c ((i, e) :: l) c'

/-- Process `i`'s events in a run's labels. -/
def proj (l : List (Fin N.n × N.E)) (i : Fin N.n) : List N.E :=
  (l.filter (fun x => decide (x.1 = i))).map Prod.snd

/-! ### Proof helpers (unit K): global runs -/

theorem grun_append {c c1 c2 : Cfg N} {l1 l2 : List (Fin N.n × N.E)}
    (h1 : GRun c l1 c1) (h2 : GRun c1 l2 c2) : GRun c (l1 ++ l2) c2 := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact GRun.cons hs (ih h2)

theorem proj_nil (i : Fin N.n) : proj ([] : List (Fin N.n × N.E)) i = [] := rfl

theorem proj_cons (j : Fin N.n) (e : N.E) (l : List (Fin N.n × N.E)) (i : Fin N.n) :
    proj ((j, e) :: l) i = if j = i then e :: proj l i else proj l i := by
  simp only [proj, List.filter_cons]
  by_cases h : j = i <;> simp [h]

theorem proj_append (a b : List (Fin N.n × N.E)) (i : Fin N.n) :
    proj (a ++ b) i = proj a i ++ proj b i := by
  simp [proj, List.filter_append]

/-- A run's end state, from any configuration. -/
theorem grun_state_gen {c c' : Cfg N} {l : List (Fin N.n × N.E)} (h : GRun c l c') :
    ∀ i, ∃ o, runFrom N i (c.st i) (proj l i) = some (c'.st i, o) := by
  induction h with
  | nil c => intro i; exact ⟨[], by simp [proj_nil, runFrom]⟩
  | @cons c c1 c' j e x l hs _ ih =>
    intro i
    obtain ⟨s', o, hstep, _, _, hst, _⟩ := hs
    rw [proj_cons]
    by_cases hj : j = i
    · subst hj
      simp only [↓reduceIte]
      obtain ⟨o2, h2⟩ := ih j
      have : c1.st j = s' := by rw [hst]; simp
      refine ⟨o ++ o2, ?_⟩
      simp only [runFrom, hstep]
      rw [← this, h2]; rfl
    · simp only [hj, ↓reduceIte]
      have : c1.st i = c.st i := by rw [hst]; simp [Ne.symm hj]
      rw [← this]; exact ih i

/-- Process `k`'s outputs over `es` from `s` (empty if undefined). -/
def outsF (k : Fin N.n) (s : N.S) (es : List N.E) : List (Out N.n N.M N.X) :=
  ((runFrom N k s es).map Prod.snd).getD []

theorem foldr_zero {ι : Type} (l : List ι) : l.foldr (fun (_ : ι) acc => 0 + acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih]

/-- Message accounting along a run: in flight plus consumed equals initially in flight plus
sent. -/
theorem grun_inflight {c c' : Cfg N} {l : List (Fin N.n × N.E)} (h : GRun c l c')
    (j : Fin N.n) (m : N.M) :
    (c'.inflight j).count m + (recvd N (proj l j)).count m =
      (c.inflight j).count m + (List.finRange N.n).foldr
        (fun k acc => (sentTo N j (outsF k (c.st k) (proj l k))).count m + acc) 0 := by
  induction h generalizing j with
  | nil c =>
    have : ∀ k, (sentTo N j (outsF k (c.st k) (proj [] k))).count m = 0 := by
      intro k; simp [outsF, proj_nil, runFrom, sentTo]
    simp only [this, foldr_zero]
    simp [proj_nil, recvd]
  | @cons c c1 c' i e x l hs hrun ih =>
    have ih' := ih j
    obtain ⟨s', o, hstep, hmem, _, hst, hinf⟩ := hs
    obtain ⟨o', ho'⟩ := grun_state_gen hrun i
    have hc1i : c1.st i = s' := by rw [hst]; simp
    rw [hc1i] at ho'
    have hsum := foldr_update (List.finRange N.n) (List.nodup_finRange N.n)
      (fun k => (sentTo N j (outsF k (c1.st k) (proj l k))).count m)
      (fun k => (sentTo N j (outsF k (c.st k) (proj ((i, e) :: l) k))).count m)
      i ((sentTo N j o).count m)
      (by
        intro k hk
        rw [proj_cons]; simp only [Ne.symm hk, ↓reduceIte]
        have : c1.st k = c.st k := by rw [hst]; simp [hk]
        rw [this])
      (by
        rw [proj_cons]; simp only [↓reduceIte]; rw [hc1i]
        have : outsF i (c.st i) (e :: proj l i) = o ++ o' := by
          simp only [outsF, runFrom, hstep, ho']; rfl
        have h2 : outsF i s' (proj l i) = o' := by simp only [outsF, ho']; rfl
        rw [this, h2]
        simp only [sentTo, List.filterMap_append, List.count_append]
        omega)
    simp only [List.mem_finRange, ↓reduceIte] at hsum
    rw [hsum]
    rw [hinf] at ih'
    simp only [List.count_append] at ih'
    rw [proj_cons]
    by_cases hj : i = j
    · subst hj
      simp only [↓reduceIte] at ih' ⊢
      cases hr : N.recv e with
      | none =>
        simp only [hr, consume] at ih'
        have : recvd N (e :: proj l i) = recvd N (proj l i) := by
          simp [recvd, hr]
        rw [this]; omega
      | some m' =>
        have hm' := hmem m' hr
        simp only [hr, consume, List.count_erase] at ih'
        have : recvd N (e :: proj l i) = m' :: recvd N (proj l i) := by
          simp [recvd, hr]
        rw [this, List.count_cons]
        by_cases hmm : m' = m
        · subst hmm
          have := List.count_pos_iff.mpr hm'
          simp only [beq_self_eq_true, ↓reduceIte] at ih' ⊢
          omega
        · have : (m' == m) = false := by simp [hmm]
          simp only [this] at ih' ⊢
          simp only [Bool.false_eq_true, ↓reduceIte] at ih' ⊢
          omega
    · simp only [hj, ↓reduceIte, Ne.symm hj] at ih' ⊢
      omega

/-- From the initial configuration, along a run whose projections are the traces' prefixes. -/
theorem grun_inflight_init {T : Traces N} {r : Pos N} {l : List (Fin N.n × N.E)} {c : Cfg N}
    (h : GRun (Cfg.init N) l c) (hl : ∀ j, proj l j = (T j).take (r j)) (j : Fin N.n)
    (m : N.M) :
    (c.inflight j).count m + (recvd N ((T j).take (r j))).count m = sentCount T r j m := by
  have hi := grun_inflight h j m
  rw [hl j] at hi
  have e2 : (List.finRange N.n).foldr (fun k acc =>
      (sentTo N j (outsF k ((Cfg.init N).st k) (proj l k))).count m + acc) 0 =
      sentCount T r j m := by
    unfold sentCount
    congr
    funext k acc
    rw [hl k]; rfl
  rw [e2] at hi
  simpa [Cfg.init] using hi

/-- An enabled event extends a run that is at the enabling vector. -/
theorem run_step {T : Traces N} {r : Pos N} {i : Fin N.n} {l : List (Fin N.n × N.E)}
    {c : Cfg N} (h : GRun (Cfg.init N) l c) (hl : ∀ j, proj l j = (T j).take (r j))
    (he : Enabled T r i) :
    ∃ e c', GRun c [(i, e)] c' ∧ ∀ j, proj (l ++ [(i, e)]) j = (T j).take (bump r i j) := by
  obtain ⟨e, he1, s, o, hs, hse, hm⟩ := he
  obtain ⟨⟨s', o'⟩, hso⟩ := Option.isSome_iff_exists.mp hse
  obtain ⟨o0, hst⟩ := grun_state_gen h i
  rw [hl i] at hst
  have hsc : c.st i = s := by
    have : runP N i ((T i).take (r i)) = some (c.st i, o0) := hst
    rw [hs] at this
    cases this; rfl
  refine ⟨e, ⟨fun j => if j = i then s' else c.st j, fun j =>
    (if j = i then consume (N.recv e) (c.inflight j) else c.inflight j) ++ sentTo N j o'⟩,
    GRun.cons (x := o'.filterMap (fun y => match y with | .ext x => some x | .send _ _ => none))
      ⟨s', o', hsc ▸ hso, ?_, rfl, rfl, rfl⟩ (GRun.nil _), ?_⟩
  · intro m hrm
    have h1 := hm m hrm
    rw [take_succ_of_getElem? he1] at h1
    have hr1 : recvd N ((T i).take (r i) ++ [e]) = recvd N ((T i).take (r i)) ++ [m] := by
      simp [recvd, List.filterMap_append, hrm]
    rw [hr1, List.count_append] at h1
    have hinv := grun_inflight_init h hl i m
    have : 0 < (c.inflight i).count m := by simp at h1; omega
    exact List.count_pos_iff.mp this
  · intro j
    rw [proj_append, hl j]
    by_cases hj : j = i
    · subst hj
      simp only [bump, ↓reduceIte, take_succ_of_getElem? he1, proj_cons, proj_nil]
    · simp only [bump, hj, ↓reduceIte, proj_cons, proj_nil, Ne.symm hj, List.append_nil]

/-- The general extension: a run at `p` extends to `max p r` for any reachable `r`. -/
theorem reach_extend_gen {T : Traces N} {r : Pos N} (hr : Reach T r) :
    ∀ {p : Pos N} {l1 : List (Fin N.n × N.E)} {c1 : Cfg N}, GRun (Cfg.init N) l1 c1 →
      (∀ i, proj l1 i = (T i).take (p i)) →
      ∃ l2 c2, GRun c1 l2 c2 ∧ ∀ i, proj (l1 ++ l2) i = (T i).take (PosMax p r i) := by
  induction hr with
  | zero =>
    intro p l1 c1 _ hp1
    refine ⟨[], c1, GRun.nil _, fun i => ?_⟩
    simp [hp1 i, PosMax]
  | @step r i _ he ih =>
    intro p l1 c1 h1 hp1
    obtain ⟨l2, c2, h2, hl2⟩ := ih h1 hp1
    by_cases hlt : r i < p i
    · refine ⟨l2, c2, h2, fun j => ?_⟩
      rw [hl2 j]
      congr 1
      simp only [PosMax, bump]; split <;> subst_vars <;> omega
    · have h12 := grun_append h1 h2
      have hrun : ∀ j, ∃ s o, runP N j ((T j).take (PosMax p r j)) = some (s, o) := by
        intro j
        obtain ⟨o, ho⟩ := grun_state_gen h12 j
        rw [hl2 j] at ho
        exact ⟨_, _, ho⟩
      have he' : Enabled T (PosMax p r) i :=
        enabled_mono he (fun j => Nat.le_max_right _ _) (by simp only [PosMax]; omega) hrun
      obtain ⟨e, c3, h3, hl3⟩ := run_step h12 hl2 he'
      refine ⟨l2 ++ [(i, e)], c3, grun_append h2 h3, fun j => ?_⟩
      rw [← List.append_assoc, hl3 j]
      congr 1
      simp only [PosMax, bump]; split <;> subst_vars <;> omega

/-- Between two reachable vectors `p ≤ q`: a run from the initial configuration through `p` (its
projections are the traces' first `p i` events) to `q`. -/
theorem reach_run {T : Traces N} {p q : Pos N} (hp : Reach T p) (hq : Reach T q)
    (hpq : PosLe p q) :
    ∃ l1 l2 c1 c2, GRun (Cfg.init N) l1 c1 ∧ GRun c1 l2 c2 ∧
      (∀ i, proj l1 i = (T i).take (p i)) ∧ (∀ i, proj (l1 ++ l2) i = (T i).take (q i)) := by
  have hpq' : ∀ {a b : Pos N}, PosLe a b → PosMax a b = b :=
    fun hab => funext fun i => Nat.max_eq_right (hab i)
  obtain ⟨l1, c1, h1, hl1⟩ := reach_extend_gen hp (p := fun _ => 0) (GRun.nil (Cfg.init N))
    (fun i => by simp [proj_nil])
  simp only [List.nil_append] at hl1
  have hl1' : ∀ i, proj l1 i = (T i).take (p i) := fun i => by
    rw [hl1 i, hpq' (fun _ => Nat.zero_le _)]
  obtain ⟨l2, c2, h2, hl2⟩ := reach_extend_gen hq h1 hl1'
  exact ⟨l1, l2, c1, c2, h1, h2, hl1', fun i => by rw [hl2 i, hpq' hpq]⟩

/-- **Extending a given run** (stage 2, the Iris layer: reality's history `l1` is kept in its real
order, so the continuation must start from it, not from `reach_run`'s interleaving): from a run
`l1` whose projections are the traces' first `p i` events, to a reachable `q ≥ p`, there is a
continuation `l2` whose run ends with the projections `(T i).take (q i)`. -/
theorem reach_extend {T : Traces N} {p q : Pos N} {l1 : List (Fin N.n × N.E)} {c1 : Cfg N}
    (h1 : GRun (Cfg.init N) l1 c1) (hp1 : ∀ i, proj l1 i = (T i).take (p i))
    (hq : Reach T q) (hpq : PosLe p q) :
    ∃ l2 c2, GRun c1 l2 c2 ∧ ∀ i, proj (l1 ++ l2) i = (T i).take (q i) := by
  obtain ⟨l2, c2, h2, hl2⟩ := reach_extend_gen hq h1 hp1
  have : PosMax p q = q := funext fun i => Nat.max_eq_right (hpq i)
  exact ⟨l2, c2, h2, fun i => by rw [hl2 i, this]⟩

/-- A run's configuration holds each process's state after its projection. -/
theorem grun_state {l : List (Fin N.n × N.E)} {c : Cfg N} (h : GRun (Cfg.init N) l c)
    (i : Fin N.n) : ∃ o, runP N i (proj l i) = some (c.st i, o) :=
  grun_state_gen h i

/-! ## Decoding predicted traces -/

/-- A self-delimiting encoding of events as words (a prophecy's resolutions). -/
structure Codec (E : Type) where
  enc : E → List w64
  dec1 : List w64 → Option (E × List w64)
  dec_enc : ∀ e rest, dec1 (enc e ++ rest) = some (e, rest)
  dec_shorter : ∀ l e rest, dec1 l = some (e, rest) → rest.length < l.length

/-- The events a word list encodes, up to its first malformed point. -/
def Codec.decodeAll {E : Type} (C : Codec E) (l : List w64) : List E :=
  match h : C.dec1 l with
  | none => []
  | some (e, rest) =>
    have : rest.length < l.length := C.dec_shorter l e rest h
    e :: C.decodeAll rest
termination_by l.length

theorem Codec.decodeAll_enc {E : Type} (C : Codec E) (es : List E) (rest : List w64) :
    C.decodeAll ((es.map C.enc).flatten ++ rest) = es ++ C.decodeAll rest := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append]
    rw [Codec.decodeAll, ← ih]
    split
    · next h => rw [C.dec_enc] at h; cases h
    · next e' rest' h =>
      rw [C.dec_enc] at h
      cases h
      rfl

end Perennial.gryff.kahn
