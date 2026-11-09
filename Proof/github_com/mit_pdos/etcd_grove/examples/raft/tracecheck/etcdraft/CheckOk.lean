/-
Lean-first (no Rocq counterpart).

# What `CheckTrace`'s search needs of a trace (layer C, 2026-11-09)

`CheckTrace.spec`'s premise `Trace.CheckTraceOk` (`notes/trace-validation-plan.md`, Q10): the search
of the trace meets its callees' premises. Its callees (`StepLine`, `Violated`, and below them every
action) are specified where the Lean transcription evaluates and on states whose numbers are far
from overflow, of the kinds of lines the workload logs; the Go checker panics with an `EvalError`
and recovers where TLC fails, which a triple returning a value cannot state. The premise has three
parts:

- **the lines in scope** (`Trace.LinesInScope`): outside the bootstrap, no configuration change,
  restart or snapshot (P1-P3 of `notes/trace-validation-sim.md`), a property of the trace alone;
- **the reached states bounded** (`State.SearchOk` of every `Trace.Reach` state: the actions'
  bounds `State.ActOk` and the messages' `State.MsgsOk`), what an invariant of the specification
  over every action gives of an in-scope trace whose events are bounded;
- **no evaluation error** (every result `CheckTraceRel` relates the trace to has none), which
  `Trace.RunRel` gives: the run layer B's simulation carries through every line is the search's
  (`Trace.RunRel.checkTraceRel_eq`, by determinism).

The rest is proved here: a reached state's position (`Trace.Reach.l_pos`), the states `StepLine`
expands reached (`Trace.LineReach.reach`), so `Trace.StepLineOk` of every state of the frontier
(`Trace.CheckTraceOk.stepLineOk`); the frontier's successors reached (`Trace.StepLineRel.reach`);
a violation's name never empty (`Trace.StepLineRel.violation_ne`); the relations deterministic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StepOk

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-! ## The premise -/

/-- The states of the trace specification the search of `tr` can reach: its initial state, and every
successor `TraceNext` gives of a reached state (every state `CheckTrace` and `StepLine` look at is
one: `Trace.LineReach.reach`, `Trace.StepLineRel.reach`). -/
inductive Trace.Reach (tr : Trace) : TState → Prop
  | init : Trace.Reach tr tr.initState
  | step (f : TState) (tss : List TState) (s2 : TState) :
      Trace.Reach tr f → tr.next f = .ok tss → s2 ∈ tss → Trace.Reach tr s2

/-- Every line outside the bootstrap of a kind the workload logs (`Line.InScope`: no `ChangeConf`, no
`InitState`, no `MsgSnap` sent). -/
def Trace.LinesInScope (tr : Trace) : Prop :=
  ∀ l, 1 ≤ l → l ≤ tr.len → tr.bootstrap.getD (l - 1) false = false → (tr.line l).InScope

/-- What the actions and the invariants need of a reached state of `tr`: the trace's servers, the
actions' bounds and flags (`State.ActOk`, which gives `Violated`'s, `State.ActOk.violOk`), and the
messages' (`State.MsgsOk`). -/
def State.SearchOk (tr : Trace) (st : State) : Prop :=
  st.server = tr.server ∧ st.ActOk ∧ st.MsgsOk

/-- `CheckTrace`'s premise: the search of `tr` meets its callees' premises (the file header). -/
def Trace.CheckTraceOk (tr : Trace) (invariants : Bool) : Prop :=
  tr.LinesInScope ∧ (∀ ts, tr.Reach ts → ts.s.SearchOk tr) ∧
  ∀ res, CheckTraceRel tr invariants res → res.evalError = none

/-! ## Folds -/

/-- A fold in `Except` keeps an invariant its steps keep. -/
theorem foldlM_except_inv {α β ε : Type} (P : β → Prop) (f : β → α → Except ε β) :
    ∀ (l : List α) (b c : β), (∀ a x c, x ∈ l → P a → f a x = .ok c → P c) → P b →
      l.foldlM f b = .ok c → P c
  | [], b, c, _, hb, h => by
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h; subst h; exact hb
  | x :: l, b, c, hs, hb, h => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hx : f b x with
    | error e => rw [hx] at h; cases h
    | ok b' =>
      rw [hx] at h
      exact foldlM_except_inv P f l b' c (fun a y c hy ha hf => hs a y c (List.mem_cons_of_mem _ hy) ha hf)
        (hs b x b' List.mem_cons_self hb hx) h

/-! ## Positions -/

/-- `receive`'s successors stay at the line or step past it. -/
theorem Trace.receive_l (tr : Trace) (ts : TState) (tss : List TState) (h : tr.receive ts = .ok tss) :
    ∀ s ∈ tss, s.l = ts.l ∨ s.l = ts.l + 1 := by
  unfold Trace.receive at h
  dsimp only at h
  split at h
  · cases h; simp
  · refine foldlM_except_inv (fun acc : List TState => ∀ s ∈ acc, s.l = ts.l ∨ s.l = ts.l + 1) _ _ [] tss
      ?_ (by simp) h
    intro acc m c _ hacc hf
    repeat' split at hf
    all_goals first
      | (cases hf; exact hacc)
      | (revert hf
         cases hr : ts.s.receive m with
         | error e => intro hf; simp [Bind.bind, Except.bind] at hf
         | ok succ =>
           intro hf
           simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at hf
           subst hf
           intro s hs
           rcases List.mem_append.1 hs with hs | hs
           · exact hacc s hs
           · obtain ⟨s2, -, rfl⟩ := List.mem_map.1 hs
             split <;> simp)

/-- `TraceNext`'s successors stay at the line or step past it. -/
theorem Trace.next_l (tr : Trace) (f : TState) (tss : List TState) (h : tr.next f = .ok tss) :
    ∀ s ∈ tss, s.l = f.l ∨ s.l = f.l + 1 := by
  unfold Trace.next at h
  split at h
  · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  · split at h
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; subst h; simp
    · simp only [Bind.bind, Except.bind] at h
      cases hn : tr.nonReceive f with
      | error e => rw [hn] at h; cases h
      | ok nr =>
        rw [hn] at h
        cases hr : tr.receive f with
        | error e => rw [hr] at h; cases h
        | ok rv =>
          rw [hr] at h
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
          subst h
          intro s hs
          rcases List.mem_append.1 hs with hs | hs
          · obtain ⟨s2, -, rfl⟩ := List.mem_map.1 hs; simp
          · exact tr.receive_l f rv hr s hs

/-- A reached state is at a line (`TraceInit`'s `l = 1`, and `l` never decreases). -/
theorem Trace.Reach.l_pos {tr : Trace} {ts : TState} (h : tr.Reach ts) : 1 ≤ ts.l := by
  induction h with
  | init => simp [Trace.initState]
  | step f tss s2 _ hn hs ih =>
    rcases tr.next_l f tss hn s2 hs with h | h <;> omega

/-- The states `StepLine` expands from a reached state are reached. -/
theorem Trace.LineReach.reach {tr : Trace} {ts f : TState} (hts : tr.Reach ts) (h : tr.LineReach ts f) :
    tr.Reach f := by
  induction h with
  | start => exact hts
  | step f tss s2 _ hn hs _ ih => exact .step f tss s2 ih hn hs

/-! ## The callees' premises -/

/-- `Violated`'s bounds are among the actions'. -/
theorem State.ActOk.violOk {st : State} (h : st.ActOk) : st.ViolOk := by
  obtain ⟨-, -, -, -, -, hs⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => (hs i hi).2.2.2.1⟩
  have := (hs i hi).1
  omega

/-- A reached state meets `Next`'s premises. -/
theorem Trace.CheckTraceOk.nextOk {tr : Trace} {invariants : Bool} (hok : tr.CheckTraceOk invariants)
    {f : TState} (hf : tr.Reach f) : f.NextOk tr := by
  obtain ⟨hsc, hb, -⟩ := hok
  obtain ⟨hsrv, hact, hmsg⟩ := hb f hf
  exact ⟨hf.l_pos, hsrv, hact, hmsg, fun hl hboot => hsc f.l hf.l_pos hl hboot⟩

/-- A reached state's line search meets `StepLine`'s premise. -/
theorem Trace.CheckTraceOk.stepLineOk {tr : Trace} {invariants : Bool} (hok : tr.CheckTraceOk invariants)
    {ts : TState} (hts : tr.Reach ts) : tr.StepLineOk ts invariants := by
  refine ⟨fun f hf => hok.nextOk (hf.reach hts), fun _ f tss s2 hf hn hs => ?_⟩
  exact ((hok.2.1 s2 (.step f tss s2 (hf.reach hts) hn hs)).2.1).violOk

/-! ## `StepLine`'s results -/

/-- What `StepLine`'s search keeps of its accumulators: the states past the line reached (and past it),
the states it will expand reached, a violation's name not empty. -/
def stepAccOk (tr : Trace) (l0 : Nat) (out next : List TState) (info : StepInfo) : Prop :=
  (∀ s ∈ out, tr.Reach s ∧ s.l = l0 + 1) ∧ (∀ s ∈ next, tr.Reach s) ∧
  ∀ v, info.violation = some v → v ≠ ""

theorem Trace.stepNewInfo_ne (invariants : Bool) (s2 : TState) (i i' : StepInfo)
    (h : Trace.stepNewInfo invariants s2 i = .ok i') (hi : ∀ v, i.violation = some v → v ≠ "") :
    ∀ v, i'.violation = some v → v ≠ "" := by
  cases invariants
  · rw [Trace.stepNewInfo_false] at h; cases h; exact hi
  · cases hv : s2.s.violated with
    | error e => simp [Trace.stepNewInfo, hv, Bind.bind, Except.bind] at h
    | ok r =>
      rw [Trace.stepNewInfo_true _ _ _ hv] at h
      cases h
      cases r with
      | none => exact hi
      | some w => intro v hv'; simp at hv'; subst hv'; exact State.violated_some_ne hv

/-- `stepRound`'s inner step keeps `stepAccOk` on a reached successor. -/
theorem Trace.stepInnerF_ok (tr : Trace) (l0 : Nat) (invariants : Bool)
    (acc acc' : List TState × List TState × List TState × List TState × StepInfo) (s2 : TState)
    (hs2 : tr.Reach s2) (hacc : stepAccOk tr l0 acc.1 acc.2.2.1 acc.2.2.2.2)
    (h : Trace.stepInnerF l0 invariants acc s2 = .ok acc') :
    stepAccOk tr l0 acc'.1 acc'.2.2.1 acc'.2.2.2.2 := by
  obtain ⟨o, v, n, fr, i⟩ := acc
  cases hvi : i.violation with
  | some w =>
    have : Trace.stepInnerF l0 invariants (o, v, n, fr, i) s2 = .ok (o, v, n, fr, i) := by
      simp [Trace.stepInnerF, hvi, Pure.pure, Except.pure]
    rw [this] at h; cases h; exact hacc
  | none =>
    obtain ⟨ho, hn, hi⟩ := hacc
    by_cases hl : s2.l = l0 + 1
    · cases hm : memEq o s2
      · rw [Trace.stepInnerF_new_out _ _ _ _ _ _ _ _ hvi hl hm] at h
        obtain ⟨i', hni, rfl⟩ := except_bind_pure_ok _ _ _ h
        refine ⟨fun s hs => ?_, hn, Trace.stepNewInfo_ne invariants s2 i i' hni hi⟩
        rcases List.mem_append.1 hs with hs | hs
        · exact ho s hs
        · simp at hs; subst hs; exact ⟨hs2, hl⟩
      · rw [Trace.stepInnerF_dup_out _ _ _ _ _ _ _ _ hvi hl hm] at h
        cases h; exact ⟨ho, hn, hi⟩
    · cases hm : memEq v s2
      · rw [Trace.stepInnerF_new_vis _ _ _ _ _ _ _ _ hvi hl hm] at h
        obtain ⟨i', hni, rfl⟩ := except_bind_pure_ok _ _ _ h
        refine ⟨ho, fun s hs => ?_, Trace.stepNewInfo_ne invariants s2 i i' hni hi⟩
        rcases List.mem_append.1 hs with hs | hs
        · exact hn s hs
        · simp at hs; subst hs; exact hs2
      · rw [Trace.stepInnerF_dup_vis _ _ _ _ _ _ _ _ hvi hl hm] at h
        cases h; exact ⟨ho, hn, hi⟩

/-- `stepRound`'s outer step keeps `stepAccOk` on a reached state. -/
theorem Trace.stepOuterF_ok' (tr : Trace) (l0 : Nat) (invariants : Bool)
    (acc acc' : List TState × List TState × List TState × StepInfo) (f : TState)
    (hf : tr.Reach f) (hacc : stepAccOk tr l0 acc.1 acc.2.2.1 acc.2.2.2)
    (h : tr.stepOuterF l0 invariants acc f = .ok acc') :
    stepAccOk tr l0 acc'.1 acc'.2.2.1 acc'.2.2.2 := by
  obtain ⟨o, v, n, i⟩ := acc
  cases hvi : i.violation with
  | some w =>
    have : tr.stepOuterF l0 invariants (o, v, n, i) f = .ok (o, v, n, i) := by
      simp [Trace.stepOuterF, hvi, Pure.pure, Except.pure]
    rw [this] at h; cases h; exact hacc
  | none =>
    obtain ⟨succ, hnext, r, hr, rfl⟩ := tr.stepOuterF_ok l0 invariants o v n i f acc' hvi h
    have hr' := foldlM_except_inv
      (fun a : List TState × List TState × List TState × List TState × StepInfo =>
        stepAccOk tr l0 a.1 a.2.2.1 a.2.2.2.2) _ succ _ r
      (fun a x c hx ha hc => tr.stepInnerF_ok l0 invariants a c x (.step f succ x hf hnext hx) ha hc)
      hacc hr
    obtain ⟨ho, hn, hi⟩ := hr'
    refine ⟨ho, hn, ?_⟩
    split
    · exact hi
    · exact hi

/-- `StepLoop`'s results keep `stepAccOk` from a reached frontier. -/
theorem Trace.StepLoop.acc_ok {tr : Trace} {l0 : Nat} {invariants : Bool} {fr : List TState}
    {st : List TState × List TState × StepInfo} {r : EvalM (List TState × StepInfo)}
    (h : tr.StepLoop l0 invariants fr st r) :
    (∀ f ∈ fr, tr.Reach f) → stepAccOk tr l0 st.1 [] st.2.2 →
      ∀ o i, r = .ok (o, i) → stepAccOk tr l0 o [] i := by
  induction h with
  | done st =>
    intro _ hst o i hr; cases hr; exact hst
  | error => intro _ _ o i hr; cases hr
  | violation frontier st out visited next info _ hround _ =>
    intro hfr hst o i hr
    cases hr
    rw [Trace.stepRound_eq] at hround
    have := foldlM_except_inv
      (fun a : List TState × List TState × List TState × StepInfo => stepAccOk tr l0 a.1 a.2.2.1 a.2.2.2)
      _ frontier _ _ (fun a x c hx ha hc => tr.stepOuterF_ok' l0 invariants a c x (hfr x hx) ha hc)
      ⟨hst.1, by simp, hst.2.2⟩ hround
    exact ⟨this.1, by simp, this.2.2⟩
  | round frontier st out visited next info r _ hround _ _ ih =>
    intro hfr hst o i hr
    rw [Trace.stepRound_eq] at hround
    have := foldlM_except_inv
      (fun a : List TState × List TState × List TState × StepInfo => stepAccOk tr l0 a.1 a.2.2.1 a.2.2.2)
      _ frontier _ _ (fun a x c hx ha hc => tr.stepOuterF_ok' l0 invariants a c x (hfr x hx) ha hc)
      ⟨hst.1, by simp, hst.2.2⟩ hround
    exact ih this.2.1 ⟨this.1, by simp, this.2.2⟩ o i hr

/-- The states one line's search reaches from a reached state are reached, at the next line. -/
theorem Trace.StepLineRel.reach {tr : Trace} {ts : TState} {invariants : Bool} {tss : List TState}
    {info : StepInfo} (hts : tr.Reach ts) (h : tr.StepLineRel ts invariants (.ok (tss, info))) :
    ∀ s ∈ tss, tr.Reach s ∧ s.l = ts.l + 1 :=
  (Trace.StepLoop.acc_ok h (by simpa using hts) ⟨by simp, by simp, by simp⟩ tss info rfl).1

/-- A violation's name is never empty (the Go's `""` is none). -/
theorem Trace.StepLineRel.violation_ne {tr : Trace} {ts : TState} {invariants : Bool} {tss : List TState}
    {info : StepInfo} (hts : tr.Reach ts) (h : tr.StepLineRel ts invariants (.ok (tss, info))) :
    ∀ v, info.violation = some v → v ≠ "" :=
  (Trace.StepLoop.acc_ok h (by simpa using hts) ⟨by simp, by simp, by simp⟩ tss info rfl).2.2

/-! ## `CheckLineRel`, a step at a time -/

/-- Past a violation, `checkLine` skips the rest of the frontier. -/
theorem Trace.CheckLineRel.skip_all (tr : Trace) (invariants : Bool) (acc : List TState × StepInfo)
    (h : acc.2.violation.isSome) : ∀ rest, tr.CheckLineRel invariants rest acc (.ok acc)
  | [] => .nil acc
  | ts :: rest => .skip ts rest acc _ h (Trace.CheckLineRel.skip_all tr invariants acc h rest)

/-! ## Determinism (each relation relates an input to at most one result) -/

theorem option_isSome_isNone {α : Type} {o : Option α} (h1 : o.isSome = true) (h2 : o.isNone = true) : False := by
  cases o <;> simp_all

theorem Trace.StepLoop.det {tr : Trace} {l0 : Nat} {invariants : Bool} {fr : List TState}
    {st : List TState × List TState × StepInfo} {r1 r2 : EvalM (List TState × StepInfo)}
    (h1 : tr.StepLoop l0 invariants fr st r1) (h2 : tr.StepLoop l0 invariants fr st r2) : r1 = r2 := by
  induction h1 generalizing r2 with
  | done st =>
    cases h2 with
    | done => rfl
    | error _ _ _ hne => exact absurd rfl hne
    | violation _ _ _ _ _ _ hne => exact absurd rfl hne
    | round _ _ _ _ _ _ _ hne => exact absurd rfl hne
  | error frontier st e hne hr =>
    cases h2 with
    | done => exact absurd rfl hne
    | error _ _ e2 _ hr2 => rw [hr] at hr2; cases hr2; rfl
    | violation _ _ _ _ _ _ _ hr2 => rw [hr] at hr2; cases hr2
    | round _ _ _ _ _ _ _ _ hr2 => rw [hr] at hr2; cases hr2
  | violation frontier st out visited next info hne hr hv =>
    cases h2 with
    | done => exact absurd rfl hne
    | error _ _ e2 _ hr2 => rw [hr] at hr2; cases hr2
    | violation _ _ _ _ _ _ _ hr2 => rw [hr] at hr2; cases hr2; rfl
    | round _ _ _ _ _ _ _ _ hr2 hv2 =>
      rw [hr] at hr2; cases hr2; exact (option_isSome_isNone hv hv2).elim
  | round frontier st out visited next info r hne hr hv _ ih =>
    cases h2 with
    | done => exact absurd rfl hne
    | error _ _ e2 _ hr2 => rw [hr] at hr2; cases hr2
    | violation _ _ _ _ _ _ _ hr2 hv2 =>
      rw [hr] at hr2; cases hr2; exact (option_isSome_isNone hv2 hv).elim
    | round _ _ _ _ _ _ _ _ hr2 _ h2' => rw [hr] at hr2; cases hr2; exact ih h2'

theorem Trace.CheckLineRel.det {tr : Trace} {invariants : Bool} {fr : List TState}
    {acc : List TState × StepInfo} {r1 r2 : EvalM (List TState × StepInfo)}
    (h1 : tr.CheckLineRel invariants fr acc r1) (h2 : tr.CheckLineRel invariants fr acc r2) : r1 = r2 := by
  induction h1 generalizing r2 with
  | nil acc => cases h2; rfl
  | skip ts rest acc r hv _ ih =>
    cases h2 with
    | skip _ _ _ _ _ h2' => exact ih h2'
    | error _ _ _ _ hv2 => exact (option_isSome_isNone hv hv2).elim
    | step _ _ _ _ _ _ hv2 => exact (option_isSome_isNone hv hv2).elim
  | error ts rest acc e hv hs =>
    cases h2 with
    | skip _ _ _ _ hv2 => exact (option_isSome_isNone hv2 hv).elim
    | error _ _ _ _ _ hs2 => have := Trace.StepLoop.det hs hs2; cases this; rfl
    | step _ _ _ _ _ _ _ hs2 => have := Trace.StepLoop.det hs hs2; cases this
  | step ts rest acc succ i2 r hv hs _ ih =>
    cases h2 with
    | skip _ _ _ _ hv2 => exact (option_isSome_isNone hv2 hv).elim
    | error _ _ _ _ _ hs2 => have := Trace.StepLoop.det hs hs2; cases this
    | step _ _ _ _ _ _ _ hs2 h2' => have := Trace.StepLoop.det hs hs2; cases this; exact ih h2'

theorem Trace.CheckFromRel.det {tr : Trace} {invariants : Bool} {n l : Nat} {fr : List TState}
    {r r1 r2 : Result} (h1 : tr.CheckFromRel invariants n l fr r r1) (h2 : tr.CheckFromRel invariants n l fr r r2) :
    r1 = r2 := by
  induction h1 generalizing r2 with
  | stop => cases h2; rfl
  | error n l frontier r e hc =>
    cases h2 with
    | error _ _ _ _ _ hc2 => have := hc.det hc2; cases this; rfl
    | violation _ _ _ _ _ _ _ hc2 => have := hc.det hc2; cases this
    | unmatched _ _ _ _ _ hc2 => have := hc.det hc2; cases this
    | step _ _ _ _ _ _ _ hc2 => have := hc.det hc2; cases this
  | violation n l frontier r next info v hc hv =>
    cases h2 with
    | error _ _ _ _ _ hc2 => have := hc.det hc2; cases this
    | violation _ _ _ _ _ _ _ hc2 hv2 =>
      have := hc.det hc2; cases this; rw [hv] at hv2; cases hv2; rfl
    | unmatched _ _ _ _ _ hc2 hv2 => have := hc.det hc2; cases this; rw [hv] at hv2; cases hv2
    | step _ _ _ _ _ _ _ hc2 hv2 => have := hc.det hc2; cases this; rw [hv] at hv2; cases hv2
  | unmatched n l frontier r info hc hv =>
    cases h2 with
    | error _ _ _ _ _ hc2 => have := hc.det hc2; cases this
    | violation _ _ _ _ _ _ _ hc2 hv2 => have := hc.det hc2; cases this; rw [hv] at hv2; cases hv2
    | unmatched _ _ _ _ _ hc2 => have := hc.det hc2; cases this; rfl
    | step _ _ _ _ _ _ _ hc2 _ hne => have := hc.det hc2; cases this; exact absurd rfl hne
  | step n l frontier r next info r' hc hv hne _ ih =>
    cases h2 with
    | error _ _ _ _ _ hc2 => have := hc.det hc2; cases this
    | violation _ _ _ _ _ _ _ hc2 hv2 => have := hc.det hc2; cases this; rw [hv] at hv2; cases hv2
    | unmatched _ _ _ _ _ hc2 => have := hc.det hc2; cases this; exact absurd rfl hne
    | step _ _ _ _ _ _ _ hc2 _ _ h2' => have := hc.det hc2; cases this; exact ih h2'

/-- `CheckTraceRel` relates a trace to at most one result. -/
theorem CheckTraceRel.det {tr : Trace} {invariants : Bool} {r1 r2 : Result}
    (h1 : CheckTraceRel tr invariants r1) (h2 : CheckTraceRel tr invariants r2) : r1 = r2 := by
  unfold CheckTraceRel at h1 h2
  dsimp only at h1 h2
  cases invariants
  · simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2; exact h1.det h2
  · simp only [↓reduceIte] at h1 h2
    cases hv : tr.initState.s.violated with
    | error e => rw [hv] at h1 h2; rw [h1, h2]
    | ok o =>
      cases o with
      | some v => rw [hv] at h1 h2; rw [h1, h2]
      | none => rw [hv] at h1 h2; exact h1.det h2

/-- A run through every line (what layer B's simulation carries) is the search's only result: TLC's
accepting verdict, without an evaluation error (`Trace.CheckTraceOk`'s last part). -/
theorem Trace.RunRel.checkTraceRel_eq {tr : Trace} {ts : TState} (h : tr.RunRel tr.len ts) :
    ∀ res, CheckTraceRel tr true res → res = { ok := true } := by
  intro res hres
  have hinit : tr.initState.s.violated = .ok none := h.init_ok
  have hrun := (h.from_init).2 { ok := true } (by
    rw [Nat.sub_self]
    exact Trace.CheckFromRel.stop _ _ _)
  have hacc : CheckTraceRel tr true { ok := true } := by
    unfold CheckTraceRel
    simp only [↓reduceIte]
    rw [hinit]
    exact hrun
  exact CheckTraceRel.det hres hacc

theorem Trace.RunRel.noEvalError {tr : Trace} {ts : TState} (h : tr.RunRel tr.len ts) :
    ∀ res, CheckTraceRel tr true res → res.evalError = none := by
  intro res hres
  rw [h.checkTraceRel_eq res hres]

/-! ## `CheckTrace`'s running result -/

/-- `CheckTrace`'s line counter: `l + 1` without overflow. -/
theorem w64_line_succ (l : w64) (n : Nat) (h1 : sint.Z l = n) (h2 : (n : Int) < 2 ^ 62) :
    sint.Z (l + W64 1) = (n : Int) + 1 ∧ sint.nat (l + W64 1) = n + 1 ∧ uint.nat l = n := by
  refine ⟨by word, by word, by word⟩

/-- The Go's `r.Branched` once a line's states so far have branched (`c`): the line `l` if no
earlier line branched (`b = 0`). -/
def brOf (c : Bool) (b l : Nat) : Nat := if c && b == 0 then l else b

theorem brOf_result (c : Bool) (b l : Nat) :
    (if c && ({ branched := b } : Result).branched == 0 then { ({ branched := b } : Result) with branched := l }
      else ({ branched := b } : Result)) = { branched := brOf c b l } := by
  unfold brOf; split <;> rfl

theorem brOf_false (b l : Nat) : brOf false b l = b := by simp [brOf]

theorem brOf_or (a c : Bool) (b l : Nat) (hl : l ≠ 0) : brOf c (brOf a b l) l = brOf (a || c) b l := by
  unfold brOf
  cases a <;> cases c <;> by_cases hb : b = 0 <;> simp [hb, hl]

/-- `checkLine`'s step on a state of the frontier, then the rest skipped past a violation. -/
theorem Trace.CheckLineRel.step_violation (tr : Trace) (invariants : Bool) (ts : TState) (rest : List TState)
    (acc : List TState × StepInfo) (succ : List TState) (i2 : StepInfo) (hv : acc.2.violation.isNone)
    (hs : tr.StepLineRel ts invariants (.ok (succ, i2))) (hv2 : i2.violation.isSome) :
    tr.CheckLineRel invariants (ts :: rest) acc
      (.ok (succ.foldl (fun nx s2 => if memEq nx s2 then nx else nx ++ [s2]) acc.1,
        { branched := acc.2.branched || i2.branched, violation := i2.violation })) :=
  .step ts rest acc succ i2 _ hv hs (Trace.CheckLineRel.skip_all tr invariants _ hv2 rest)

end Etcdraft
end EtcdGrove
end Perennial
