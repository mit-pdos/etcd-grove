/-
The statement of a robustness theorem [Trusted definition!]: one definition, over the executions
of Perennial's distributed semantics (`Perennial/GooseLang/DistLang.lean`), for any extensions.

`Robust crashing stable g threads bound`: run the programs of `crashing`, each on a machine of its own
that may crash at any step and then restarts with its program (from a local state its extensions'
crash relations allow), and the programs of `stable`, each on a machine of its own that never
crashes, all sharing the global state `g` (the network, with whatever extensions are plugged in:
`[GooseExts] [GooseSemantics]`). Then, in every execution of fewer than `bound` steps along which
every machine keeps fewer than `threads` live threads, no thread of any machine has a panic that nothing recovered (a top-level panic), and none is stuck (which
is what an invalid operation is in GooseLang, its builtin `Panic` among them: the conclusion of
the adequacy theorems, `goose_dist_crash_adequacy`).

The executions are `DistCrashNstepsBelow`, Perennial's (`DistCrashNsteps` with the thread bound in
every configuration, the first and the last included): a real step of one thread of one machine, or a
crash of a machine that has a boot program. Its list of boot programs is `crashing`'s, so the
machines of `stable`, which come after them, have none and never crash (`distCrashStep_cases`).
Everything else is that relation's nondeterminism: the scheduler (a machine that never runs
again, or starts late, is one it does not pick), the crashes, and the faults the extensions'
semantics allow (the net extension: a direction cut at any read or write, any delay, a dial
failing; a partition is such an execution).

**Every machine starts as a fresh Go process** (`Fresh`, a premise inside `Robust`, so that no
instance repeats it): its Go context is the one the theorem's Go semantics is about (`lctx`, the
instance `[GoLocalContext]`: the meaning of the Go instructions, shared by the machines as echo's
three programs share one), no package is initialized, and it has its main thread only. **Every
machine and the shared state start in their extensions' initial states** (Perennial's trusted
`ExtSemantics.initLocal`/`initGlobal`, through `extsInitLocal`/`extsInitGlobal`: e.g. the net
extension's no listener and no connection, `Net.net_semantics`, and the Linux file extension's files
as on disk, `Fs.fs_semantics`, both stated by the extensions since 2026-11-22; an extension that
states none starts anywhere, Perennial's default `True`; premises inside `Robust` too, 2026-11-21,
for kvnet's statement). What an instance needs beyond them (a directory
that is empty, its addresses) stays the instance's.

The statement says nothing of what the programs compute. A property of a system (its clients'
history is linearizable) is a theorem of this form about a deployment that includes a program
checking it and panicking if it fails, e.g. a client on a machine that does not crash, which
keeps its history: the property is then written in Go, where it is tested, and not in a trusted
Lean definition over traces.

The step bound is the proofs' (time receipts, as the closed adequacy theorems' `n < 2^61`).

**The thread bound is a premise about the execution, not about the program**, and independent of
the step bound (until 2026-11-20 `Robust` had none, and an instance's step bound had to stay below
the thread bound its proof needed: `2^28 - 1` steps for the etcd examples). What it excludes: an
execution in which some machine reaches `threads` live threads is covered up to the configuration
before, not after; the bound is over every machine, so one machine's runaway goroutines also end
the coverage of another machine's later steps. A machine's count (`state.threads`) is its forks
minus the `ThreadExit` steps it has taken: Goose's output runs `ThreadExit` only as a forked
thread's last step, so for it the count is the forked threads not yet retired, which includes a
thread that has returned or panicked and not yet taken that step (a count above the live
goroutines, which only excludes more). An instance with no thread bound of its own states
`threads := bound + 1`, which is the statement without it (`Robust.toAll`, and from fresh machines
fewer than `bound` steps never reach `bound + 1` threads).
-/
module

public import Perennial.GooseLang.DistLang
public import Perennial.GooseLang.CrashLang
public import Perennial.GooseLang.AdequacyAlong

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

open Iris.ProgramLogic

section statement
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- The machine with the local state `σ` is a fresh Go process with the Go context `lctx`: no
package initialized, its main thread only. -/
def Fresh (lctx : GoLocalContext) (σ : state) : Prop :=
  σ.goState.goLctx = lctx ∧ σ.goState.packageState = ∅ ∧ σ.threads = 1

/-- **A robustness statement** (see the file header): in every execution of fewer than `bound`
steps along which every machine keeps fewer than `threads` live threads, of the machines
`crashing` (which may crash and restart) and `stable` (which never crash), each running its
program from its local state, a fresh Go process with the context `lctx` in its extensions'
initial state, on the shared state `g`, in its extensions' initial state, no thread of any machine
is stuck or has an unrecovered panic. -/
def Robust [lctx : GoLocalContext] (crashing stable : List (Expr × state)) (g : GlobalState)
    (threads bound : Nat) : Prop :=
  (∀ m, m ∈ crashing ++ stable → Fresh lctx m.2) →
  extsInitGlobal g →
  (∀ m, m ∈ crashing ++ stable → extsInitLocal m.2 g) →
  ∀ (n : Nat) (κs : List Observation) (c : DistCfg),
    DistCrashNstepsBelow (crashing.map Prod.fst) threads n (distInit (crashing ++ stable) g) κs
      c →
    n < bound →
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      ∀ e, e ∈ tp → RealNotStuck e (σ, c.global) ∧ ¬ UnrecoveredPanic e

end statement

/-! ## Sanity -/

section facts
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- A step of the executions is a step of a thread, or a crash of one of the first
`boots.length` machines: a machine after them never crashes. -/
theorem distCrashStep_cases {boots : List Expr} {c c' : DistCfg} {κ : List Observation}
    (h : DistCrashStep boots c κ c') :
    DistStep c κ c' ∨
      ∃ i tp σ e σ', i < boots.length ∧ c.nodes[i]? = some (tp, σ) ∧ boots[i]? = some e ∧
        Crash σ σ' ∧ c' = ⟨c.nodes.set i ([e], σ'), c.global⟩ := by
  cases h with
  | step h => exact .inl h
  | @crash nodes g i tp σ e σ' hi hb hc =>
    exact .inr ⟨i, tp, σ, e, σ', (List.getElem?_eq_some_iff.mp hb).1, hi, hb, hc, rfl⟩

/-- Letting more machines crash only adds executions. -/
theorem distCrashNsteps_more_boots {boots : List Expr} (rest : List Expr) {n : Nat}
    {c c' : DistCfg} {κs : List Observation} (h : DistCrashNsteps boots n c κs c') :
    DistCrashNsteps (boots ++ rest) n c κs c' := by
  induction h with
  | refl c => exact .refl c
  | cons hs _ ih =>
    refine .cons ?_ ih
    cases hs with
    | step hs => exact .step hs
    | crash hi hb hc =>
      refine .crash hi ?_ hc
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]
      exact hb

/-- Letting more machines crash only adds executions, the thread bound kept. -/
theorem distCrashNstepsBelow_more_boots {boots : List Expr} (rest : List Expr) {T n : Nat}
    {c c' : DistCfg} {κs : List Observation} (h : DistCrashNstepsBelow boots T n c κs c') :
    DistCrashNstepsBelow (boots ++ rest) T n c κs c' := by
  induction h with
  | refl c hc => exact .refl c hc
  | cons hc hs _ ih =>
    refine .cons hc ?_ ih
    cases hs with
    | step hs => exact .step hs
    | crash hi hb hcr =>
      refine .crash hi ?_ hcr
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1]
      exact hb

/-- A deployment that is robust when every machine may crash is robust when only some may: the
distributed crash adequacy theorem (`goose_dist_crash_adequacy`, about executions in which every
node may crash) proves statements of this form. -/
theorem Robust.of_all_crashing [GoLocalContext] {crashing stable : List (Expr × state)}
    {g : GlobalState} {threads bound : Nat} (h : Robust (crashing ++ stable) [] g threads bound) :
    Robust crashing stable g threads bound := by
  intro hfresh hig hil n κs c hsteps hn
  refine h (by simpa using hfresh) hig (by simpa using hil) n κs c ?_ hn
  rw [List.map_append, List.append_nil]
  exact distCrashNstepsBelow_more_boots _ hsteps

/-- One machine with no boot program runs as a single process: its executions are the real
thread-pool executions (`RealNsteps`) of its threads. -/
theorem distCrashNsteps_single {n : Nat} {tp : List Expr} {σ : state} {g : GlobalState}
    {κs : List Observation} {c : DistCfg}
    (h : DistCrashNsteps [] n ⟨[(tp, σ)], g⟩ κs c) :
    ∃ tp' σ' g', c = ⟨[(tp', σ')], g'⟩ ∧ RealNsteps n (tp, (σ, g)) κs (tp', (σ', g')) := by
  generalize hc₀ : (⟨[(tp, σ)], g⟩ : DistCfg) = c₀ at h
  induction h generalizing tp σ g with
  | refl c => subst hc₀; exact ⟨tp, σ, g, rfl, @Language.NSteps.refl _ _ _ _ gooseRealLang _⟩
  | @cons n c₁ c₂ c₃ κ κs hstep _ ih =>
    subst hc₀
    cases hstep with
    | crash _ hb _ => simp at hb
    | step hstep =>
      cases hstep with
      | @node nodes g i tp₀ σ₀ κ tp₁ σ₁ g₁ hi hs =>
        obtain rfl : i = 0 := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp only [List.length_singleton] at this
          omega
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        obtain ⟨tp', σ', g', rfl, hrest⟩ := ih (tp := tp₁) (σ := σ₁) (g := g₁) rfl
        exact ⟨tp', σ', g', rfl, @Language.NSteps.cons _ _ _ _ gooseRealLang _ _ _ _ _ _ hs hrest⟩

/-- **A single process that never crashes**: the conclusion of the single-node adequacy theorem
(`goose_adequacy`: no thread stuck, none with an unrecovered panic, in every real execution of the
program of fewer than `bound` steps) is the robustness statement of the program alone on a
machine that does not crash, a fresh Go process (`Fresh`), at any thread bound. -/
theorem Robust.of_single [lctx : GoLocalContext] {e : Expr} {σ : state} {g : GlobalState}
    {threads bound : Nat}
    (h : Fresh lctx σ →
      ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState), n < bound →
      RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2) →
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)) :
    Robust [] [(e, σ)] g threads bound := by
  intro hfresh _ _ n κs c hsteps hn i tp' σ' hi e' he'
  obtain ⟨tp₁, σ₁, g₁, rfl, hreal⟩ := distCrashNsteps_single (tp := [e]) hsteps.nsteps
  obtain ⟨hns, hnp⟩ := h (hfresh (e, σ) (by simp)) n κs tp₁ (σ₁, g₁) hn hreal
  obtain rfl : i = 0 := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_singleton] at this
    omega
  simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
  obtain ⟨rfl, rfl⟩ := hi
  exact ⟨hns e' he', hnp e' he'⟩

/-- Every machine may crash: the hypothesis is the distributed crash adequacy theorem's
conclusion as it stands (`goose_dist_crash_adequacy`), for the machines `es`. -/
theorem Robust.of_all [lctx : GoLocalContext] {es : List (Expr × state)} {g : GlobalState}
    {threads bound : Nat}
    (h : (∀ m, m ∈ es → Fresh lctx m.2) →
      ∀ (n : Nat) (κs : List Observation) (c : DistCfg),
        DistCrashNsteps (es.map Prod.fst) n (distInit es g) κs c → n < bound →
        ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
          (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧ (∀ e, e ∈ tp → ¬ UnrecoveredPanic e)) :
    Robust es [] g threads bound := by
  intro hf _ _ n κs c hs hn i tp σ hi e he
  simp only [List.append_nil] at hf hs
  obtain ⟨h₁, h₂⟩ := h hf n κs c hs.nsteps hn i tp σ hi
  exact ⟨h₁ e he, h₂ e he⟩

/-- A real step before an execution with crashes of one process. -/
theorem realCrashNsteps_step {boot : Expr} {m : Nat} {ρ₁ ρ₂ ρ' : List Expr × CfgState}
    {κ κs : List Observation} {b : Bool}
    (hs : @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂) (h : RealCrashNsteps boot m ρ₂ κs ρ' b) :
    RealCrashNsteps boot (m + 1) ρ₁ (κ ++ κs) ρ' b := by
  cases h with
  | done h =>
    exact .done (@Language.NSteps.cons _ _ _ _ gooseRealLang _ _ _ _ _ _ hs h)
  | @crash n₁ m₂ _ κs₁ t σ g σ' κs₂ _ b' h₁ hc h₂ =>
    have h₃ := RealCrashNsteps.crash (boot := boot)
      (@Language.NSteps.cons _ _ _ _ gooseRealLang _ _ _ _ _ _ hs h₁) hc h₂
    rw [List.append_assoc] at h₃
    rw [show n₁ + m₂ + 1 = n₁ + 1 + m₂ by omega]
    exact h₃

/-- One machine with a boot program runs as a single process with crashes: its executions are
`RealCrashNsteps`'s (which does not count a crash as a step, so of at most as many steps). -/
theorem distCrashNsteps_single_crashing {boot : Expr} {n : Nat} {tp : List Expr} {σ : state}
    {g : GlobalState} {κs : List Observation} {c : DistCfg}
    (h : DistCrashNsteps [boot] n ⟨[(tp, σ)], g⟩ κs c) :
    ∃ tp' σ' g' m b, m ≤ n ∧ c = ⟨[(tp', σ')], g'⟩ ∧
      RealCrashNsteps boot m (tp, (σ, g)) κs (tp', (σ', g')) b := by
  generalize hc₀ : (⟨[(tp, σ)], g⟩ : DistCfg) = c₀ at h
  induction h generalizing tp σ g with
  | refl c =>
    subst hc₀
    exact ⟨tp, σ, g, 0, false, Nat.le_refl _, rfl,
      .done (@Language.NSteps.refl _ _ _ _ gooseRealLang _)⟩
  | @cons n c₁ c₂ c₃ κ κs hstep _ ih =>
    subst hc₀
    cases hstep with
    | @crash nodes g i tp₀ σ₀ e σ₁ hi hb hcr =>
      obtain rfl : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp only [List.length_singleton] at this
        omega
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi hb
      obtain ⟨rfl, rfl⟩ := hi
      subst hb
      obtain ⟨tp', σ', g', m, b, hm, rfl, hrest⟩ := ih (tp := [boot]) (σ := σ₁) (g := g) rfl
      refine ⟨tp', σ', g', 0 + m, true, by omega, rfl, ?_⟩
      exact .crash (@Language.NSteps.refl _ _ _ _ gooseRealLang _) hcr hrest
    | step hstep =>
      cases hstep with
      | @node nodes g i tp₀ σ₀ κ tp₁ σ₁ g₁ hi hs =>
        obtain rfl : i = 0 := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp only [List.length_singleton] at this
          omega
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        obtain ⟨tp', σ', g', m, b, hm, rfl, hrest⟩ := ih (tp := tp₁) (σ := σ₁) (g := g₁) rfl
        exact ⟨tp', σ', g', m + 1, b, by omega, rfl, realCrashNsteps_step hs hrest⟩

/-- **A single process that crashes and restarts**: the conclusion of the single-node crash
adequacy theorem (no thread stuck, none with an unrecovered panic, in every real execution with
crashes of the program of fewer than `bound` steps) is the robustness statement of the program
alone on a machine that may crash, a fresh Go process (`Fresh`). -/
theorem Robust.of_single_crashing [lctx : GoLocalContext] {e : Expr} {σ : state}
    {g : GlobalState} {threads bound : Nat}
    (h : Fresh lctx σ →
      ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool),
      n < bound → RealCrashNsteps e n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b →
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)) :
    Robust [(e, σ)] [] g threads bound := by
  intro hfresh _ _ n κs c hsteps hn i tp' σ' hi e' he'
  obtain ⟨tp₁, σ₁, g₁, m, b, hm, rfl, hreal⟩ :=
    distCrashNsteps_single_crashing (boot := e) (tp := [e]) hsteps.nsteps
  obtain ⟨hns, hnp⟩ := h (hfresh (e, σ) (by simp)) m κs tp₁ (σ₁, g₁) b (by omega) hreal
  obtain rfl : i = 0 := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_singleton] at this
    omega
  simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
  obtain ⟨rfl, rfl⟩ := hi
  exact ⟨hns e' he', hnp e' he'⟩

/-- One machine with no boot program, with the thread bound: its executions are the real
thread-pool executions of its threads with the same bound (`RealNstepsBelow`). -/
theorem distCrashNstepsBelow_single {T n : Nat} {tp : List Expr} {σ : state} {g : GlobalState}
    {κs : List Observation} {c : DistCfg}
    (h : DistCrashNstepsBelow [] T n ⟨[(tp, σ)], g⟩ κs c) :
    ∃ tp' σ' g', c = ⟨[(tp', σ')], g'⟩ ∧ RealNstepsBelow T n (tp, (σ, g)) κs (tp', (σ', g')) := by
  generalize hc₀ : (⟨[(tp, σ)], g⟩ : DistCfg) = c₀ at h
  induction h generalizing tp σ g with
  | refl c hc =>
    subst hc₀
    exact ⟨tp, σ, g, rfl, .refl _ (hc 0 tp σ rfl)⟩
  | @cons n c₁ c₂ c₃ κ κs hc hstep _ ih =>
    subst hc₀
    cases hstep with
    | crash _ hb _ => simp at hb
    | step hstep =>
      cases hstep with
      | @node nodes g i tp₀ σ₀ κ tp₁ σ₁ g₁ hi hs =>
        obtain rfl : i = 0 := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp only [List.length_singleton] at this
          omega
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        obtain ⟨tp', σ', g', rfl, hrest⟩ := ih (tp := tp₁) (σ := σ₁) (g := g₁) rfl
        exact ⟨tp', σ', g', rfl, .cons (hc 0 _ _ rfl) hs hrest⟩

/-- **A single process that never crashes, with its thread bound**: the conclusion of
`goose_adequacy_below` (Perennial's `AdequacyAlong.lean`: in every real execution of fewer than
`bound` steps along which fewer than `threads` threads are live, no thread stuck, none with an
unrecovered panic) is the robustness statement at that thread bound. -/
theorem Robust.of_single_below [lctx : GoLocalContext] {e : Expr} {σ : state} {g : GlobalState}
    {threads bound : Nat}
    (h : Fresh lctx σ →
      ∀ (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState), n < bound →
      RealNstepsBelow threads n ([e], ((σ, g) : CfgState)) κs (t2, σ2) →
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧ (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)) :
    Robust [] [(e, σ)] g threads bound := by
  intro hfresh _ _ n κs c hsteps hn i tp' σ' hi e' he'
  obtain ⟨tp₁, σ₁, g₁, rfl, hreal⟩ := distCrashNstepsBelow_single (tp := [e]) hsteps
  obtain ⟨hns, hnp⟩ := h (hfresh (e, σ) (by simp)) n κs tp₁ (σ₁, g₁) hn hreal
  obtain rfl : i = 0 := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_singleton] at this
    omega
  simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
  obtain ⟨rfl, rfl⟩ := hi
  exact ⟨hns e' he', hnp e' he'⟩

/-- The machines of a deployment of fresh processes start with one thread each. -/
theorem distInit_threads [lctx : GoLocalContext] {es : List (Expr × state)} {g : GlobalState}
    (hf : ∀ m, m ∈ es → Fresh lctx m.2) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), (distInit es g).nodes[i]? = some (tp, σ) →
      σ.threads = 1 := by
  intro i tp σ hi
  simp only [distInit, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨m, hm, hmeq⟩ := hi
  cases hmeq
  exact (hf m (List.mem_of_getElem? hm)).2.2

/-- **What a robustness statement says without its thread bound**: from fresh machines, an
execution of `n` steps never has more than `n + 1` threads on a machine, so `Robust … threads
bound` covers every execution (`DistCrashNsteps`, no thread bound) of fewer than
`min bound (threads - 1)` steps. An instance with `threads := bound + 1` thus says exactly what
the statement without a thread bound said (the converse being `Robust.of_single` and its
siblings, which take that statement's hypothesis). -/
theorem Robust.toAll [lctx : GoLocalContext] {crashing stable : List (Expr × state)}
    {g : GlobalState} {threads bound : Nat} (h : Robust crashing stable g threads bound)
    (hf : ∀ m, m ∈ crashing ++ stable → Fresh lctx m.2) (hig : extsInitGlobal g)
    (hil : ∀ m, m ∈ crashing ++ stable → extsInitLocal m.2 g) (n : Nat) (κs : List Observation)
    (c : DistCfg)
    (hs : DistCrashNsteps (crashing.map Prod.fst) n (distInit (crashing ++ stable) g) κs c)
    (hn : n < min bound (threads - 1)) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) →
      ∀ e, e ∈ tp → RealNotStuck e (σ, c.global) ∧ ¬ UnrecoveredPanic e :=
  h hf hig hil n κs c ((DistCrashNstepsBelow.of_single hs (distInit_threads hf)).mono (by omega))
    (by omega)

end facts

end Robustness
end Perennial
