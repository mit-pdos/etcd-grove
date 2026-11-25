/-
clockwork's `Clock` as the auto-compactor uses it (`github.com/jonboulle/clockwork`): the spec-first
pilot's clock (`notes/compactor-pilot-plan.md`, "Phase 1: the design of the skeleton"). Lean-first.

Until 2026-11-21 these predicates were axioms (the trust boundary); they are now defined over
Perennial's model of the runtime's monotonic clock (`Perennial/TrustedCode/time.lean`, "The runtime's
monotonic clock"; `time.clockLb`, `Perennial/Proof/time/Base.lean`), and `NewRealClock` with
`realClock`'s `Now` and `After` are proved over clockwork v0.5.0's code.
- `clockLb γc n` (persistent): the clock has reached `n` (for `n > 2^63 - 1`: it has reached
  `2^63 - 1`, where Go's clock and timers saturate).
- `stampAt γc P T` (persistent, sealed): the persistent fact `P` held when the clock read `T`. Its
  only producer is `time.After` (`wp_After_stamp`), which stamps a fact the caller holds with the
  reading at the call; no law makes one up.
- `realClock`: the real clock, the only `ClockName`.
- `clockOk γc clk` (persistent): `clk` is a clock over `γc`: `Now()` returns (its value is not used
  for safety), `After(d)` returns, for any persistent `P` and bound `clockLb γc n` the caller holds,
  a reading `T ≥ n`, a stamp of `P` at `T`, and a channel whose value comes only once the clock has
  reached `T + d`; and the clock has some bound (`clockLb_init`).

**How to read results over these predicates.** `clockLb` speaks of the model's clock, which a
program observes only through the timers; the trusted claim (Perennial's model) is that the
machine's monotonic clock is one of the model clock's evolutions (Go's timers fire only once
`nanotime() >= when`, and `nanotime` never goes back). A stamp's "`P` held at `T`" is not
expressible in Iris beyond `□ P ∗ clockLb T`; the sealing keeps it to `After`'s stamps.
`Now()` gives nothing usable (Perennial's `runtimeNow` readings are arbitrary), which is why the
compactor's first sample, timed only by `Now()`, gets the weaker bound (`v3compactor.perPermit`).
-/
module

public import Proof.github_com.jonboulle.clockwork.Base
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.time.Base
public import Perennial.Spec.time.After

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace clockwork

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The name of a clock: the real clock (`realClock`), the only one the proofs know. -/
inductive ClockName where
  /-- The runtime's monotonic clock, which every `NewRealClock()` reads (Go's monotonic clock is
  the process's). -/
  | real

/-- **The real clock**: the one clock `NewRealClock`'s clocks read. -/
abbrev realClock : ClockName := .real

/-- The clock `γc` has reached `n`: for the real clock, Perennial's `time.clockLb n` (its model of the
runtime's monotonic clock, `Perennial/Proof/time/Base.lean`; values above `2^63 - 1`, where Go's
clock and timers saturate, count as `2^63 - 1`). -/
def clockLb : ClockName → Int → IProp GF
  | .real, n => time.clockLb n

/-- The persistent fact `P` held when the clock `γc` read `T`: `P`, and the clock has reached `T`.
Sealed (`@[no_expose]`): no law makes one up, so a stamp comes only from `After`, which stamps a fact
the caller holds at the call with the clock's reading at the call. -/
@[no_expose] def stampAt (γc : ClockName) (P : IProp GF) (T : Int) : IProp GF :=
  iprop(□ P ∗ clockLb γc T)

instance clockLb_persistent (γc : ClockName) (n : Int) :
    Persistent (clockLb (GF := GF) γc n) := by
  cases γc; unfold clockLb; infer_instance

instance stampAt_persistent (γc : ClockName) (P : IProp GF) (T : Int) :
    Persistent (stampAt (GF := GF) γc P T) := by
  unfold stampAt; infer_instance

/-- A lower bound of the clock is one of every smaller value. -/
theorem clockLb_le (γc : ClockName) (n m : Int) (h : m ≤ n) :
    clockLb (GF := GF) γc n ⊢ clockLb γc m := by
  cases γc; unfold clockLb; exact time.clockLb_le h

/-- A stamped fact held (and, persistent, still holds). -/
theorem stampAt_elim (γc : ClockName) (P : IProp GF) [Persistent P] (T : Int) :
    stampAt (GF := GF) γc P T ⊢ P := by
  unfold stampAt
  iintro ⟨#HP, -⟩
  iexact HP

/-- A stamp is at a time the clock has reached. -/
theorem stampAt_clockLb (γc : ClockName) (P : IProp GF) (T : Int) :
    stampAt (GF := GF) γc P T ⊢ clockLb γc T := by
  unfold stampAt
  iintro ⟨-, #H⟩
  iexact H

/-- **Where stamps come from**: Go's `time.After(d)` (over Perennial's spec, `time.After.spec`),
which `realClock.After` calls: under `time`'s `isPkgInit`, for a persistent `P` and a bound `clockLb n` the caller holds, the
clock's reading `T ≥ n` at the call, a stamp of `P` at `T`, and a channel whose values come only once
the real clock has reached `T + d`. -/
theorem wp_After_stamp [github_com.jonboulle.clockwork.Assumptions]
    (wp_After : time.After.spec (GF := GF) (hG := hG)) (d : time.Duration)
    (P : IProp GF) (n : Int) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.time -∗ □ P -∗ clockLb realClock n -∗
      {{ True }} (App (Val (@! time.After)) (Val #d))
      {{ (ch : Loc) (γ : ChanNames), RET #ch; ∃ T : Int, ⌜n ≤ T⌝ ∗ stampAt realClock iprop(□ P) T ∗
          isChanBag γ ch (V := time.Time) (fun _ => clockLb realClock (T + sint.Z d)) }} := by
  iintro #Ht #HP #Hn
  unfold clockLb
  imodintro
  iintro %Φ _ HΦ
  wp_apply_core wp_After d n (fun T => time.clockLb (T + sint.Z d)) $$ [Hn]
  · isplitr
    · iexact Ht
    iframe Hn
    iintro %T _ #H
    iexact H
  iintro %ch %γ %T ⟨%HT, #HTlb, #Hch⟩
  iapply HΦ
  iexists T
  isplitr
  · ipureintro; exact HT
  iframe Hch
  unfold stampAt clockLb
  iframe #

/-- **A clock** (`clk`, a `clockwork.Clock` interface value) over `γc`: `Now()` returns some time;
`After(d)` reads the clock at the call, `T`, at least any bound `n` the caller holds, stamps any
persistent `P` the caller holds at `T`, and returns a channel whose values come only once the clock
has reached `T + d` (for any `d`: a negative one fires at once, as Go's `time.After` does); and
the clock has some reading (`clockLb_init`). -/
def clockOk (γc : ClockName) (clk : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜clk = GoInterface.ok ci⌝ ∗ (∃ n : Int, clockLb γc n) ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Now" ci.v)) (Val #()))
        {{ (t : time.Time), RET #t; True }}) ∗
    □ (∀ (d : time.Duration) (P : IProp GF) (n : Int), □ P -∗ clockLb γc n -∗
        {{ True }} (App (Val #(methods ci.ty go!"After" ci.v)) (Val #d))
        {{ (ch : Loc) (γ : ChanNames), RET #ch; ∃ T : Int, ⌜n ≤ T⌝ ∗ stampAt γc iprop(□ P) T ∗
            isChanBag γ ch (V := time.Time) (fun _ => clockLb γc (T + sint.Z d)) }}))

instance clockOk_persistent (γc : ClockName) (clk : GoInterface) :
    Persistent (clockOk (GF := GF) γc clk) := by
  unfold clockOk; infer_instance

/-! The laws a client uses instead of unfolding `clockOk`: the clock is a non-nil interface, and
its methods' triples. -/

theorem clockOk_ok (γc : ClockName) (clk : GoInterface) :
    clockOk (GF := GF) γc clk ⊢ ⌜∃ ci : GoInterfaceOk, clk = GoInterface.ok ci⌝ := by
  unfold clockOk
  iintro ⟨%ci, %h, -⟩
  ipureintro; exact ⟨ci, h⟩

/-- The clock has some reading (a first bound for the caller's chain). -/
theorem clockLb_init (γc : ClockName) (clk : GoInterface) :
    clockOk (GF := GF) γc clk ⊢ ∃ n : Int, clockLb γc n := by
  unfold clockOk
  iintro ⟨%ci, %h, #Hn, -⟩
  iexact Hn

/-- `Now()` returns (some time: the model gives no relation to `clockLb`). -/
theorem clockOk_Now (γc : ClockName) (ci : GoInterfaceOk) :
    clockOk (GF := GF) γc (GoInterface.ok ci) ⊢
      {{ True }} (App (Val #(methods ci.ty go!"Now" ci.v)) (Val #()))
      {{ (t : time.Time), RET #t; True }} := by
  unfold clockOk
  iintro ⟨%ci', %h, -, #HNow, -⟩
  cases h
  iexact HNow

/-- `After(d)`: a channel that delivers once the clock is `d` past a time `T`, at least any bound
`n` the caller holds, at which a persistent fact `P` the caller holds is stamped. -/
theorem clockOk_After (γc : ClockName) (ci : GoInterfaceOk) (d : time.Duration) (P : IProp GF)
    (n : Int) :
    clockOk (GF := GF) γc (GoInterface.ok ci) ⊢ □ P -∗ clockLb γc n -∗
      {{ True }} (App (Val #(methods ci.ty go!"After" ci.v)) (Val #d))
      {{ (ch : Loc) (γ : ChanNames), RET #ch; ∃ T : Int, ⌜n ≤ T⌝ ∗ stampAt γc iprop(□ P) T ∗
          isChanBag γ ch (V := time.Time) (fun _ => clockLb γc (T + sint.Z d)) }} := by
  unfold clockOk
  iintro ⟨%ci', %h, -, -, #HAfter⟩ #HP #Hn
  cases h
  iapply HAfter $$ HP Hn

end defs

end clockwork
end EtcdGrove
end Perennial
