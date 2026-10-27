/-
clockwork's `Clock` as the auto-compactor uses it (`github.com/jonboulle/clockwork`, names only): the
trust boundary of the spec-first pilot (`notes/compactor-pilot-plan.md`, "Phase 1: the design of
the skeleton"). Lean-first (no Rocq counterpart).

**The clock** is a ghost quantity `γc`, the real clock's monotonic reading in nanoseconds, which
only the environment advances. Its predicates are axioms, as bbolt's are (`InvBbolt.lean`): what
they mean is the trust boundary, stated here.
- `clockLb γc n` (persistent): the clock has reached `n`.
- `stampAt γc P T` (persistent): the persistent fact `P` held when the clock read `T`. It is
  produced only by `After`, which reads the clock when called (`stampAt_intro` is not a law: a
  stamp cannot be made up afterwards, or `P` could be one learned later than `T`).
- `realClock`: the name of the real clock, which every `NewRealClock()` reads.
- `clockOk γc clk` (persistent): `clk` is a clock over `γc`: `Now()` returns (its value is not
  used for safety), and `After(d)` returns, for any persistent `P` and clock bound `clockLb γc n`
  the caller holds, a reading `T ≥ n` of the clock at the call, a stamp of `P` at `T`, and a channel
  whose value comes only once the clock has reached `T + d` (`T ≥ n` is what lets waits chain:
  after `k` waits of `d` from a bound `n`, the clock is past `n + k·d`).

**How to read results over these axioms.** They are lower bounds and stamps only, so they have a
trivial model (`clockLb := True`, `stampAt P T := P`): no Lean result can rule out that model. A
result's time content (a revision "at least `period` old") holds under the intended reading, that
`clockLb` and `stampAt` speak of the real clock; that reading is the trust boundary, as the meaning
of any environment axiom is (2026-10-27, the pilot's first spec review). What survives the trivial model is
what does not mention the clock: in the compactor's C1, that the store had reached the compacted
revision. The intended reading is what phase 2 tests (`notes/spec-first-plan.md`): a run under an
instrumented clock, checking each stamp against the clock's readings. `Now()` gives nothing usable
(Perennial's `Time.Sub` has no meaningful spec), which is why the compactor's first sample, timed only
by `Now()`, gets the weaker bound (`v3compactor.perPermit`).

Why this is true of clockwork v0.5.0's real clock (`clockwork.NewRealClock()`, the compactor's):
`realClock.Now` is `time.Now()` and `realClock.After` is `time.After`; Go's `time.After(d)` fires
no earlier than `d` after the call by the monotonic clock, which never goes back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import GeneratedProof.github_com.jonboulle.clockwork
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.time.Base

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

/-- The ghost name of a clock. -/
abbrev ClockName := GName

/-- **The real clock**: the one ghost clock `NewRealClock`'s clocks read (Go's monotonic clock is
the process's). -/
axiom realClock : ClockName

axiom clockLb (γc : ClockName) (n : Int) : IProp GF
axiom stampAt (γc : ClockName) (P : IProp GF) (T : Int) : IProp GF

@[instance] axiom clockLb_persistent (γc : ClockName) (n : Int) :
  Persistent (clockLb (GF := GF) γc n)
@[instance] axiom stampAt_persistent (γc : ClockName) (P : IProp GF) (T : Int) :
  Persistent (stampAt (GF := GF) γc P T)

/-- The clock has some reading (a first bound for the caller's chain). -/
axiom clockLb_init (γc : ClockName) : ⊢ ∃ n : Int, clockLb (GF := GF) γc n

/-- A lower bound of the clock is one of every smaller value. -/
axiom clockLb_le (γc : ClockName) (n m : Int) (h : m ≤ n) :
  clockLb (GF := GF) γc n ⊢ clockLb γc m

/-- A stamped fact held (and, persistent, still holds). -/
axiom stampAt_elim (γc : ClockName) (P : IProp GF) [Persistent P] (T : Int) :
  stampAt (GF := GF) γc P T ⊢ P

/-- A stamp is at a time the clock has reached. -/
axiom stampAt_clockLb (γc : ClockName) (P : IProp GF) (T : Int) :
  stampAt (GF := GF) γc P T ⊢ clockLb γc T

/-- **A clock** (`clk`, a `clockwork.Clock` interface value) over `γc`: `Now()` returns some time;
`After(d)` reads the clock at the call, `T`, at least any bound `n` the caller holds, stamps any
persistent `P` the caller holds at `T`, and returns a channel whose values come only once the clock
has reached `T + d` (for any `d`: a negative one fires at once, as Go's `time.After` does). -/
def clockOk (γc : ClockName) (clk : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜clk = GoInterface.ok ci⌝ ∗
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

/-- `Now()` returns (some time: the model gives no relation to `clockLb`). -/
theorem clockOk_Now (γc : ClockName) (ci : GoInterfaceOk) :
    clockOk (GF := GF) γc (GoInterface.ok ci) ⊢
      {{ True }} (App (Val #(methods ci.ty go!"Now" ci.v)) (Val #()))
      {{ (t : time.Time), RET #t; True }} := by
  unfold clockOk
  iintro ⟨%ci', %h, #HNow, -⟩
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
  iintro ⟨%ci', %h, -, #HAfter⟩ #HP #Hn
  cases h
  iapply HAfter $$ HP Hn

end defs

end clockwork
end EtcdGrove
end Perennial
