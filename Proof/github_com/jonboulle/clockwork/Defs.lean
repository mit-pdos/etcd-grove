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
  used for safety), and `After(d)` returns, for any persistent `P` the caller holds, a stamp of
  `P` at the clock's reading `T` at the call, and a channel whose value comes only once the clock
  has reached `T + d`.

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
`After(d)` (for `0 ≤ d`) stamps any persistent `P` the caller holds at the clock's reading `T` at the
call, and returns a channel whose values come only once the clock has reached `T + d`. -/
def clockOk (γc : ClockName) (clk : GoInterface) : IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜clk = GoInterface.ok ci⌝ ∗
    □ ({{ True }} (App (Val #(methods ci.ty go!"Now" ci.v)) (Val #()))
        {{ (t : time.Time), RET #t; True }}) ∗
    □ (∀ (d : time.Duration) (P : IProp GF), ⌜0 ≤ sint.Z d⌝ -∗ □ P -∗
        {{ True }} (App (Val #(methods ci.ty go!"After" ci.v)) (Val #d))
        {{ (ch : Loc) (γ : ChanNames), RET #ch; ∃ T : Int, stampAt γc iprop(□ P) T ∗
            isChanBag γ ch (V := time.Time) (fun _ => clockLb γc (T + sint.Z d)) }}))

instance clockOk_persistent (γc : ClockName) (clk : GoInterface) :
    Persistent (clockOk (GF := GF) γc clk) := by
  unfold clockOk; infer_instance

end defs

end clockwork
end EtcdGrove
end Perennial
