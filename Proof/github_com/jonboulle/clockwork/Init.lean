/-
Package initialization of `github_com.jonboulle.clockwork`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True` (`Base.lean`). Its initializer allocates its two variables, initializes its
imports and runs their translated initializers (`context.go`; until 2026-11-20 untranslated, the
trust-boundary axiom `opaqueInitsOk`): `keyClock = contextKey("clock")`, and
`ErrFakeClockDeadlineExceeded = fmt.Errorf("clockwork.FakeClock: %w", context.DeadlineExceeded)`
(`fmt.ErrorfErrs.wp_proof`: `DeadlineExceeded`'s value `deadlineExceededError{}` is an error `fmt` formats
by its `Error()`, `clockwork.errOk_deadlineExceeded`).
-/
module

public import Proof.github_com.jonboulle.clockwork.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.jonboulle.clockwork.InitFacts

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end Perennial
