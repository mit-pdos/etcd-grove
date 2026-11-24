/-
Package initialization of `go_uber_org.zap.zapcore`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact: `DefaultClock` holds a fixed `systemClock` (zap's `NewNop`, which zap's
initializer runs, loads it; prove-initleft, 2026-11-21: until then `True`), and `_cePool` a fixed pool of
owned entries (zap-z2, 2026-11-23: `CheckedEntry.Write` and `After` use it). Its initializer initializes its imports, allocates its variables and runs
their translated initializers and its translated `init` (prove-misc, 2026-11-20; until then the
trust-boundary axioms `opaqueInitsOk` and `initFuncsOk`): the pools (`pool.New`, proved), the interface
assertions, `nullLiteralBytes`, `errUnmarshalNilLevel` (`errors.New`), the level colors (a map literal)
and their two string maps, which `init` (`level_strings.go`) fills: each level's color formatted
around its name (`color.Add`, `fmt.Sprintf`; `Level.String`/`CapitalString` of the map's levels).
-/
module

public import Proof.go_uber_org.zap.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.go_uber_org.multierr.Init
public import Proof.go_uber_org.zap.internal.color.Init
public import Proof.go_uber_org.zap.internal.exit.Init
public import Proof.go_uber_org.zap.internal.pool.Init
public import Proof.runtime.Init
public import Proof.fmt.SprintfPure
public import Perennial.Proof.errors.NewVar

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
