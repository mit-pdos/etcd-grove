/-
Package initialization of `hash.crc32`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`crc32Init`, `PkgInit.lean`): `IEEETable` holds, read-only, a pointer to the IEEE
table, read-only. Its initializer allocates its variables, initializes its imports and runs their
translated initializers: `simpleMakeTable(IEEE)` (`crc32.go:101`, over its spec) and the two
`sync.OnceFunc(func() {...})` (`castagnoliInitOnce`, `ieeeInitOnce`: Perennial's `sync.wp_OnceFunc`;
their functions run only when called). (prove-etcdint3, 2026-11-21: until then untranslated, the
trust-boundary axiom `opaqueInitsOk`, and its fact `True`.)
-/
module

public import Proof.hash.crc32.PkgInit
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Proof.hash.Init

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
