/-
Package initialization of `hash.crc32`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`crc32Init`, `PkgInit.lean`): `IEEETable` holds, read-only, a pointer to the IEEE
table, read-only; `castagnoliInitOnce` a function every call of which returns with the Castagnoli
table set up (`castagnoliReady`); and `haveInv`, the invariant of `haveCastagnoli` (once true, the
table is set up and `updateCastagnoli` holds a function computing CRC-32C). Its initializer allocates
its variables, initializes its imports and runs their translated initializers: `simpleMakeTable(IEEE)`
(`crc32.go:101`, over its spec) and the two `sync.OnceFunc(func() {...})` (`castagnoliInitOnce`,
`ieeeInitOnce`: Perennial's `sync.wp_OnceFunc`; their functions run only when called). The proof
allocates `haveInv` and gives `castagnoliInitOnce`'s function its triple: it sets `castagnoliTable`
(`simpleMakeTable`), then either the fast path (`archInitCastagnoli`, `archUpdateCastagnoli`: the
trusted hooks) or the slicing-by-8 table and its closure (`slicingMakeTable`, `slicingUpdate`), and
stores `true` in `haveCastagnoli`. (prove-etcdint3, 2026-11-21: until then untranslated, the
trust-boundary axiom `opaqueInitsOk`, and its fact `True`; crc32-hooks2, 2026-11-22, etcd-grove#14:
the Castagnoli state and once.)
-/
module

public import Proof.hash.crc32.PkgInit
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Proof.hash.Init
public import Proof.internal.byteorder.Init

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
