/-
Package initialization of `go_etcd_io.etcd.pkg.v3.featuregate`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`featuregateInit`, `featuregate/Defs.lean`; featuregate-3, 2026-11-23, until then `True`):
`defaultFeatures` holds a read-only map of `AllAlpha` and `AllBeta` (`defaultKnown`), `specialFeatures`
some map, both for good. Its initializer initializes its imports, allocates the two and runs their
translated initializers, map literals of constants and function values.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.PkgInit
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.maps.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Proof.flag.Init
public import Proof.go_uber_org.zap.Init

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
