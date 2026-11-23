/-
Package initialization of `go_etcd_io.etcd.server.v3.features`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`featuresInit`, `features/Defs.lean`; featuregate-3, 2026-11-23, until then `True`):
`DefaultEtcdServerFeatureGates` holds a read-only map of the server's features (`serverFeatureSpecs`),
for good. Its initializer initializes its imports, allocates `DefaultEtcdServerFeatureGates` and runs
its translated initializer, a map literal of `featuregate.FeatureSpec` literals (prove-smallinits,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.features.PkgInit
public import Perennial.Proof.fmt.Link
public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.Init

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
