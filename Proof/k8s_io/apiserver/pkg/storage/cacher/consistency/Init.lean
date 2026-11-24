/-
Package initialization of `k8s_io.apiserver.pkg.storage.cacher.consistency`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True` (its readers, the watch cache's snapshotter and `checkSnapshotResourceVersion`,
are proved only where they do not reach the load). Its initializer allocates
`PanicOnCacheInconsistency`, initializes its imports, runs the variable's translated initializer
(`false`) and its translated `init` (`checker.go:50`), which stores in it whether
`KUBE_WATCHCACHE_CONSISTENCY_CHECKER` parses as true (`os.Getenv`: the trust-boundary axiom
`os.Getenv.wp_proof`; `strconv.ParseBool.wp_proof`, proved over Perennial's translation). (Until
2026-11-24 the `init` was names-only, the trust-boundary axiom `initFuncsOk`.)
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Perennial.Proof.strconv.Link
public import Proof.k8s_io.apiserver.pkg.storage.cacher.metrics.Init
public import Proof.os.Init

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
