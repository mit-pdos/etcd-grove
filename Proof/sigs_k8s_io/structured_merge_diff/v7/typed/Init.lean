/-
Package initialization of `sigs_k8s_io.structured_merge_diff.v7.typed`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `typedPoolsAt` (`Base.lean`, `typedPools` of `Walkers.lean` at the closures; the Prove phase, 2026-11-19):
`ruleKeepRHS` holds its closure, which meets `ruleKeepRHSOk`, and the five walker pools are
`sync.isPool`s of pooled walkers, each `New` making a zero walker (`InitClosures.lean`, over the
closures of `Closures.lean`). Its initializer allocates its translated variables, initializes its
imports, sets them (`ruleKeepRHS`, a function value; the walker pools `fmPool`, `tPool`,
`cmpwPool`, `mwPool`, `vPool`, `sync.Pool` literals with a `New` function) and runs the trusted
initializers of `ssParser` and `DeducedParseableType`
(`TrustedCode/sigs_k8s_io/structured_merge_diff/v7/typed.lean`: models that do nothing).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.InitClosures

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
