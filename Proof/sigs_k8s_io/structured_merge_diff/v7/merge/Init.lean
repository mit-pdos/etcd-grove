/-
Package initialization of `sigs_k8s_io.structured_merge_diff.v7.merge`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True` (`Base.lean`). Its initializer initializes its imports and evaluates
`var _ error = Conflicts{}` (`conflict.go`: a conversion to an interface, discarded; goose stores
nothing for a blank variable).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Init
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Init

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
