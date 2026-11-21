/-
Package initialization of `k8s_io.apiserver.pkg.util.flowcontrol`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s2, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): `readOnlyVerbs = sets.NewString(...)` (`sets` with bodies: `New`'s spec) and the
two interface assertions `var _ fmt.GoStringer = RequestDigest{}` and
`var _ fmt.GoStringer = (*priorityLevelState)(nil)` (conversions to an interface).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.fmt.Link
public import Proof.k8s_io.apimachinery.pkg.util.sets.Init
public import Proof.k8s_io.apiserver.pkg.authentication.user.Init
public import Proof.k8s_io.apiserver.pkg.endpoints.request.Init

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
