/-
Package initialization of `k8s_io.apimachinery.pkg.api.errors`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`apierrorsInit`, `storage/etcd3/Base.lean`; prove-k8s2, 2026-11-20, `True` until then):
`knownReasons` holds, read-only for good, the map of the 19 known reasons (`knownReasonsMap`), which
`IsTimeout` looks reasons up in. Its initializer initializes its imports, allocates its variables and
runs their translated initializers: `var _ error = &StatusError{}` and `knownReasons`, a map literal
of the 19 known reasons (prove-k8s, 2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.net.http.Init

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
