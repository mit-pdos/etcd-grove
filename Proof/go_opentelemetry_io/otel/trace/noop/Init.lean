/-
Package initialization of `go_opentelemetry_io.otel.trace.noop`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`noopInit`, `storage/mvcc/Base.lean`): `noopSpanInstance` holds a no-op `Span` as a
`trace.Span`, read-only for good. Its initializer allocates it, initializes its imports and runs its
translated initializers (`noopSpanInstance = Span{}` and the interface assertions `var _ I = T{}`,
`noop.go`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.context.Link
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.go_opentelemetry_io.otel.codes.Init
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_opentelemetry_io.otel.trace.embedded.Init

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
