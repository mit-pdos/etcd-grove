/-
Package initialization of `go_opentelemetry_io.otel.trace`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`traceInit`, `storage/mvcc/Base.lean`): `noopSpanInstance` holds a `noopSpan` as a
`Span`, read-only for good. Its initializer allocates it, initializes its imports and runs its
translated initializer (`noopSpan{}` converted to `Span`, `noop.go`; prove-protootel, 2026-11-20:
until then in `opaqueInitsOk`), those of `tracerProviderInstance` and
`autoInstEnabled` (`new`) and of the `start`/`ended` func literals (prove-otel4, 2026-11-21), and the
untranslated initializers of its other variables (`maxSpan`, which goose's guard refuses, and the
`var _ I = T{}` assertions: `trace.toml`), which the trust-boundary axiom `opaqueInitsOk` says run
without panicking.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.context.Link
public import Proof.go_opentelemetry_io.otel.attribute.Init
public import Proof.go_opentelemetry_io.otel.codes.Init
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
