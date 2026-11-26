/-
Package initialization of `go_opentelemetry_io.otel.«attribute»`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer allocates `encoderIDCounter` and `defaultEncoderID`,
initializes its import (`sync/atomic`) and runs its translated `init` (prove-otel-encoderid,
2026-11-25: the fork's `id := NewEncoderID(); defaultEncoderID = id`, in place of `defaultEncoderID =
NewEncoderID()`, which goose's modelcheck refuses and was the trust-boundary axiom `opaqueInitsOk`):
`NewEncoderID`'s proof, on the counter at zero, returns the ID 1, which it stores.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.sync.atomic.Link

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
