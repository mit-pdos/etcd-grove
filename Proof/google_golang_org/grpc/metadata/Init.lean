/-
Package initialization of `google_golang_org.grpc.metadata`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`metadataInit`, `cache/v3/Base.lean`; phase 7 S2 core, 2026-11-23, until then `True`):
its `init` has stored `fromOutgoingContextRaw` in `internal.FromOutgoingContextRaw` for good (the counter of
`internal`'s invariant past `0`). Its initializer allocates `loggableMetadataKeys`, initializes its imports,
runs its variable's translated initializer, a map literal of the keys `MD.String` prints (prove-grpcext,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`), and its translated `init` function
(phase 7 S2 core, 2026-11-23; until then the trust-boundary axiom `initFuncsOk`), which stores
`fromOutgoingContextRaw`, converted to `any`, in `internal.FromOutgoingContextRaw`, another package's
variable: through `internal`'s invariant, lending the initializer's package state
(`grpc/internal/FromOutRaw.lean`, `wp_store_fromOutRaw`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.strings.Link
public import Proof.google_golang_org.grpc.internal.Init
public import Proof.google_golang_org.grpc.internal.FromOutRaw

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
