/-
Package initialization of `google_golang_org.grpc.internal.mem`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`internalMemInit`, `cache/v3/Base.lean`; grpc-mem, 2026-11-26): `uintSize` holds `64` for
good (no translated code writes it; `newBinaryTiered` reads it). Its initializer allocates
`BufferPoolingThreshold` and `uintSize`, initializes its imports, runs their translated initializers (the
constants `1 << 10` and `bits.UintSize`) and its translated `init` function, which stores a closure in
`internal.SetBufferPoolingThresholdForTesting`, through `internal`'s invariants (`grpc/internal/Hooks.lean`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.bits.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.sync.Link
public import Proof.google_golang_org.grpc.internal.Init
public import Proof.google_golang_org.grpc.internal.Hooks

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
