/-
Package initialization of `google_golang_org.grpc.mem`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True` (no translated code reads its variables). Its initializer allocates
`defaultBufferPoolSizeExponents`, `defaultBufferPool` and `bufferObjectPool`, initializes its imports, runs
the translated initializers of the first and the third (grpc-mem, 2026-11-26: a slice literal of the exponents
`8, 12, 14, 15, 20`; a `sync.Pool` literal of a function literal) and its translated `init` function
(`buffer_pool.go:52`), which builds the default pool (`NewBinaryTieredBufferPool`, proved over `internal/mem`'s
translation: no error, every exponent being at most `62`, so no panic), stores it in `defaultBufferPool`
and stores a closure in `internal.SetDefaultBufferPool`, through `internal`'s invariants
(`grpc/internal/Hooks.lean`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Proof.google_golang_org.grpc.internal.Init
public import Proof.google_golang_org.grpc.internal.mem.Init
public import Proof.google_golang_org.grpc.internal.Hooks
public import Perennial.Proof.slices.Link

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
