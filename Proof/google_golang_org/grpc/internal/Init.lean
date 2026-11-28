/-
Package initialization of `google_golang_org.grpc.internal`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`internalInit`, `cache/v3/Base.lean`): the invariants of its hook cells (`hookCell`),
which a package initializer holding its package state opens for a plain store (`grpc/internal/Hooks.lean`).
Its initializer allocates the hook variables that the translated `init`s of `metadata`, `codes` and grpc
set (`internal.go`, `experimental.go`: no initializers, so each holds `nil`) and puts each cell in its
invariant (phase7-inits, 2026-11-25); `FromOutgoingContextRaw`, which grpc's initializer also reads, in an
invariant of its own that says `metadata`'s `init` stored `metadata.fromOutgoingContextRaw` in it
(`fromOutRawInv`, `grpc/internal/FromOutRaw.lean`; phase 7 S2 core, 2026-11-23; W1, 2026-11-26); its
other variables with initializers are goose `[[skip]]`s (literals), the rest names only.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Proof.google_golang_org.grpc.connectivity.Init
public import Proof.google_golang_org.grpc.internal.Hooks
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
