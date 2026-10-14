/-
Lean-first (no Rocq counterpart).

# The porcupine driver: the results (2026-10-14)

**A linearizable library, traced as etcd's robustness tests trace etcd, passes porcupine's
check** (`run_never_illegal`, `Run.spec`): `Run` runs `clients` goroutines of `ops` operations
each of a library `apply` that is logically atomic (TaDa) against porcupine's model (`applySpec`),
on any inputs `gen` produces (`genSpec`: randomized traffic included), each operation traced with
call and return timestamps of a monotone clock (`clockSpec`) read just before and just after it,
and porcupine (`CheckOperationsVerbose`, as etcd calls it) never answers `Illegal`; with no
timeout it answers `Ok`. Proved down to porcupine's code (`porcupine/Results.lean`).

The clock: `CounterClock` (an atomic counter) is proved to be one, for executions of fewer than
`2^63` steps. `MonotonicClock` (`time.Since`, etcd's) is not: Perennial models the runtime's
nanosecond clock as an arbitrary value per reading, so no monotone spec of it is true in the
model (`notes/STATUS.md`, "Porcupine").

`lintest/counter/Results.lean` instantiates it with a counter under a mutex, end to end.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

/-- See the file header. -/
theorem run_never_illegal : Run.spec (GF := GF) (hG := hG) := wp_Run

end results

end lintest
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.lintest.run_never_illegal
