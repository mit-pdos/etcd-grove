/-
Lean-first (no Rocq counterpart).

# Porcupine: the results (2026-10-14)

**Porcupine is complete**: on a history that is linearizable for the model (`Linearizable`,
porcupine's definition: closed intervals, an operation precedes another iff it returns strictly
before the other is called), its entry points never answer `Illegal`, and with no timeout they
answer `Ok` (`CheckOperations` answers `true`). The model is any `porcupine.Model` with a
specification `S` (`isModel`: no `Partition`, `Init`/`Step` or `StepContext` stepping as `S.M`
does, an `Equal` true only on equal states, any `Hash`) -- the shape of etcd's robustness model;
the history any slice of `Operation`s with `call ≤ return` and fewer than `2^60` operations
(`HistOk`).

The whole checker is verified, from the Go code (`third_party/porcupine`, upstream v1.3.1 with one
translatable rewrite, `UPSTREAM.md`): the sorted entries (`makeEntries` over Perennial's proved
`sort.Sort`), the search (`checkSingle`: the linked list with `lift`/`unlift`, the bitset, the
memoization cache, the context checks; its correctness argument is `Theory.lean`), the partitions'
goroutines with their channel, the timeout and the cancellation (`checkParallel`), and the
defaults (`fillDefault`). Only completeness is claimed (`Ok` is not shown to imply
linearizability), which is what "porcupine never fails a linearizable trace" needs.
-/
module

public import Proof.github_com.anishathalye.porcupine.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- `CheckOperationsVerbose`, what etcd's robustness tests call: never `Illegal` on a
linearizable history; `Ok` with no timeout. -/
theorem checkOperationsVerbose_complete :
    CheckOperationsVerbose.spec (GF := GF) (hG := hG) := wp_CheckOperationsVerbose

/-- `CheckOperationsTimeout`: never `Illegal` on a linearizable history; `Ok` with no timeout. -/
theorem checkOperationsTimeout_complete :
    CheckOperationsTimeout.spec (GF := GF) (hG := hG) := wp_CheckOperationsTimeout

/-- `CheckOperations`: `true` on a linearizable history. -/
theorem checkOperations_complete :
    CheckOperations.spec (GF := GF) (hG := hG) := wp_CheckOperations

end results

end porcupine
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.porcupine.checkOperationsVerbose_complete
#print axioms Perennial.EtcdGrove.porcupine.checkOperationsTimeout_complete
#print axioms Perennial.EtcdGrove.porcupine.checkOperations_complete
