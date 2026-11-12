/-
Lean-first (no Rocq counterpart). Trace-check step 5 (2026-11-12): `RunTracedOk`, the pure facts
`node.run.spec` (`Spec/go_etcd_io/raft/v3/node__run.lean`) takes of a traced node, out of the spec
file (the layout: a spec file exposes only its `<F>.spec`). Raft-internal.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.TraceFits

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

variable [GooseExts]

/-- **What the gated `node.run` needs of a traced node** beyond `runPre` (pure; `StartNode`'s traced
proof discharges it): the node is dynamic (`confcP`'s static arm, `CCShrink`, has no traced callee: every
node of the node API is dynamic, `StartNode`'s `HdynOk`), the receipts fit the trace's bound past the
bootstrap log (`traceReadyFits`: the cluster's `readyFits` at its `RaftNames`, for the traced triples'
premise and `ownStepGhost_traceBound`), and the term ceiling's successor is below the trace's bound
(`traceCeilFits`, `receiptBound GF + 2 ≤ traceNumBound`: the ceiling `rs.tc` is at most `receiptBound GF` by `termLB` and
`budgetInv`, so `rs.tc + 1 < traceNumBound`, the traced triples' `Htcb`). The harness has the last two
from `tcRunFits` (`receiptBound GF + 3 ≤ 2^61`, three voters' bootstrap entries). -/
def RunTracedOk (GF : BundledGFunctors) [ReceiptGS GF] (γ : NodeNames) : Prop :=
  γ.mode.isDyn = true ∧ traceReadyFits GF γ.raft ∧ traceCeilFits GF

end EtcdGrove
end Perennial
