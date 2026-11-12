/-
Lean-first (no Rocq counterpart). **The receipts' fit at a traced node** (2026-11-12, trace-check's
receipt bounds; `notes/decisions.md`, "Trace-check's receipt bounds as instances"). Raft-internal (not
on `etc/api/raft.txt`).

`RawNode.acceptReady.spec`'s traced premise said `receiptBound GF + γ.reBoot.length ≤ traceNumBound`,
the bound arithmetic `notes/bounds-plan.md` keeps out of specs. It is named here, raft's receipt fit
(as the node API's `readyFits`, at `RaftNames`): the proofs that read the log's numbers off raft's
ghost state (`ownRaftGhost_traceBoundIf`) unfold it; the specs say only `traceReadyFits GF γ`.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Ghost
public import Proof.go_etcd_io.raft.v3.Protocol.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris

section fits
variable [GooseExts]

/-- **The receipts fit the trace's bound past the bootstrap log** (raft's receipt fit at a traced
cluster): every index raft hands out is below `receiptBound GF + γ.reBoot.length` (a time receipt
per entry past the bootstrap log), so below the trace's `traceNumBound`. The node API's `readyFits`
at the cluster's `RaftNames` (`Cluster.bootLen` is `γ.raft.reBoot.length`). -/
def traceReadyFits (GF : BundledGFunctors) [ReceiptGS GF] (γ : RaftNames) : Prop :=
  receiptBound GF + γ.reBoot.length ≤ traceNumBound

/-- The fit, unfolded (for the proofs that read the log's numbers off it). -/
theorem traceReadyFits.le {GF : BundledGFunctors} [ReceiptGS GF] {γ : RaftNames}
    (h : traceReadyFits GF γ) : receiptBound GF + γ.reBoot.length ≤ traceNumBound := h

/-- The fit, from the bound. -/
theorem traceReadyFits.intro {GF : BundledGFunctors} [ReceiptGS GF] {γ : RaftNames}
    (h : receiptBound GF + γ.reBoot.length ≤ traceNumBound) : traceReadyFits GF γ := h

end fits

end EtcdGrove
end Perennial
