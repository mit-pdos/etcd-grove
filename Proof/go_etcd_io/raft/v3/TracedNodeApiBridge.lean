/-
Lean-first (no Rocq counterpart). Trace-check's S7 (part 2) (2026-11-11; `notes/decisions.md`, "S7
(part 2)"): the client API's traced statements (`TracedNodeApi.lean`) from the frozen Draft's
(`TracedApiDraft.lean`). Internal (not importable): the final assembly (a linking file) imports it.

`startTraceC` is the Draft's `startTrace` (`startTraceC_eq`) and `startDone` its `startDoneB`
(`startDone_eq`, amendment A8.3), so `StartNode.gatedSpec` gives `StartNode.tracedSpec`
(`StartNode.tracedSpec_of_gated`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedNodeApi
public import Proof.go_etcd_io.raft.v3.TracedApiDraft
import all Proof.go_etcd_io.raft.v3.TracedNodeApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The client's precondition is the Draft's. -/
theorem startTraceC_eq (γ : Cluster) (N : Namespace) (vs : List w64) (cv : Config) :
    startTraceC (GF := GF) γ N vs cv = startTrace γ N vs cv := by
  unfold startTraceC startTrace Cluster.traceSim TracedConfigOk traceFits
  rfl

/-- The client's completion witness is the Draft's (amendment A8.3). -/
theorem startDone_eq (γ : Cluster) (id : w64) : startDone (GF := GF) γ id = startDoneB γ id := by
  unfold startDone startDoneB bootDoneG
  rfl

/-- **`StartNode.tracedSpec` from the Draft's `StartNode.gatedSpec`.** -/
theorem StartNode.tracedSpec_of_gated (h : StartNode.gatedSpec (GF := GF)) :
    StartNode.tracedSpec (GF := GF) := by
  intro γ N vs ctxs c cv lok si csm Q F peers dq pv h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16
  rw [startTraceC_eq, startDone_eq]
  exact h γ N vs ctxs c cv lok si csm Q F peers dq pv h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16

end spec

end EtcdGrove
end Perennial
