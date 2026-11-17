/- Lean-first (no Rocq counterpart).

(2026-11-12, trace-check step 5) **The untraced instance of the one proof**: `StartNode.gatedSpec_proof`
(`TracedStartNode.lean`, where this file's proof moved and was generalized to both modes) proves the
Draft's `StartNode.gatedSpec`; `StartNode.spec` is its instance (`StartNode.spec_of_gatedSpec`). -/
module

public import Proof.go_etcd_io.raft.v3.TracedStartNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem StartNode.wp_proof
    (wp_setupNode : setupNode.spec (GF := GF) (hG := hG))
    (wp_node_run : node.run.spec (GF := GF) (hG := hG)) :
    StartNode.spec (GF := GF) (hG := hG) :=
  StartNode.spec_of_gatedSpec (StartNode.gatedSpec_proof wp_setupNode wp_node_run)

end proof

end EtcdGrove
end Perennial
