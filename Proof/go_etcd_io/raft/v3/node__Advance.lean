/- Lean-first (no Rocq counterpart).

(2026-11-12, trace-check implementation step 1; the design's §3.1, A5) `node.Advance.spec` is the
instance at `ms = []` (`node.Advance.spec_of_traced`, `TracedAdvanceSpec.lean`) of the one proof of
`node.Advance`, the traced triple `node.Advance.tracedSpec_proof` (`NodeAdvanceTraced.lean`, which
holds what was this file's body: the raw triple over raft's internals and its wrapper). -/
module

public import Spec.go_etcd_io.raft.v3.node__Advance
public import Proof.go_etcd_io.raft.v3.NodeAdvanceTraced

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

theorem node.Advance.wp_proof :
    node.Advance.spec (GF := GF) (hG := hG) :=
  node.Advance.spec_of_traced node.Advance.tracedSpec_proof

end proof

end EtcdGrove
end Perennial
