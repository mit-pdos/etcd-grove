/-
**Raft's traced node API, linked** (2026-11-12, trace-check implementation step 1; the design's §3.1):
`Linked.lean`'s counterpart for the traced statements of `TracedNodeApi.lean`, re-exported under
`RaftLink` from `Link.lean`'s proofs (imported non-publicly, as `Linked` does). Apart from `Linked`
because `TracedNodeApi`'s `trTok` would clash with etcd's rafthttp `trTok` in the server, which imports
`Linked`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedNodeApi
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__Advance
import Proof.go_etcd_io.raft.v3.Link
import Proof.go_etcd_io.raft.v3.TracedStartNode
import Proof.go_etcd_io.raft.v3.TracedNodeApiBridge

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftLink

open Iris Iris.BI go_etcd_io.raft.v3

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`node.Advance`'s one proof, traced** (`node.Advance.tracedSpec`): `node.Advance.spec` is its
instance (`node.Advance.spec_of_traced`). -/
theorem node.wp_Advance_traced [StorageModel GF] :
    node.Advance.tracedSpec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.Advance.tracedSpec_proof

/-- `node.Step` with the message's token (`node.Step.tracedSpec`): `stepIn_intro`, then
`node.Step.spec`. -/
theorem node.wp_Step_traced [StorageModel GF] :
    node.Step.tracedSpec (GF := GF) (hG := hG) :=
  node.Step.tracedSpec_of_spec _root_.Perennial.EtcdGrove.node.wp_Step

/-- **`StartNode` of a traced cluster** (2026-11-12, trace-check step 5): the one proof
(`StartNode.gatedSpec_proof`, from the linked `setupNode` and `node.run`), at the client's
statement (`StartNode.tracedSpec_of_gated`). What the tracecheck harness took as its hypothesis
`HarnessOpen`. -/
theorem wp_StartNode_traced [StorageModel GF] :
    StartNode.tracedSpec (GF := GF) :=
  StartNode.tracedSpec_of_gated
    (_root_.Perennial.EtcdGrove.StartNode.gatedSpec_proof _root_.Perennial.EtcdGrove.wp_setupNode
      _root_.Perennial.EtcdGrove.node.wp_run)

end links

end RaftLink
end EtcdGrove
end Perennial
