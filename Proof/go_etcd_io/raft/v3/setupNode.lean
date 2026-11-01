/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.setupNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `len(peers) == 0` dead (`ps ≠ []`); `NewRawNode` (no error); `Bootstrap` (no error, so no
warning); `newNode`. -/
theorem setupNode.wp_proof
    (wp_NewRawNode : NewRawNode.spec (GF := GF) (hG := hG))
    (wp_RawNode_Bootstrap : RawNode.Bootstrap.spec (GF := GF) (hG := hG))
    (wp_newNode : newNode.spec (GF := GF) (hG := hG)) :
    setupNode.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end EtcdGrove
end Perennial
