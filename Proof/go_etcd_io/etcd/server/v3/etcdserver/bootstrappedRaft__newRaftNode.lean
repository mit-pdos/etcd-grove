/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedRaft__newRaftNode.lean`.
Lean-first (no Rocq counterpart). Its callees with specs: raft's node API's `StartNode`
(`StartNode.spec` in a static cluster, `StartNode.dynamicSpec` in a dynamic one; at the
cluster's storage model, `srvStor`) and `newRaftNode`; Perennial's `sync.Mutex.Lock`/`Unlock` are
its linked results, used directly; the rest are the contracts the spec takes
(`InvNodeStart.lean`). (2026-10-27: over the node API; until then raft's `StartNode.spec`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedRaft__newRaftNode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newRaftNode
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedRaft.newRaftNode.wp_proof
    (wp_StartNode : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
      StartNode.spec (GF := GF) (hG := hG))
    (wp_newRaftNode : _root_.Perennial.EtcdGrove.newRaftNode.spec (GF := GF) (hG := hG)) :
    bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

end EtcdGrove
end Perennial
