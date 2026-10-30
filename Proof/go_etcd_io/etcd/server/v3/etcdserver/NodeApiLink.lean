/-
**The node API's results at the server's storage model** (2026-10-27, the server port): the node
API's specs (`Spec/go_etcd_io/raft/v3/`) are stated over any raft storage model (`[StorageModel GF]`);
the server states its node premises at the cluster's, `srvStor γr` (the `MemoryStorage` registry
of its `SrvRaft`), for every `γr` it allocates. These are the node API's linked results at it, the
terms `Link.lean` passes (`=` callees of `etc/link-lean-first-server.txt`); and raft's
`MemoryStorage.Snapshot` result (stated over any storage model, which it does not use) at one. A
linking module, as `Link.lean` (it imports raft's `Link.lean`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.go_etcd_io.raft.v3.Link
public import Proof.go_etcd_io.raft.v3.Linked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem srvApi_wp_StartNode : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    StartNode.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact wp_StartNode

/-- (2026-10-30, the repair) raft's `node.Stop` (its whole running token to `nodeStopped`), the
`Stop` clause of `isRaftNodeIfc` (until then the premise `rnStopOk`). -/
theorem srvApi_wp_Stop : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.Stop.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_Stop

theorem srvApi_wp_Ready : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.Ready.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_Ready

theorem srvApi_wp_Advance : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.Advance.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_Advance

theorem srvApi_wp_Tick : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.Tick.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_Tick

theorem srvApi_wp_ReadIndex : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.ReadIndex.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_ReadIndex

theorem srvApi_wp_Propose : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.Propose.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_Propose

theorem srvApi_wp_ApplyConfChange : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.ApplyConfChange.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_ApplyConfChange

theorem srvApi_wp_Step : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.Step.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_Step

theorem srvApi_wp_ReportUnreachable : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.ReportUnreachable.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_ReportUnreachable

theorem srvApi_wp_ReportSnapshot : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    node.ReportSnapshot.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact node.wp_ReportSnapshot

/-- `MemoryStorage.Snapshot`'s application triple (raft's linked result, whose `[StorageModel GF]`
its statement does not use), at the server's any-storage model. -/
theorem srvApi_wp_MemSnapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) := by
  letI := srvAnyStor (GF := GF); exact MemoryStorage.wp_Snapshot

end links

end EtcdGrove
end Perennial
