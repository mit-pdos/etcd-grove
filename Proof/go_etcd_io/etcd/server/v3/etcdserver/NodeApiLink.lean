/-
**The node API's results at the server's storage model** (2026-10-27, the server port): the node
API's specs (`NodeApiDraft.lean`) are stated over any raft storage model (`[StorageModel GF]`);
the server states its node premises at the cluster's, `srvStor γr` (the `MemoryStorage` registry
of its `SrvRaft`), for every `γr` it allocates. These are the node API's linked results at it, the
terms `Link.lean` passes (`=` callees of `etc/link-lean-first-server.txt`); and raft's
`MemoryStorage.Snapshot` result (stated over any storage model, which it does not use) at one. A
linking module, as `Link.lean` (it imports raft's `Link.lean`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.go_etcd_io.raft.v3.Link

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
    Draft.StartNode.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.wp_StartNode

theorem srvApi_wp_StartNode_dyn : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.StartNode.dynamicSpec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.wp_StartNode_dynamic

theorem srvApi_wp_Ready : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.Ready.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_Ready

theorem srvApi_wp_Advance : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.Advance.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_Advance

theorem srvApi_wp_Advance_dyn : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.Advance.dynamicSpec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_Advance_dynamic

theorem srvApi_wp_Tick : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.Tick.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_Tick

theorem srvApi_wp_ReadIndex : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.ReadIndex.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_ReadIndex

theorem srvApi_wp_Propose : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.Propose.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_Propose

theorem srvApi_wp_ApplyConfChange : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.ApplyConfChange.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_ApplyConfChange

theorem srvApi_wp_ApplyConfChange_dyn : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.ApplyConfChange.dynamicSpec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_ApplyConfChange_dynamic

theorem srvApi_wp_Step : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.Step.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_Step

theorem srvApi_wp_ReportUnreachable : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.ReportUnreachable.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_ReportUnreachable

theorem srvApi_wp_ReportSnapshot : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr;
    Draft.node.ReportSnapshot.spec (GF := GF) (hG := hG) := fun γr => by
  letI := srvStor (GF := GF) γr; exact Draft.node.wp_ReportSnapshot

/-- `MemoryStorage.Snapshot`'s application triple (raft's linked result, whose `[StorageModel GF]`
its statement does not use), at the server's any-storage model. -/
theorem srvApi_wp_MemSnapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) := by
  letI := srvAnyStor (GF := GF); exact MemoryStorage.wp_Snapshot

end links

end EtcdGrove
end Perennial
