/-
**`raftNode_of_StartNode`, as a hypothesis** (the import tiers, 2026-11-18): `NodeStartLinked.lean`'s
statement as `raftNode_of_StartNode.law : Prop`, which `NewServer`'s proof takes instead of importing
`NodeStartLinked`; `raftNode_of_StartNode_law_holds` proves it, and the `Link`s pass it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeStart

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section laws1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `raftNode_of_StartNode`'s statement (`NodeStartLinked.lean`, a linking module), as a hypothesis
of the proofs that use it (the import tiers); `raftNode_of_StartNode_law_holds` proves it. -/
abbrev raftNode_of_StartNode.law : Prop :=
  ∀ (wp_bnr : bootstrappedRaft.newRaftNode.spec (GF := GF) (hG := hG))
      (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
      (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
      (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
      (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
      (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
      (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
      (wp_Ready : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Ready.spec (GF := GF) (hG := hG))
      (wp_Advance : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Advance.spec (GF := GF) (hG := hG))
      (wp_Tick : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Tick.spec (GF := GF) (hG := hG))
      (wp_Stop : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Stop.spec (GF := GF) (hG := hG))
      (wp_ReadIndex : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.ReadIndex.spec (GF := GF) (hG := hG))
      (wp_Step : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Step.spec (GF := GF) (hG := hG))
      (wp_ReportUnreachable : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.ReportUnreachable.spec (GF := GF) (hG := hG))
      (wp_ReportSnapshot : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.ReportSnapshot.spec (GF := GF) (hG := hG))
      (wp_Propose : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.Propose.spec (GF := GF) (hG := hG))
      (wp_ApplyConfChange : ∀ γr : SrvRaft, letI := srvStor (GF := GF) γr; node.ApplyConfChange.spec (GF := GF) (hG := hG)),
    NodeStartSpec (GF := GF)

end laws1

end EtcdGrove
end Perennial
