/- `MemoryStorage.InitialState` (`storage.go:121`; U8 v2 step 3): without the lock, the snapshot
read from the allocation's fuel (`memStorFresh`), the hard state and the counter from
`memStorMeta`. -/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState
public import Proof.go_etcd_io.raft.v3.LemmasConfState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.InitialState.wp_proof
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetConfState : raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG))
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG)) :
    MemoryStorage.InitialState.spec (GF := GF) (hG := hG) := by
  sorry -- durability stage I (I-5): statement changed (mode o / detached memStorFresh c sv)

end proof

end EtcdGrove
end Perennial
