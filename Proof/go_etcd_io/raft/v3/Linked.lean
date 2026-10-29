/-
**Raft's linked results, without raft's proofs** (2026-10-26, raft's signature, stage 1;
`notes/decisions.md`, "Package signatures"): the results of `Link.lean` that proofs outside raft's
linking files use as lemmas, re-exported under `RaftLink` (`open RaftLink` gives them their
names). This module imports `Link.lean` non-publicly: a client sees each result's statement (its
public spec), not the proofs, so it does not reach raft's internals (`etc/api-check.py
etc/api/raft.txt`). A client's own `Link.lean`, `Results.lean` or `Adequacy.lean` may import
raft's `Link.lean` itself.
-/
module

public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.StartNode
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Proof.go_etcd_io.raft.v3.ConfchangeApi
import Proof.go_etcd_io.raft.v3.Link
import Proof.go_etcd_io.raft.v3.ConfchangeApiProof

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftLink

open Iris Iris.BI go_etcd_io.raft.v3

section linksLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem wp_StartNode [StorageModel GF] :
    StartNode.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_StartNode

theorem wp_RestartNode [StorageModel GF] :
    RestartNode.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_RestartNode

/-! The dynamic variants (2026-10-28: the known exception to one spec per function, until a cluster
takes both snapshots and reconfiguration; `etc/gen-link.py` links only a function's `wp_proof`, so
they are linked here, from the same callees). -/

theorem wp_StartNode_dynamic [StorageModel GF] :
    StartNode.dynamicSpec (GF := GF) (hG := hG) :=
  StartNode.wp_proof_dynamic _root_.Perennial.EtcdGrove.wp_setupNode
    _root_.Perennial.EtcdGrove.node.wp_run

theorem node.wp_Advance_dynamic [StorageModel GF] :
    node.Advance.dynamicSpec (GF := GF) (hG := hG) :=
  node.Advance.wp_proof_dynamic

theorem node.wp_ApplyConfChange_dynamic [StorageModel GF] :
    node.ApplyConfChange.dynamicSpec (GF := GF) (hG := hG) :=
  node.ApplyConfChange.wp_proof_dynamic _root_.Perennial.EtcdGrove.raftpb.ConfChange.wp_AsV2
    _root_.Perennial.EtcdGrove.raftpb.ConfChangeV2.wp_AsV2

/-! The variants over a cluster with snapshots and reconfiguration (2026-10-28, stage U4a:
`isCluster`, `InvNodeRule.lean`; the same exception, linked here from the same callees). -/

theorem wp_RestartNode_unified [StorageModel GF] :
    RestartNode.unifiedSpec (GF := GF) (hG := hG) :=
  RestartNode.wp_proof_unified _root_.Perennial.EtcdGrove.wp_NewRawNode
    _root_.Perennial.EtcdGrove.wp_newNode _root_.Perennial.EtcdGrove.node.wp_run

theorem node.wp_Advance_unified [StorageModel GF] :
    node.Advance.unifiedSpec (GF := GF) (hG := hG) :=
  node.Advance.wp_proof_unified

theorem node.wp_ApplyConfChange_unified [StorageModel GF] :
    node.ApplyConfChange.unifiedSpec (GF := GF) (hG := hG) :=
  node.ApplyConfChange.wp_proof_unified _root_.Perennial.EtcdGrove.raftpb.ConfChange.wp_AsV2
    _root_.Perennial.EtcdGrove.raftpb.ConfChangeV2.wp_AsV2

end linksLC

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem wp_NewMemoryStorage [StorageModel GF] :
    NewMemoryStorage.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_NewMemoryStorage

/-- (2026-10-28, stage U4a) `CreateSnapshot` at a term the caller knows: the known exception to one
spec per function, linked here from the same callees. -/
theorem MemoryStorage.wp_CreateSnapshot_unified [StorageModel GF] :
    MemoryStorage.CreateSnapshot.unifiedSpec (GF := GF) (hG := hG) :=
  MemoryStorage.CreateSnapshot.wp_proof_unified _root_.Perennial.EtcdGrove.raftpb.Snapshot.wp_GetMetadata
    _root_.Perennial.EtcdGrove.raftpb.SnapshotMetadata.wp_GetIndex
    _root_.Perennial.EtcdGrove.raftpb.Entry.wp_GetIndex _root_.Perennial.EtcdGrove.MemoryStorage.wp_lastIndex
    _root_.Perennial.EtcdGrove.raftpb.wp_EnsureSnapshot _root_.Perennial.EtcdGrove.raftpb.Entry.wp_GetTerm
    _root_.Perennial.EtcdGrove.proto.wp_CloneConfState _root_.Perennial.EtcdGrove.proto.wp_CloneSnapshot

theorem wp_IsEmptyHardState  :
    IsEmptyHardState.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_IsEmptyHardState

theorem wp_IsEmptySnap  :
    IsEmptySnap.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_IsEmptySnap

theorem MemoryStorage.wp_Append [StorageModel GF] :
    MemoryStorage.Append.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Append

/-- (2026-10-29, U8, J5) For a client that persists a `Ready`'s hard state (kvreconf). -/
theorem MemoryStorage.wp_SetHardState [StorageModel GF] :
    MemoryStorage.SetHardState.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_SetHardState

theorem MemoryStorage.wp_Entries [AllG GF] [StorageModel GF] :
    MemoryStorage.Entries.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Entries

theorem MemoryStorage.wp_FirstIndex [AllG GF] [StorageModel GF] :
    MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_FirstIndex

theorem MemoryStorage.wp_LastIndex [AllG GF] [StorageModel GF] :
    MemoryStorage.LastIndex.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_LastIndex

theorem MemoryStorage.wp_Term [AllG GF] [StorageModel GF] :
    MemoryStorage.Term.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Term

/-! `confchange` and `tracker` for clients (2026-10-29, stage U11, `ConfchangeApi.lean`): the
importable specs, from the internal ones (`ConfchangeApiProof.lean`) and `Link.lean`'s results. -/

theorem tracker.wp_MakeProgressTracker_api :
    tracker.MakeProgressTracker.apiSpec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.tracker.MakeProgressTracker.apiSpec_of
    _root_.Perennial.EtcdGrove.tracker.wp_MakeProgressTracker

theorem confchange.wp_Restore_api :
    confchange.Restore.apiSpec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.confchange.Restore.apiSpec_of
    _root_.Perennial.EtcdGrove.confchange.wp_Restore

theorem confchange.Changer.wp_Simple_api :
    confchange.Changer.Simple.apiSpec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.confchange.Changer.Simple.apiSpec_of
    _root_.Perennial.EtcdGrove.confchange.Changer.wp_Simple

theorem confchange.Changer.wp_EnterJoint_api :
    confchange.Changer.EnterJoint.apiSpec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.confchange.Changer.EnterJoint.apiSpec_of
    _root_.Perennial.EtcdGrove.confchange.Changer.wp_EnterJoint

theorem confchange.Changer.wp_LeaveJoint_api :
    confchange.Changer.LeaveJoint.apiSpec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.confchange.Changer.LeaveJoint.apiSpec_of
    _root_.Perennial.EtcdGrove.confchange.Changer.wp_LeaveJoint

end links

end RaftLink
end EtcdGrove
end Perennial
