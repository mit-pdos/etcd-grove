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
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Proof.go_etcd_io.raft.v3.ConfchangeApi
public import Spec.go_etcd_io.raft.v3.node__ForgetLeader
public import Spec.go_etcd_io.raft.v3.node__Campaign
public import Spec.go_etcd_io.raft.v3.node__Status
public import Spec.go_etcd_io.raft.v3.node__Stop
public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Spec.go_etcd_io.raft.v3.node__TransferLeadership
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
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

theorem wp_RestartNode [StorageModel GF] :
    RestartNode.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.wp_RestartNode

/-! (2026-10-29, U9) One spec per function: `RestartNode`, `node.Advance` and
`node.ApplyConfChange` over the one cluster (`isCluster`), linked in `Link.lean` like every other
function (until U9 the static family there, and the dynamic and unified variants here); `StartNode`
has no spec until the server's repair (U10). -/

theorem node.wp_Advance [StorageModel GF] :
    node.Advance.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Advance

theorem node.wp_ApplyConfChange [StorageModel GF] :
    node.ApplyConfChange.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_ApplyConfChange

/-! (2026-10-29, stage U9a) Stopping a node, and `ForgetLeader` over the node API. -/

theorem node.wp_Stop [StorageModel GF] :
    node.Stop.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Stop

theorem node.wp_ForgetLeader [StorageModel GF] :
    node.ForgetLeader.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_ForgetLeader

/-! (2026-10-29, stage U7) `Campaign` and `Status` over the node API. -/

theorem node.wp_Status [StorageModel GF] :
    node.Status.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Status

theorem node.wp_Campaign [StorageModel GF] :
    node.Campaign.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Campaign

/-! (raft-final, 2026-10-29) The other node methods. -/

theorem node.wp_Propose [StorageModel GF] :
    node.Propose.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Propose

theorem node.wp_Step [StorageModel GF] :
    node.Step.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Step

theorem node.wp_ProposeConfChange [StorageModel GF] :
    node.ProposeConfChange.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_ProposeConfChange

theorem node.wp_ReadIndex [StorageModel GF] :
    node.ReadIndex.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_ReadIndex

theorem node.wp_Ready [StorageModel GF] :
    node.Ready.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Ready

theorem node.wp_ReportSnapshot [StorageModel GF] :
    node.ReportSnapshot.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_ReportSnapshot

theorem node.wp_ReportUnreachable [StorageModel GF] :
    node.ReportUnreachable.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_ReportUnreachable

theorem node.wp_Tick [StorageModel GF] :
    node.Tick.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_Tick

theorem node.wp_TransferLeadership [StorageModel GF] :
    node.TransferLeadership.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.node.wp_TransferLeadership

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

/-! (raft-final, 2026-10-29) The rest of `MemoryStorage` a client wrapping it calls (kvreconf). -/

theorem MemoryStorage.wp_InitialState :
    MemoryStorage.InitialState.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_InitialState

theorem MemoryStorage.wp_CreateSnapshot :
    MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_CreateSnapshot

theorem MemoryStorage.wp_ApplySnapshot :
    MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_ApplySnapshot

theorem MemoryStorage.wp_Compact :
    MemoryStorage.Compact.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Compact

theorem MemoryStorage.wp_Snapshot :
    MemoryStorage.Snapshot.spec (GF := GF) (hG := hG) :=
  _root_.Perennial.EtcdGrove.MemoryStorage.wp_Snapshot

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
