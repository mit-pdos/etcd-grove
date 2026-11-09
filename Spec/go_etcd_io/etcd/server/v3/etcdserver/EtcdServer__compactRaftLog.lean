/-
`(*EtcdServer).compactRaftLog(snapi)` (`server.go:2162-2194`): unless a merged snapshot is in flight,
compact the `MemoryStorage` up to `snapi - SnapshotCatchUpEntries` (at least `1`).

**Users**: `snapshotIfNeededAndCompactRaftLog` (`server.go:1248`). Snippet `snapshot.go`
(`ReqSnapshotCompact`).

**Proof sketch**. `inflightSnapshots.Load()` (an atomic, any value); `compacti ≤ snapi`;
`raftStorage.Compact(compacti)` (R1's `MemoryStorage.Compact.spec` through `stor_compact`, with
`appliedLb n compacti` from `nodeAdvanced r snapi` and `storSnapLb n compacti` from `nodeSnapLb r
snapi`, `appliedLb_mono`/`storSnapLb_mono`): `ErrCompacted` returns (already compacted further);
compacting past the last index is excluded by the update's precondition (raft's invariant: the
applied index is in the log), so `lg.Panic` is unreachable. This is the fork's fix of
`issues/etcd-compact-past-raft-applied.md`: `applyAll` waits for `raftAdvancedC` first.

**Changes** from `specs-ref`'s spec (the storage's key `nk`, `memStorInv`, `nodeAppliedLb`): over
`nodeAdvanced`/`nodeSnapLb`; no apply-thread token needed. **Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Compact the raft log below a snapshot** at an index raft has applied. -/
def EtcdServer.compactRaftLog.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : Nat) (snapi : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvNode s γ id ∗
      nodeAdvanced (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s)
        (uint.nat snapi) ∗
      nodeSnapLb (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s)
        (uint.nat snapi) }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"compactRaftLog")) (Val #snapi))
  {{ RET #(); True }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
