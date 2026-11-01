/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__compactRaftLog.lean`. Lean-first
(no Rocq counterpart); the trust boundary (names-only) until 2026-10-26.

The body (`server.go`): `s.inflightSnapshots.Load()` (its invariant, `srvInflight`), returning
after an `Info` if it is not `0`; `compacti` from `SnapshotCatchUpEntries`;
`s.r.raftStorage.Compact(compacti)` (`MemoryStorage.Compact`'s premises: `compacti ≤ snapi`, at
most the floor and the snapshot, within the cap). `Compact` returns `nil` or raft's
`ErrCompacted`; of the latter `errors.Is(err, raft.ErrCompacted)` is `true` (an `errors.New`
error, `ErrCompactedNew`: a leaf pointer error, `ErrorStringLeaf`), so the `Panic` is dead.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__compactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.go_etcd_io.raft.v3.MemstorageApi
public import Spec.errors.Is
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Uint64
public import Perennial.Spec.sync.atomic.Int64__Load

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.compactRaftLog.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hCompact : MemoryStorage.Compact.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    EtcdServer.compactRaftLog.spec (GF := GF) (hG := hG) := by
  sorry -- durability stage I (I-5): broken by the MemoryStorage statement changes (mode o, memStorFresh c sv)

end proof

end EtcdGrove
end Perennial
