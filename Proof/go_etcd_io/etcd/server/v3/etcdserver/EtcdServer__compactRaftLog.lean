/-
The trust boundary: `EtcdServer.compactRaftLog` (names-only: the `MemoryStorage`'s compaction).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__compactRaftLog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Trust boundary** (names-only; restated in D22 S-h, 2026-10-20, with the in-flight skip): the
body (`server.go`) loads `s.inflightSnapshots` (an atomic in its invariant, `srvInflight`) and
returns if it is not `0`; else computes `compacti` from `SnapshotCatchUpEntries` (read-only) and
calls `s.r.raftStorage.Compact(compacti)` (`MemoryStorage.Compact`'s premises as stated), returning
on `ErrCompacted` and logging with the logger's reader slot. What would discharge it: translating
it with its body over `MemoryStorage.Compact`'s spec, `errors.Is` and raft's `ErrCompacted`. -/
axiom EtcdServer.compactRaftLog.wp_proof : EtcdServer.compactRaftLog.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
