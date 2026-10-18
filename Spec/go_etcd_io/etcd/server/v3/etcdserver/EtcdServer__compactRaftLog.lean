/-
`s.compactRaftLog(snapi)` (`server.go`): the trust boundary (names-only). Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.compactRaftLog(snapi)` (the contract of a names-only callee: it compacts the
`MemoryStorage`'s log below `snapi`, keeping `SnapshotCatchUpEntries`, unless a snapshot is in
flight) returns, with the logger's reader slot given back.

(D19i part 1, 2026-10-18; until then false: the contract owned nothing of the `MemoryStorage`)
The compaction is `MemoryStorage.Compact(compacti)`, `compacti` at most `snapi` (`snapi -
SnapshotCatchUpEntries`, or `1`), under the application's snapshot token (`memSnapTok`) with its
snapshot at or past `snapi` (`snapshot` took it) and its boundary at most `snapi`, and the
storage's floor at least `snapi` (raised by raft at the `Advance` that `raftAdvancedC` reports):
`Compact.spec`'s premises; `ErrCompacted` (already compacted) is returned on. `1 ≤ snapi`: the
snapshot trigger fires only past index `0`. The boundary stays at most `snapi`. (It also reads
`s.inflightSnapshots`, an atomic `sendMergedSnap` adds to, and `s.Cfg.SnapshotCatchUpEntries`,
never written after the server's construction.) -/
abbrev EtcdServer.compactRaftLog.spec : Prop :=
  ∀ (s : Loc) (snapi : w64) (ms : Loc) (γs : MemStorNames) (σ : StorState),
  uint.Z σ.prev.index' ≤ uint.Z snapi → uint.Z snapi ≤ uint.Z σ.ss.index' → 1 ≤ uint.Z snapi →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvLgReader s ∗
      rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ memSnapTok ms γs σ ∗
      memFloorAtLeast ms γs (uint.Z snapi) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"compactRaftLog")) (Val #snapi))
  {{ RET #(); srvLgReader s ∗ ∃ σ' : StorState, memSnapTok ms γs σ' ∗
      ⌜uint.Z σ'.prev.index' ≤ uint.Z snapi ∧ σ'.ss = σ.ss⌝ }}

end spec

end EtcdGrove
end Perennial
