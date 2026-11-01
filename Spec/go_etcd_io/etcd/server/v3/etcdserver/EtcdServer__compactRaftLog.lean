/-
`s.compactRaftLog(snapi)` (`server.go`). Lean-first (no Rocq counterpart); the request path's
unit 4b (2026-10-13); the trust boundary (names-only) until 2026-10-26, now translated and proved.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.raft.v3.MemstorageApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (2026-10-30, the repair) **The compaction index** `compactRaftLog` computes from `snapi` and
`SnapshotCatchUpEntries` `scu`: `snapi - scu` past `scu`, else `1`. -/
def compactIdx (snapi scu : w64) : Nat :=
  if uint.Z scu < uint.Z snapi then uint.nat snapi - uint.nat scu else 1

/-- `s.compactRaftLog(snapi)` (it compacts the `MemoryStorage`'s log below `snapi`, keeping
`SnapshotCatchUpEntries`, unless a snapshot is in flight) returns, with the logger's reader slot
given back, and the storage compacted to the compaction index (`compactIdx`) or not at all (a
snapshot in flight).

(2026-10-30, the repair: raft's two-writer `MemoryStorage` specs, R1) The compaction is
`MemoryStorage.Compact(compacti)`, over `Compact.spec`'s premises at the server's justifications
(`memStorInv`, `memStorJ`): the storage's stored snapshot past `snapi` (`memSnapLb`, which
`snapshot`'s `CreateSnapshot` gave), its entry at the compaction index frozen or already compacted,
and the node's applied index past `snapi` (`nodeAppliedLb`, `J.B`'s: the `raftAdvancedC` close
reports it). `ErrCompacted` is returned on. `1 ≤ snapi`: the snapshot trigger fires only past index
`0`. (Until the repair: the application's shared snapshot token, D22 J4, and the storage's floor
and cap.)

(D22 S-h, 2026-10-20) **The in-flight skip**: it first reads `s.inflightSnapshots` (`srvInflight`)
and returns at once, compacting nothing, while it is not `0`. (2026-10-19, D21 M3)
`SnapshotCatchUpEntries` is `scu` (read-only). (2026-10-26, its body translated) The logger's cell
`s.lg` (`l`, not `nil`). -/
abbrev EtcdServer.compactRaftLog.spec : Prop :=
  ∀ (s : Loc) (snapi : w64) (ms : Loc) (γs : MemStorNames) (γr : SrvRaft) (id : w64)
    (scu : w64) (l : Loc),
  1 ≤ uint.Z snapi →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvLgReader s ∗
      srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗
      srvInflight s ∗
      rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗
      (letI : MemStorReg GF := ⟨γr.reg⟩
       iprop(memStorInv ms γs γr.cl id ∗ nodeAppliedLb γr.cl id (uint.nat snapi))) ∗
      memSnapLb γs (uint.nat snapi) ∗
      ((∃ e, memLog γs (compactIdx snapi scu) DFrac.discard [e]) ∨
        memCompacted γs (compactIdx snapi scu)) ∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"compactRaftLog")) (Val #snapi))
  {{ RET #(); srvLgReader s }}

end spec

end EtcdGrove
end Perennial
