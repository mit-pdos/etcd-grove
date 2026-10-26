/-
`s.compactRaftLog(snapi)` (`server.go`). Lean-first (no Rocq counterpart); the request path's
unit 4b (2026-10-13); the trust boundary (names-only) until 2026-10-26, now translated and proved.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

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

/-- `s.compactRaftLog(snapi)` (it compacts the
`MemoryStorage`'s log below `snapi`, keeping `SnapshotCatchUpEntries`, unless a snapshot is in
flight) returns, with the logger's reader slot given back.

(D19i part 1, 2026-10-18; until then false: the contract owned nothing of the `MemoryStorage`)
The compaction is `MemoryStorage.Compact(compacti)`, `compacti` at most `snapi` (`snapi -
SnapshotCatchUpEntries`, or `1`), under the application's snapshot token (`memSnapTok`) with its
snapshot at or past `snapi` (`snapshot` took it) and its boundary at most `snapi`, and the
storage's floor at least `snapi` (raised by raft at the `Advance` that `raftAdvancedC` reports):
`Compact.spec`'s premises; `ErrCompacted` (already compacted) is returned on. `1 ≤ snapi`: the
snapshot trigger fires only past index `0`. The boundary stays at most `snapi`. (It also reads
`s.Cfg.SnapshotCatchUpEntries`, never written after the server's construction.)

(D22 S-h, 2026-10-20) **The in-flight skip**: it first reads `s.inflightSnapshots` (`Load`, an
atomic `sendMergedSnap` adds to and its release goroutine subtracts from: `srvInflight`, its
invariant, until then not in the contract although the body reads it) and returns at once,
compacting nothing, while it is not `0` (a merged snapshot is being sent, or was within
`releaseDelayAfterSnapshot`: the entries after it stay for the follower). The postcondition
covers both outcomes (the storage's boundary unchanged, or raised to at most `snapi`).

(2026-10-19, D21 M3) `SnapshotCatchUpEntries` is `scu` (read-only), and the compaction index is at
most the storage's cap (`MemStorNames.cap`, `Compact.spec`'s premise since D21 M3): `compacti` as
the body computes it, `snapi - scu` past `scu`, else `1`.
(2026-10-26, its body translated) The logger's cell `s.lg` (`l`, not `nil`), which `Logger` reads. -/
abbrev EtcdServer.compactRaftLog.spec : Prop :=
  ∀ (s : Loc) (snapi : w64) (ms : Loc) (γs : MemStorNames) (σ : StorState) (scu : w64) (l : Loc),
  uint.Z σ.prev.index' ≤ uint.Z snapi → uint.Z snapi ≤ uint.Z σ.ss.index' → 1 ≤ uint.Z snapi →
  (if uint.Z scu < uint.Z snapi then uint.Z snapi - uint.Z scu else 1) ≤ γs.cap →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ srvLgReader s ∗
      srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗
      srvInflight s ∗
      rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ memSnapTok ms γs σ ∗
      memFloorAtLeast ms γs (uint.Z snapi) ∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"compactRaftLog")) (Val #snapi))
  {{ RET #(); srvLgReader s ∗ ∃ σ' : StorState, memSnapTok ms γs σ' ∗
      ⌜uint.Z σ'.prev.index' ≤ uint.Z snapi ∧ σ'.ss = σ.ss⌝ }}

end spec

end EtcdGrove
end Perennial
