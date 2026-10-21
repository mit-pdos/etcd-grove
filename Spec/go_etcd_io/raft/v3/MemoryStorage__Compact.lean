/- `MemoryStorage.Compact` (`storage.go:254`), specified 2026-10-12 (Lean-first: no Rocq
counterpart). -/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.Compact(ci)`: unless `ci` is at or below the compaction boundary
(`ErrCompacted`, nothing changed), the entries up to `ci` are dropped: the boundary is
`ci` at its term, the stored entries those after it (`memStorCompacted`). The snapshot
is not touched (`ss` unchanged; `memStorMeta`, which the application keeps, is not taken, so
it still holds the stored snapshot, `ConfState` included).

It changes what raft reads, so it takes the owner's `ownMemoryStorage` with nothing
pending (no `Ready`'s entries being appended); not `memStorMeta`. The premises, for a
`ci` above the boundary:

- `ci ≤ lastIndex`: above it `Compact` calls `Panicf`. Its documentation asks for
  `ci ≤ raftLog.applied`, which implies it only for a storage that holds what raft
  applied;
- the entry at `ci` has the index `ci`: the new boundary's index is read from that
  entry ("ents[i] has raft log position i+snapshot.Metadata.Index", `storage.go`), a
  fact of a storage raft appends to that `StorState` does not record.

The error variable's value is passed in, as `Snapshot`'s spec does for its error.

**The application's (D19i part 1, 2026-10-18).** etcd's apply loop calls it while raft owns the
storage, so it no longer takes `ownMemoryStorage`: the application's token (the storage's boundary
`σt.prev` and snapshot) and the floor's witness (`memFloorTok ms γs x`: raft's published floor at
least `x`, the storage holding entries up to it). Premise, for a `ci` above the boundary: `ci`
within the floor and at or below the storage's snapshot (a compacted storage keeps a snapshot
covering its boundary). The entry at `ci` is numbered `ci`: the storage keeps its entries numbered
by their positions (`HistOk`), which raft's batches are (`PendOk`). (2026-10-19, D21 M3) And within
the storage's cap (`MemStorNames.cap`), which no compaction passes. -/
abbrev MemoryStorage.Compact.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σt : StorState) (x ci : w64) (ecomp : GoInterface),
  (uint.Z σt.prev.index' < uint.Z ci →
    uint.Z ci ≤ uint.Z x ∧ uint.Z ci ≤ uint.Z σt.ss.index' ∧
    -- (2026-10-19, D21 M3) and within the storage's cap
    uint.Z ci ≤ γs.cap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htok" ∷ memSnapTok ms γs σt ∗
      "#Hfw" ∷ memFloorTok ms γs x ∗
      "#Herr" ∷ globalAddr ErrCompacted ↦□ ecomp }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Compact")) (Val #ci))
  {{ (err : GoInterface), RET #err;
      (⌜uint.Z ci ≤ uint.Z σt.prev.index' ∧ err = ecomp⌝ ∗ memSnapTok ms γs σt) ∨
      (∃ (t : w64), ⌜uint.Z σt.prev.index' < uint.Z ci ∧ err = interface.nil⌝ ∗
        memSnapTok ms γs { σt with prev := entryID.mk t ci }) }}

end spec

end EtcdGrove
end Perennial
