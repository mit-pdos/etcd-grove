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
is not touched.

It changes what raft reads, so it takes the owner's `ownMemoryStorage` with nothing
pending (no `Ready`'s entries being appended); not `memStorMeta`. The premises, for a
`ci` above the boundary:

- `ci ≤ lastIndex`: above it `Compact` calls `Panicf`. Its documentation asks for
  `ci ≤ raftLog.applied`, which implies it only for a storage that holds what raft
  applied;
- the entry at `ci` has the index `ci`: the new boundary's index is read from that
  entry ("ents[i] has raft log position i+snapshot.Metadata.Index", `storage.go`), a
  fact of a storage raft appends to that `StorState` does not record.

The error variable's value is passed in, as `Snapshot`'s spec does for its error. -/
abbrev MemoryStorage.Compact.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (ci : w64) (ecomp : GoInterface),
  σ.pend = [] →
  (uint.Z σ.prev.index' < uint.Z ci →
    uint.Z ci ≤ uint.Z σ.prev.index' + (σ.ents.length : Int) ∧
    ∀ e, σ.ents[(uint.Z ci - uint.Z σ.prev.index' - 1).toNat]? = some e → e.Index' = ci) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "#Herr" ∷ globalAddr ErrCompacted ↦□ ecomp }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Compact")) (Val #ci))
  {{ (err : GoInterface), RET #err;
      (⌜uint.Z ci ≤ uint.Z σ.prev.index' ∧ err = ecomp⌝ ∗ ownMemoryStorage ms γs σ) ∨
      (∃ (t : w64), ⌜uint.Z σ.prev.index' < uint.Z ci ∧ termAt σ.prev σ.ents ci = some t ∧
          err = interface.nil⌝ ∗
        ownMemoryStorage ms γs (memStorCompacted σ ci t)) }}

end spec

end EtcdGrove
end Perennial
