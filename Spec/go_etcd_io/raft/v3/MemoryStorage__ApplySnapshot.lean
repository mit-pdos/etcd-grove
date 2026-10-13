/- `MemoryStorage.ApplySnapshot` (`storage.go:207`), specified 2026-10-12 (Lean-first: no
Rocq counterpart). -/
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

/-- `ms.ApplySnapshot(snap')`: unless the storage's snapshot is non-empty and at least
as recent (`ss.index ≠ 0 ∧ snap'.Index ≤ ss.index`: `ErrSnapOutOfDate`, nothing
changed), the storage is the snapshot: the boundary is its id, nothing stored after it
(`memStorApplied`), and it is the snapshot `memStorMeta` holds and `Snapshot()`
returns.

It changes what raft reads, so it takes the owner's `ownMemoryStorage` with nothing
pending (no `Ready`'s entries being appended), and `memStorMeta`. The premises: the
snapshot's index is below `2^61` (`ownMemoryStorage`'s bound; a client assumption, as
`Append`'s), and its `ConfState.Voters` slice is read-only, for good (as
`memstorageFields` holds it). The error variable's value is passed in, as `Snapshot`'s
spec does for its error. -/
abbrev MemoryStorage.ApplySnapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState) (hs : raftpb.HardState)
    (snap snap' : raftpb.Snapshot) (voters : List w64) (eood : GoInterface),
  σ.pend = [] →
  uint.Z snap'.Metadata'.Index' < 2^61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "Hmeta" ∷ memStorMeta ms γs hs snap ∗
      "#Hvoters" ∷ snap'.Metadata'.ConfState'.Voters' ↦*□ voters ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot"))
      (Val #snap'))
  {{ (err : GoInterface), RET #err;
      (⌜σ.ss.index' ≠ W64 0 ∧ uint.Z snap'.Metadata'.Index' ≤ uint.Z σ.ss.index' ∧
          err = eood⌝ ∗
        ownMemoryStorage ms γs σ ∗ memStorMeta ms γs hs snap) ∨
      (⌜¬ (σ.ss.index' ≠ W64 0 ∧ uint.Z snap'.Metadata'.Index' ≤ uint.Z σ.ss.index') ∧
          err = interface.nil⌝ ∗
        ownMemoryStorage ms γs (memStorApplied snap') ∗ memStorMeta ms γs hs snap') }}

end spec

end EtcdGrove
end Perennial
