/- Lean-first (no Rocq counterpart).

`(*Storage).Snapshot()` (register.go:70): the `MemoryStorage`'s snapshot, but
`ErrSnapshotTemporarilyUnavailable` for an empty one -- what raft's `Storage` contract asks
(a non-empty snapshot or that error).

raft v3.7 (2026-10-16, stage R6b): the snapshot is a pointer, the fresh clone
`MemoryStorage.Snapshot` returns, owned (`ownSnapM snap 1 sv`, D4); its emptiness is read through
the nil-safe getters (`snap.GetMetadata().GetIndex() == 0`). Stated as `isStorage`'s `HSnapshot`
clause (`InvStorage.lean`) asks of the method, on the storage's owner's view
(`ownMemoryStorage`), which `regStorage_isStorage` (`RegStorageInstance.lean`) turns into the
register's `ownStorage`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- See the file header. -/
abbrev Storage.Snapshot.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (σ : StorState) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
      s.[RStorage, go!"MemoryStorage"] ↦□ ms ∗ ownMemoryStorage ms γs σ ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (s @!! go.GoType.PointerType rStorageTy @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ownMemoryStorage ms γs σ ∗
      (⌜err = esu⌝ ∨
       (⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        ⌜snapId sv = σ.ss ∧ sv.Metadata'.Index' ≠ W64 0 ∧
          sv.Metadata'.ConfState'.AutoLeave' = σ.sal ∧
          sv.Metadata'.ConfState'.lists = σ.scs⌝)) }}

end spec

end register
end EtcdGrove
end Perennial
