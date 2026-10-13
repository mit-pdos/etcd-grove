/- Lean-first (no Rocq counterpart).

`(*Storage).Snapshot()` (register.go:69): the `MemoryStorage`'s snapshot, but
`ErrSnapshotTemporarilyUnavailable` for an empty one -- what raft's `Storage` contract asks
(a non-empty snapshot or that error).
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
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ s.[RStorage, go!"MemoryStorage"] ↦□ ms ∗ ownMemoryStorage ms γs σ ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (s @!! go.GoType.PointerType rStorageTy @!! go!"Snapshot")) (Val #()))
  {{ (snap : raftpb.Snapshot) (err : GoInterface), RET (PairV #snap #err);
      ownMemoryStorage ms γs σ ∗
      (⌜err = esu⌝ ∨
       (⌜err = interface.nil ∧ snapId snap = σ.ss ∧ snap.Metadata'.Index' ≠ W64 0⌝ ∗
        ∃ (voters : List w64), snap.Metadata'.ConfState'.Voters' ↦*□ voters)) }}

end spec

end register
end EtcdGrove
end Perennial
