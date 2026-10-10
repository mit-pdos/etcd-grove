/-
Port of election_proof/spec_MemoryStorage__Snapshot.v (feb5c73d4).

Lean notes:
* `ownMemoryStorage` (`InvMemstorage.lean`) needs ghost state, so the section has the
  extra variable `[AllG GF]` (porting guide, "Section variables"); in Rocq it comes
  with `heapGS Σ`.
* `global_addr raft.ErrSnapshotTemporarilyUnavailable` is
  `globalAddr ErrSnapshotTemporarilyUnavailable`; `snap_id` is `snapId`;
  `(#snap, #err)` is `PairV #snap #err`.
-/
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
variable [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.Snapshot()` (`storage.go:244`): returns `ms.snapshot` by value, and `nil`.
Stated exactly as `isStorage`'s `HSnapshot` asks of the method, including the premise
about `ErrSnapshotTemporarilyUnavailable` and the error *disjunction* --
`MemoryStorage` only ever takes the second disjunct (`nil`, the stored snapshot). The
snapshot's metadata is the storage's `ss` (`snapId`) -- until 2026-10-10 also
non-empty, because `ownMemoryStorage` said `ss.index <> 0`; a new `MemoryStorage` has
no snapshot and returns an empty one, which `isStorage` excludes, so the instance
(`MemstorageInstance.lean`) adds the premise instead -- and its `ConfState.Voters` slice
is the read-only one `ownMemoryStorage` holds. -/
abbrev MemoryStorage.Snapshot.spec : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Snapshot")) (Val #()))
  {{ (snap : raftpb.Snapshot) (err : GoInterface), RET (PairV #snap #err);
      ownMemoryStorage ms γs σ ∗
      (⌜err = esu⌝ ∨
       (⌜err = interface.nil ∧ snapId snap = σ.ss⌝ ∗
        ∃ (voters : List w64), snap.Metadata'.ConfState'.Voters' ↦*□ voters)) }}

end spec

end EtcdGrove
end Perennial
