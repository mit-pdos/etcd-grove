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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
is the read-only one `ownMemoryStorage` holds.

Since 2026-10-14 (reconfiguration stage B8) all four of its `ConfState`'s slices, read-only
(`ownCSL`), which the storage keeps (`ownCSRO` in `memstorageFields`) and `isStorage`'s
`HSnapshot` hands out. Since 2026-10-15 (stage S) *which* `ConfState`: the lists `σ.scs` and the
`AutoLeave` `σ.sal` the storage's state records, the ones `CreateSnapshot`/`ApplySnapshot`
stored, so that raft knows which certified snapshot it forwards (`ownRaftLog`'s `Hsksn`).

raft v3.7 (stage R3, 2026-10-15): `Snapshot()` makes the storage's snapshot whole
(`ms.snapshot = EnsureSnapshot(ms.snapshot)`, a write of the field and of the object's nil
fields, `storage.go:212`; the storage owns both, `memSnapOwn`) and returns a fresh clone
(`proto.Clone`, 213), owned by the caller, whose record's id, conf-state lists and `AutoLeave`
are the storage's. Until the retarget the snapshot came back by value with its `ConfState`
slices the storage's, read-only (`ownCSL`).

D17d (2026-10-18): a conjunction. The first triple is raft's (the owner's, `ownMemoryStorage`,
through `isStorage`); the second the **application's**, with its snapshot token (`memSnapTok`):
the snapshot its token records, as a whole clone (`ownSnapW`: `EnsureSnapshot` sets the metadata
and its conf state, `proto.Clone` keeps them), and no error. etcd's `run` calls it while raft's
goroutine owns the storage.

(D22 S-b′2, 2026-10-20) Raft's triple also hands out the snapshot's certificate from the storage's
registry (`memStorCert`) when it is not empty: the home keeps the current snapshot's
(`memSnapHome`), which is what `isStorage`'s `HSnapshot` passes on (`storCert`). -/
abbrev MemoryStorage.Snapshot.spec : Prop :=
  (∀ (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (esu : GoInterface) (n : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu ∗
      -- (D19i part 1) what the caller knows of the storage's compaction
      (⌜n ≤ 0⌝ ∨ memStorCut γs n) }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ownMemoryStorage ms γs σ ∗
      (⌜err = esu⌝ ∨
       (⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        -- non-empty once compacted (the storage's boundary is at most its snapshot's index); the
        -- view's snapshot or (D19i part 1) a newer one the application took, at or below the
        -- floor, at an entry of the view
        ⌜((σ.prev.index' ≠ W64 0 ∨ 1 ≤ n) → sv.Metadata'.Index' ≠ W64 0) ∧
          ((snapId sv = σ.ss ∧ sv.Metadata'.ConfState'.AutoLeave' = σ.sal ∧
            sv.Metadata'.ConfState'.lists = σ.scs ∧ sv.Data' = σ.sdat) ∨
           (uint.Z σ.ss.index' < uint.Z sv.Metadata'.Index' ∧
            uint.Z σ.prev.index' ≤ uint.Z sv.Metadata'.Index' ∧
            uint.Z sv.Metadata'.Index' ≤ uint.Z σ.fl ∧
            termAt σ.prev σ.ents sv.Metadata'.Index' = some sv.Metadata'.Term'))⌝ ∗
        -- (D22 S-b′2, 2026-10-20) a non-empty one certified in the registry
        (⌜sv.Metadata'.Index' = W64 0⌝ ∨
          memStorCert γs (snapTrip sv sv.Metadata'.ConfState'.lists)))) }}) ∧
  -- (D17d, 2026-10-18) the application's: with its snapshot token
  (∀ (ms : Loc) (γs : MemStorNames) (σ : StorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htok" ∷ memSnapTok ms γs σ }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Snapshot")) (Val #()))
  {{ (snap : Loc), RET (PairV #snap #interface.nil);
      memSnapTok ms γs σ ∗
      ∃ (sv : SnapshotM), ownSnapW snap (DFrac.own 1) sv ∗
        ⌜snapId sv = σ.ss ∧ sv.Metadata'.ConfState'.AutoLeave' = σ.sal ∧
          sv.Metadata'.ConfState'.lists = σ.scs ∧ sv.Data' = σ.sdat⌝ }})

end spec

end EtcdGrove
end Perennial
