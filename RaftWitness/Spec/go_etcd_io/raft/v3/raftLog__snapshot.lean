/- Port of election_proof/spec_raftLog__snapshot.v (feb5c73d4).

Lean notes: Rocq's `(#snap, #err)` is `PairV #snap #err`; `global_addr` is
`globalAddr`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `l.snapshot()` -- the snapshot the log can offer a lagging peer
(`raftLog.snapshot.impl`, `Code/go_etcd_io/raft/v3.lean`):

    if l.unstable.snapshot != nil { return *l.unstable.snapshot, nil }
    return l.storage.Snapshot()

Either the distinguished `ErrSnapshotTemporarilyUnavailable` -- whose points-to the
caller passes in, since the comparison in `maybeSendSnapshot` is against the
package-level variable, not against a claim about `errors.New` -- or a `nil` error and a
snapshot whose metadata `(Term, Index)` is

- non-zero (`IsEmptySnap`'s test, so `maybeSendSnapshot`'s `panic` is dead),
- at or below `committed`, and an entry id of the log: the log has `Term` at `Index`
  (`plogTermAt`, possibly as its base) -- since 2026-10-03, for `SnapOk`
  (`Protocol/Model.lean`),

with its `ConfState.Voters` slice read-only, for good (since 2026-10-03, so that the
`MsgSnap` built from it is abstracted from the heap, `msgAbs`).

Two sources. A pending snapshot (`LogState.snap`) is returned by value from
`*l.unstable.snapshot`: it *is* the log's base (`LogStoreOk`), at or below `committed`
by `ownRaftLog`; its voters are `ownSnap`'s. Otherwise `Storage.Snapshot()`:
`isStorage`'s `HSnapshot` says the snapshot is the storage's own, `ss`, and
`ownRaftLog`'s `StoredSnapOk` relates `ss` to the log and the commit index.

(2026-10-15, stage S) The snapshot, with its lists, is one the node may send (`ksn`): the
storage's is (`ownRaftLog`'s `Hsksn`, the lists those `HSnapshot` returns), and so is the pending
one (`Hpksn`).

The log comes back at the same state, like `raftLog.firstIndex`: the one caller,
`raft.maybeSendSnapshot`, calls both on the same log.

raft v3.7 (stage R3, 2026-10-15): both sources return a **fresh clone**, owned by the caller
(`proto.Clone(l.unstable.snapshot)`, `log.go:295`; the storage's `Snapshot()` clones too), where
until the retarget the snapshot came by value with its `ConfState` slices read-only (`ownCSL`).
The lists are the record's. -/
abbrev raftLog.snapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "#Hesu" ∷ globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu ∗
      -- (2026-10-16, stage R8a, D11) the log is compacted: `Storage.Snapshot` promises a
      -- non-empty snapshot only then (`HSnapshot`); with a pending snapshot `LogStoreOk` gives it
      -- anyway. (D19i part 1, 2026-10-18) Or the storage is, by the application (`storPast`).
      "#Hcompact" ∷ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ownRaftLog l ls ∗
      (⌜err = esu⌝ ∨
       (⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        ⌜sv.Metadata'.Index' ≠ W64 0 ∧
          uint.Z sv.Metadata'.Index' ≤ uint.Z ls.committed ∧
          plogTermAt ls.prev (ls.sents ++ ls.uents) sv.Metadata'.Index'
            = some sv.Metadata'.Term' ∧
          -- (2026-10-15, stage S) one the node may send; (D19i part 1) or one the application
          -- took, at or below the floor (its certificate is the application's: A3, `SnapObl`)
          (snapTrip sv sv.Metadata'.ConfState'.lists ∈ ls.ksn ∨
           uint.Z sv.Metadata'.Index' ≤ uint.Z ls.fl)⌝)) }}

end spec

end EtcdGrove
end Perennial
