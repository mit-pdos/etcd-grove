/- Port of election_proof/spec_raftLog__snapshot.v (feb5c73d4).

Lean notes: Rocq's `(#snap, #err)` is `PairV #snap #err`; `global_addr` is
`globalAddr`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

The log comes back at the same state, like `raftLog.firstIndex`: the one caller,
`raft.maybeSendSnapshot`, calls both on the same log. -/
abbrev raftLog.snapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "#Hesu" ∷ globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"snapshot")) (Val #()))
  {{ (snap : raftpb.Snapshot) (err : GoInterface), RET (PairV #snap #err);
      ownRaftLog l ls ∗
      (⌜err = esu⌝ ∨
       (⌜err = interface.nil ∧
          snap.Metadata'.Index' ≠ W64 0 ∧
          uint.Z snap.Metadata'.Index' ≤ uint.Z ls.committed ∧
          plogTermAt ls.prev (ls.sents ++ ls.uents) snap.Metadata'.Index'
            = some snap.Metadata'.Term'⌝ ∗
        ∃ (voters : List w64), snap.Metadata'.ConfState'.Voters' ↦*□ voters)) }}

end spec

end EtcdGrove
end Perennial
