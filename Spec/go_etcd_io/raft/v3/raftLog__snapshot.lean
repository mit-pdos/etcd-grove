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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
package-level variable -- or a `nil` error and a fresh, owned snapshot, non-empty
(`IsEmptySnap`'s test, so `maybeSendSnapshot`'s `panic` is dead), from one of two sources:

- a pending snapshot (`LogState.snap`), cloned: one the node may send (`ksn`), the log's base,
  at or below `committed`;
- (U8 v2, candidate 17 rev 3) the storage's (`Storage.Snapshot()`): at or past the log's
  boundary, and valid (`svCert`, the contract's `snapshotValid` as raft carries it). Until U8 v2
  this branch also related the snapshot to raft's log (commit bound and term, through the
  storage's state raft owned, `StoredSnapOk`) and to the certificate registry (`storCert`); the
  storage's snapshot is now the client's, and what it is comes from its validity.

The premise: the log is compacted (its boundary non-zero), or the storage is (`storPast`), so a
storage snapshot is non-empty. The log comes back at the same state. -/
abbrev raftLog.snapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (esu : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "#Hesu" ∷ globalAddr ErrSnapshotTemporarilyUnavailable ↦□ esu ∗
      "#Hcompact" ∷ (⌜uint.Z ls.prev.index' ≠ 0⌝ ∨ storPast ls.storage 1) }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"snapshot")) (Val #()))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ownRaftLog l ls ∗
      (⌜err = esu⌝ ∨
       (⌜err = interface.nil⌝ ∗ ∃ (sv : SnapshotM), ownSnapM snap (DFrac.own 1) sv ∗
        ⌜sv.Metadata'.Index' ≠ W64 0⌝ ∗
        (⌜ls.snap ≠ none ∧ snapTrip sv sv.Metadata'.ConfState'.lists ∈ ls.ksn ∧
            uint.Z sv.Metadata'.Index' ≤ uint.Z ls.committed ∧
            plogTermAt ls.prev (ls.sents ++ ls.uents) sv.Metadata'.Index'
              = some sv.Metadata'.Term'⌝ ∨
         (⌜ls.snap = none ∧ uint.Z ls.prev.index' ≤ uint.Z sv.Metadata'.Index'⌝ ∗
           svCert ls.sn sv)))) }}

end spec

end EtcdGrove
end Perennial
