/-
## `(*raftLog).snapshot()` (internal)

**Users**: `maybeSendSnapshot` (`raft.go:672`): on `ErrSnapshotTemporarilyUnavailable` it gives up,
on another error it panics; it panics on an empty snapshot, after a term or entries lookup answered
`ErrCompacted`. Snippet `raftlog/reads.go` (`ReqSnapshotForSend`).

**Proof sketch**: a pending snapshot: `proto.Clone` of it (its validity was `restore`'s premise).
Else `Storage.Snapshot` through `isStorage`, its update fired inside the log's invariant, where the
stored snapshot is valid (`V`) or empty, and at least every `logCompactedLb` (the compaction point
was at least it when it was issued, the stored snapshot is at least the compaction point, and only
grows); a pending snapshot is at least every `logCompactedLb` too (it is past `committed`, which is
past the storage's floor).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__snapshot.lean`: validity through the client's `V` (was the log's
ghost list of sendable snapshots `ksn` with certificates); `logCompactedLb` replaces the old
derivation of non-emptiness from the frozen prefix.

**Margin**: the stored snapshot may be newer than any `logCompactedLb`.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) The snapshot to send: the pending one, or the storage's (valid, or empty); at least every index found compacted. -/
def raftLog.snapshot.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (S : StorState → IProp GF) (V : Snapshot → IProp GF) (N : Namespace),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗ logStorage l S V N }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"snapshot")) (Val #()))
  {{ (sp : Loc) (err : GoInterface), RET (PairV #sp #err); raftLog l ls ∗
      ((⌜err = interface.nil⌝ ∗ ∃ s, snapshotPts sp (DFrac.own 1) s ∗ (⌜s.isEmpty⌝ ∨ V s) ∗
          ⌜∀ s', ls.us.snap = some s' → s = s'⌝ ∗
          (∀ j, logCompactedLb l j -∗ ⌜j ≤ uint.nat s.index⌝)) ∨
       (errIs go_etcd_io.raft.v3.ErrSnapshotTemporarilyUnavailable err ∗ ⌜ls.us.snap = none⌝)) }}

end spec
end Raft
end EtcdGrove
end Perennial
