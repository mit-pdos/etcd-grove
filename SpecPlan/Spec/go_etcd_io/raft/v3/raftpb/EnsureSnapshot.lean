/-
`EnsureSnapshot(s)` (`raftpb/util.go:57`).

Users: raft's `NewMemoryStorage` (`nil`), `MemoryStorage.Snapshot`/`ApplySnapshot`/`CreateSnapshot`
(`storage.go:212`, `222`, `255`: the stored snapshot, full; a client's argument, owned or full), `raft.
handleSnapshot` (`raft.go:1859`: a received message's snapshot, full and shared read-only). Snippet:
`examples/specreq/raftpb/snapshot.go` (`ReqEnsure`).

Proof sketch: `nil`: `new(Snapshot)`. Otherwise `snapshotRaw_unfold`/`snapshotPts_unfold`;
`EnsureSnapshotMetadata(s.Metadata)` (its spec, either case); store the result if the field was
`nil`. Full: nothing written (`EnsureSnapshotMetadata`'s second case).

Changes: from `specs-ref/.../raftpb/EnsureSnapshot.lean`: the old `snapOpt`/`ownSnapS` cases over
`snapshotRaw`/`snapshotPts` (the old `ownSnapE`/`W`/`S` hierarchy collapses to "any presence" and
"full").
Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `EnsureSnapshot(p)` of `nil` or an owned snapshot (any presence): a full one holding the same
model (the empty one for `nil`), `p` itself when it was not `nil`; of a full one (any fraction):
`p`, nothing written. -/
def EnsureSnapshot.spec : Prop :=
  (∀ (p : Loc) (o : Option Snapshot),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        match o with
        | none => ⌜p = null⌝
        | some s => snapshotRaw p (DFrac.own 1) s }}
      (App (Val (@! go_etcd_io.raft.v3.raftpb.EnsureSnapshot)) (Val #p))
    {{ (r : Loc), RET #r; snapshotPts r (DFrac.own 1) (o.getD Snapshot.empty) ∗
        ⌜o ≠ none → r = p⌝ }}) ∧
  (∀ (p : Loc) (dq : DFrac) (s : Snapshot),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ snapshotPts p dq s }}
      (App (Val (@! go_etcd_io.raft.v3.raftpb.EnsureSnapshot)) (Val #p))
    {{ RET #p; snapshotPts p dq s }})

end spec

end RaftPb
end EtcdGrove
end Perennial
