/-
`EnsureSnapshotMetadata(m)` (`raftpb/util.go:33`).

Users: `EnsureSnapshot` (this batch). Proof sketch: `EnsureConfState` of its `ConfState` field
(either case), then fresh cells for `nil` `Index`/`Term` (`snapMetaGo` at `full = true`); for a full
metadata nothing is written.
Changes: from `specs-ref/.../raftpb/EnsureSnapshotMetadata.lean`: over `snapMetaGo`.
Margin: none.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Api

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

/-- `EnsureSnapshotMetadata(p)` of `nil` or an owned metadata: a full one holding the same model;
of a full one: `p`, nothing written. -/
def EnsureSnapshotMetadata.spec : Prop :=
  (∀ (p : Loc) (o : Option SnapMeta),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        match o with
        | none => ⌜p = null⌝
        | some sm => snapMetaGo p (DFrac.own 1) sm false }}
      (App (Val (@! go_etcd_io.raft.v3.raftpb.EnsureSnapshotMetadata)) (Val #p))
    {{ (r : Loc), RET #r; snapMetaGo r (DFrac.own 1) (o.getD Snapshot.empty.meta) true ∗
        ⌜o ≠ none → r = p⌝ }}) ∧
  (∀ (p : Loc) (dq : DFrac) (sm : SnapMeta),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ snapMetaGo p dq sm true }}
      (App (Val (@! go_etcd_io.raft.v3.raftpb.EnsureSnapshotMetadata)) (Val #p))
    {{ RET #p; snapMetaGo p dq sm true }})

end spec

end RaftPb
end EtcdGrove
end Perennial
