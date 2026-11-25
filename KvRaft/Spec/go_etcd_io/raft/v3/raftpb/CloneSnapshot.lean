-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/CloneSnapshot.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.CloneSnapshot` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Stated as the `proto` trust-boundary spec it replaces.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvPbSnapSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `CloneSnapshot(s)` (`raftpb/noax.go`, the fork's branch raft37-goose-lean-noax,
`notes/raft-noax.md`): what `proto.Clone` of a `*pb.Snapshot` was stated to do
(`Spec/google_golang_org/protobuf/proto/CloneSnapshot.lean`, whose five conjuncts these are, for the
hand-written Go function that replaces the call): of a snapshot holding `s` (at any fraction), a
fresh snapshot holding `s`, owned, a deep copy; of a nil one, nil; whole (`ownSnapW`), every pointer
field set (`ownSnapS`) and the metadata's fields set (`ownSnapV`) are kept. -/
abbrev raftpb.CloneSnapshot.spec : Prop :=
  (∀ (p : Loc) (dq : DFrac) (s : SnapshotM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapM p dq s }}
      (App (Val #(functions raftpb.CloneSnapshot [])) (Val #p))
    {{ (p' : Loc), RET #p'; ownSnapM p dq s ∗ ownSnapM p' (DFrac.own 1) s }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val #(functions raftpb.CloneSnapshot [])) (Val #(null : Loc)))
  {{ RET #(null : Loc); True }} ∧
  (∀ (p : Loc) (dq : DFrac) (s : SnapshotM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapW p dq s }}
      (App (Val #(functions raftpb.CloneSnapshot [])) (Val #p))
    {{ (p' : Loc), RET #p'; ownSnapW p dq s ∗ ownSnapW p' (DFrac.own 1) s }}) ∧
  (∀ (p : Loc) (dq : DFrac) (s : SnapshotM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapS p dq s }}
      (App (Val #(functions raftpb.CloneSnapshot [])) (Val #p))
    {{ (p' : Loc), RET #p'; ownSnapS p dq s ∗ ownSnapS p' (DFrac.own 1) s }}) ∧
  (∀ (p : Loc) (dq : DFrac) (s : SnapshotM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownSnapV p dq s }}
      (App (Val #(functions raftpb.CloneSnapshot [])) (Val #p))
    {{ (p' : Loc), RET #p'; ownSnapV p dq s ∗ ownSnapV p' (DFrac.own 1) s }})

end spec

end EtcdGrove
end Perennial
