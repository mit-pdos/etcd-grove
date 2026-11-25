-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/CloneConfState.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.CloneConfState` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Stated as the `proto` trust-boundary spec it replaces.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `CloneConfState(cs)` (`raftpb/noax.go`, the fork's branch raft37-goose-lean-noax,
`notes/raft-noax.md`): what `proto.Clone` of a `*pb.ConfState` was stated to do
(`Spec/google_golang_org/protobuf/proto/CloneConfState.lean`): of a conf state holding `c` (at any
fraction), a fresh conf state holding `c`, owned; of a nil one, nil. -/
abbrev raftpb.CloneConfState.spec : Prop :=
  (∀ (p : Loc) (dq : DFrac) (c : ConfStateM),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownCSM p dq c }}
      (App (Val #(functions raftpb.CloneConfState [])) (Val #p))
    {{ (p' : Loc), RET #p'; ownCSM p dq c ∗ ownCSM p' (DFrac.own 1) c }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val #(functions raftpb.CloneConfState [])) (Val #(null : Loc)))
  {{ RET #(null : Loc); True }}

end spec

end EtcdGrove
end Perennial
