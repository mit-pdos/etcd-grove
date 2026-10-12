/-
`(*raftpb.SnapshotMetadata).GetIndex()`, of etcd's raft dependency (raft v3.7: protobuf-go v2). Lean-first
(no Rocq counterpart); see `InvRaftMsg.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `GetIndex()` of a nil `*SnapshotMetadata`: 0 (`raft.IsEmptySnap` of a nil snapshot). -/
abbrev raftpb.SnapshotMetadata.GetIndex.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (null @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetIndex")) (Val #()))
  {{ RET #(W64 0); True }}

end spec

end EtcdGrove
end Perennial
