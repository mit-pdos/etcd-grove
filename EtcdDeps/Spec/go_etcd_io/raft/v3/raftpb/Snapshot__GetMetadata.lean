/-
`(*raftpb.Snapshot).GetMetadata()`, of etcd's raft dependency (raft v3.7: protobuf-go v2). Lean-first
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

/-- `GetMetadata()` of a nil `*Snapshot`: nil (the raft wrapper's only case: the node
contract hands out no snapshot). -/
abbrev raftpb.Snapshot.GetMetadata.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (null @!! go.GoType.PointerType raftpb.Snapshot.ty @!! go!"GetMetadata")) (Val #()))
  {{ RET #(null : Loc); True }}

end spec

end EtcdGrove
end Perennial
