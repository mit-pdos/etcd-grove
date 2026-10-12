/-
`(*raftpb.Message).GetTo()`, of etcd's raft dependency (raft v3.7: protobuf-go v2). Lean-first
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

/-- `m.GetTo()`: the message's `To` (0 if absent). -/
abbrev raftpb.Message.GetTo.spec : Prop :=
  ∀ (m : Loc) (to : w64) (ty : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ msgAt m to ty }}
    (App (Val (m @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetTo")) (Val #()))
  {{ RET #to; True }}

end spec

end EtcdGrove
end Perennial
