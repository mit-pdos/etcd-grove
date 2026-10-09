/-
`(*raftpb.ConfChange).GetId()`, of etcd's raft dependency (raft v3.7: protobuf-go v2).
Lean-first (no Rocq counterpart); see `InvRaftpb.lean`.
-/
import EtcdGrove.Server.InvRaftpb

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

/-- `cc.GetId()`: the change's `Id` (0 if absent). -/
abbrev raftpb.ConfChange.GetId.spec : Prop :=
  ∀ (cc : Loc) (v : raftpb.ConfChange) (dq : DFrac) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ cc ↦{dq} v ∗
      optU64 v.Id' id }}
    (App (Val (cc @!! go.GoType.PointerType raftpb.ConfChange.ty @!! go!"GetId")) (Val #()))
  {{ RET #id; cc ↦{dq} v }}

end spec

end EtcdGrove
end Perennial
