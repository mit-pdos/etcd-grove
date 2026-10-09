/-
`(*raftpb.Entry).GetTerm()`, of etcd's raft dependency (raft v3.7: protobuf-go v2). Lean-first
(no Rocq counterpart); see `InvRaftpb.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb

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

/-- `e.GetTerm()`: the entry's `Term` (0 if absent). -/
abbrev raftpb.Entry.GetTerm.spec : Prop :=
  ∀ (e : Loc) (m : EntryModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ entryAt e m }}
    (App (Val (e @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"GetTerm")) (Val #()))
  {{ RET #m.term; True }}

end spec

end EtcdGrove
end Perennial
