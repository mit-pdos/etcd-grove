/-
`(*raftpb.SnapshotMetadata).GetTerm()`, of etcd's raft dependency (raft v3.7: protobuf-go v2). Lean-first
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

/-- `GetTerm()` of a `*SnapshotMetadata` whose `Term` field holds `t` (`optU64`; the server's
`run`, 2026-10-13), or of a nil one: `t`, 0. -/
abbrev raftpb.SnapshotMetadata.GetTerm.spec : Prop :=
  ∀ (md : Loc) (t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      (⌜md = null ∧ t = W64 0⌝ ∨
        ∃ pt : Loc, ⌜md ≠ null⌝ ∗ structFieldRef raftpb.SnapshotMetadata go!"Term" md ↦□ pt ∗ optU64 pt t) }}
    (App (Val (md @!! go.GoType.PointerType raftpb.SnapshotMetadata.ty @!! go!"GetTerm")) (Val #()))
  {{ RET #t; True }}

end spec

end EtcdGrove
end Perennial
