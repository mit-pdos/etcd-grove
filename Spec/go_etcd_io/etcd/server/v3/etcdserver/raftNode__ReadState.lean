/-
`(*raftNode).ReadState()` (raft.go): the channel `readStateC`.
Lean-first (no Rocq counterpart); see `InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.ReadState()` returns `readStateC`, a channel of read states each answering the
registrations of its request id (`isRNReadStateC E`, the read loop's `isReadStateC E.RQ`; 2026-10-13,
the request path's unit 4b). -/
abbrev raftNode.ReadState.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r }}
    (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"ReadState")) (Val #()))
  {{ (c : Loc), RET #c; isRNReadStateC E c }}

end spec

end EtcdGrove
end Perennial
