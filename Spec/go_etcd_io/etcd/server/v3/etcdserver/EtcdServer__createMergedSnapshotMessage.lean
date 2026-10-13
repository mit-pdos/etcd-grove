/-
`s.createMergedSnapshotMessage(m, t, i, cs)` (`snapshot_merge.go`): the trust boundary
(names-only). Lean-first (no Rocq counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.createMergedSnapshotMessage(m, t, i, cs)` (the contract of a names-only callee: it
snapshots the backend and raft's store into a message for a follower) returns some message. -/
abbrev EtcdServer.createMergedSnapshotMessage.spec : Prop :=
  ∀ (s m : Loc) (t i : w64) (cs : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"createMergedSnapshotMessage")) (Val #m)) (Val #t)) (Val #i)) (Val #cs))
  {{ (merged : Loc), RET #merged; True }}

end spec

end EtcdGrove
end Perennial
