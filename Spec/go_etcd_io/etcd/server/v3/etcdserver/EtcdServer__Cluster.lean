/-
`s.Cluster()` (`server.go`): `s.cluster` as an `api.Cluster`.
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.Cluster()` returns `s.cluster` (read-only), an `*membership.RaftCluster`, as an
`api.Cluster`. -/
abbrev EtcdServer.Cluster.spec : Prop :=
  ∀ (s cl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvClusterAddr s ↦□ cl }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cluster")) (Val #()))
  {{ RET #(interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty)
      #cl : GoInterface); True }}

end spec

end EtcdGrove
end Perennial
