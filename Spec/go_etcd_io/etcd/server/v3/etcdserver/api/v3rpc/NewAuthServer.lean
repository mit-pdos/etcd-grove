/-
`v3rpc.NewAuthServer` (`v3rpc/auth.go`; item 4, the server start). Lean-first (no Rocq counterpart); the
vocabulary is `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvGrpcStart.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthServer

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewAuthServer(s)`** returns a new `*AuthServer` over the server as its authenticator
(`authServerIs`; the auth plan's A3, the API layer, 2026-10-24: `True` until then). -/
abbrev v3rpc.NewAuthServer.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc }}
    (App (Val (@! v3rpc.NewAuthServer)) (Val #s))
  {{ (p : Loc), RET #p; v3rpc.authServerIs p s }}

end spec

end EtcdGrove
end Perennial
