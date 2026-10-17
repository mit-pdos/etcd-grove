/-
`v3rpc.clientIPFromContext` (`v3rpc/interceptor.go`; PR etcd#22259). Lean-first (no Rocq
counterpart); the vocabulary is `Proof/go_etcd_io/etcd/server/v3/auth/ClientIP.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota
public import Proof.go_etcd_io.etcd.server.v3.auth.ClientIP

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`clientIPFromContext(ctx)`** (new in PR etcd#22259; what the request-stats log line
reports as `remote`): `auth.ClientIPFromContext(ctx)`, the client IP the context carries, or
`""`. -/
abbrev v3rpc.clientIPFromContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      auth.ctxClientIPIs ctx o }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.clientIPFromContext))
      (Val #(GoInterface.ok ctx)))
  {{ RET #(o.getD go!""); True }}

end spec

end EtcdGrove
end Perennial
