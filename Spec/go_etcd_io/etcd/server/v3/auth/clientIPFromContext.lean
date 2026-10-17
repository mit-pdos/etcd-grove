/-
`auth.clientIPFromContext` (`server/auth/store.go`; PR etcd#22259). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/auth/ClientIP.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.ClientIP
public import Proof.go_etcd_io.etcd.server.v3.auth.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`clientIPFromContext(ctx)`** (new in PR etcd#22259; the unexported alias the store's log lines call): `ClientIPFromContext(ctx)`. -/
abbrev auth.clientIPFromContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.ctxClientIPIs ctx o }}
    (App (Val (@! go_etcd_io.etcd.server.v3.auth.clientIPFromContext)) (Val #(GoInterface.ok ctx)))
  {{ RET #(o.getD go!""); True }}

end spec

end EtcdGrove
end Perennial
