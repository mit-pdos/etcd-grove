/-
`c.refreshToken(ctx)` (`client/v3/retry_interceptor.go`; unit P3a). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.refreshToken(ctx)` on the retry interceptor's client returns `nil` (no bundle) or
`getToken`'s answer: `nil` or a client error grpc's `status` accepts (`clientErrOk`). -/
abbrev Client.refreshToken.spec : Prop :=
  ∀ (c : Loc) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ ctxOk ctx cd }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"refreshToken")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; clientErrOk err }}

end spec

end EtcdGrove
end Perennial
