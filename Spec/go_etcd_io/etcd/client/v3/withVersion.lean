/-
`withVersion(ctx)` (`client/v3/ctx.go`, names only; unit P3a): the context with the client's API
version in its outgoing gRPC metadata (`metadata.FromOutgoingContext`, `Pairs`, `MD.Copy`,
`MD.Set`, `NewOutgoingContext`: grpc's `metadata`, names only).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `withVersion(ctx)` returns a context derived from `ctx` by a value (grpc's
`NewOutgoingContext` is `context.WithValue`): the same `Done` and `Err` (`isContext` with `ctx`'s
descriptor, its values changed). -/
abbrev withVersion.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ context.isContext ctx cd }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withVersion)) (Val #(GoInterface.ok ctx)))
  {{ (c' : GoInterface), RET #c'; ∃ (ci : GoInterfaceOk) (vs : GMap GoInterface GoInterface),
      ⌜c' = GoInterface.ok ci⌝ ∗ context.isContext ci { cd with Values := vs } }}

end spec

end EtcdGrove
end Perennial
